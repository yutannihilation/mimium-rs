use std::path::PathBuf;

use crate::ast::*;
use crate::interner::{ExprNodeId, Symbol, ToSymbol, TypeNodeId};
use crate::pattern::{Pattern, TypedId, TypedPattern};
use crate::types::{PType, Type};
use crate::utils::error::ReportableError;
use crate::utils::metadata::*;
use chumsky::{prelude::*, Parser};
// use chumsky::Parser;
mod token;
use resolve_include::resolve_include;
use token::{Op, Token};
mod error;
mod lexer;
mod resolve_include;
mod statement;
use statement::{into_then_expr, stmt_from_expr_top, Statement};

use super::intrinsics;

#[cfg(test)]
mod test;

#[derive(Clone)]
struct ParseContext {
    file_path: Symbol,
}
pub(crate) type ParseError<'src> = Rich<'src, Token>;

fn type_parser<'src>(
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], TypeNodeId, extra::Err<ParseError<'src>>> + Clone {
    let path = ctx.file_path;
    recursive(move |ty| {
        let primitive = select! {
           Token::FloatType => Type::Primitive(PType::Numeric),
           Token::IntegerType => Type::Primitive(PType::Int),
           Token::StringType => Type::Primitive(PType::String)
        }
        .map_with(move |t: Type, ex| {
            let span: SimpleSpan = ex.span();
            t.into_id_with_location(Location::new(span.into_range(), path))
        });

        let tuple = ty
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .delimited_by(just(Token::ParenBegin), just(Token::ParenEnd))
            .map_with(move |t, ex| {
                let span: SimpleSpan = ex.span();
                Type::Tuple(t).into_id_with_location(Location::new(span.into_range(), path))
            })
            .boxed()
            .labelled("Tuple");

        // let _struct_t = todo!();
        let atom = primitive.or(tuple);
        let func = atom
            .clone()
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::ParenBegin), just(Token::ParenEnd))
            .then(just(Token::Arrow).ignore_then(ty.clone()))
            .map_with(move |(a, e), ex| {
                let span: SimpleSpan = ex.span();
                Type::Function(a, e, None)
                    .into_id_with_location(Location::new(span.into_range(), path))
            })
            .boxed()
            .labelled("function");

        func.or(atom).labelled("Type")
    })
}
fn ident_parser<'src>(
) -> impl Parser<'src, &'src [Token], Symbol, extra::Err<ParseError<'src>>> + Clone {
    select! { Token::Ident(s) => s }.labelled("ident")
}
fn literals_parser<'src>(
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>> + Clone {
    select! {
        //Currently Integer literals are treated as float until the integer type is introduced in type system.
        // Token::Int(x) => Literal::Int(x),
        Token::Int(x)=>Literal::Float(x.to_string().to_symbol()),
        Token::Float(x) =>Literal::Float(x.to_symbol()),
        Token::Str(s) => Literal::String(s.to_symbol()),
        Token::SelfLit => Literal::SelfLit,
        Token::Now => Literal::Now,
        Token::SampleRate => Literal::SampleRate,
        Token::PlaceHolder => Literal::PlaceHolder,
    }
    .map_with(move |e, ex| {
        let span: SimpleSpan = ex.span();
        Expr::Literal(e).into_id(Location {
            span: span.into_range(),
            path: ctx.file_path,
        })
    })
    .labelled("literal")
}
fn var_parser<'src>(
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>> + Clone {
    ident_parser().map_with(move |e, ex| {
        Expr::Var(e).into_id(Location {
            span: ex.span().into_range(),
            path: ctx.file_path,
        })
    })
}
fn with_type_annotation<'src, P, O>(
    parser: P,
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], (O, Option<TypeNodeId>), extra::Err<ParseError<'src>>> + Clone
where
    P: Parser<'src, &'src [Token], O, extra::Err<ParseError<'src>>> + Clone,
{
    parser
        .then(just(Token::Colon).ignore_then(type_parser(ctx)).or_not())
        .map(|(id, t)| (id, t))
}

fn lvar_parser_typed<'src>(
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], TypedId, extra::Err<ParseError<'src>>> + Clone {
    with_type_annotation(ident_parser(), ctx.clone())
        .map_with(move |(sym, t), ex| match t {
            Some(ty) => TypedId { id: sym, ty },
            None => TypedId {
                id: sym,
                ty: Type::Unknown.into_id_with_location(Location {
                    span: ex.span().into_range(),
                    path: ctx.file_path,
                }),
            },
        })
        .labelled("lvar_typed")
}
fn pattern_parser<'src>(
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], TypedPattern, extra::Err<ParseError<'src>>> + Clone {
    let pat = recursive(|pat| {
        pat.clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .delimited_by(just(Token::ParenBegin), just(Token::ParenEnd))
            .map(Pattern::Tuple)
            .or(select! {
                Token::Ident(s) => Pattern::Single(s),
                // Note: _ represents an unused variable, but it is treated as
                // an ordinary symbol here.
                Token::PlaceHolder => Pattern::Single("_".to_symbol()),
            })
            .labelled("Pattern")
    });
    with_type_annotation(pat, ctx.clone()).map_with(move |(pat, ty), ex| match ty {
        Some(ty) => TypedPattern { pat, ty },
        None => TypedPattern {
            pat,
            ty: Type::Unknown.into_id_with_location(Location {
                span: ex.span().into_range(),
                path: ctx.file_path,
            }),
        },
    })
}
fn binop_folder<'src, I, OP>(
    prec: I,
    op: OP,
    ctx: ParseContext,
) -> Boxed<'src, 'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>>
where
    I: Parser<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>> + Clone,
    OP: Parser<'src, &'src [Token], (Op, Span), extra::Err<ParseError<'src>>> + Clone,
{
    prec.clone()
        .then(
            op.then_ignore(just(Token::LineBreak).or(just(Token::SemiColon)).repeated())
                .then(prec)
                .repeated(),
        )
        .foldl(move |x, ((op, opspan), y)| {
            let span = x.to_span().start..y.to_span().end;
            let loc = Location {
                span,
                path: ctx.file_path,
            };
            let arg = match op {
                Op::Pipe => return Expr::PipeApply(x, y).into_id(loc.clone()),
                // A@B is a syntactic sugar of _mimium_schedule_at(B, A)
                Op::At => vec![y, x],
                _ => vec![x, y],
            };
            Expr::Apply(
                Expr::Var(op.get_associated_fn_name()).into_id(Location {
                    span: opspan,
                    path: ctx.file_path,
                }),
                arg,
            )
            .into_id(loc)
        })
        .boxed()
}

type ExprParser<'src> = Recursive<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>>;

fn items_parser<'src>(
    expr: ExprParser<'src>,
) -> impl Parser<'src, &'src [Token], Vec<ExprNodeId>, extra::Err<ParseError<'src>>> + Clone {
    expr.separated_by(just(Token::Comma))
        .allow_trailing()
        .collect::<Vec<_>>()
}

fn op_parser<'src, I>(
    apply: I,
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>> + Clone
where
    I: Parser<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>> + Clone,
{
    let ctx = ctx.clone();
    let unary = select! { Token::Op(Op::Minus) => {} }
        .map_with(|e, ex| (e, ex.span()))
        .repeated()
        .then(apply.clone())
        .foldr(move |(_op, op_span), rhs| {
            let rhs_span = rhs.to_span();
            let loc = Location {
                span: op_span.start..rhs_span.start,
                path: ctx.file_path,
            };
            let neg_op = Expr::Var("neg".to_symbol()).into_id(loc);
            let loc = Location {
                span: op_span.start..rhs_span.end,
                path: ctx.file_path,
            };
            Expr::Apply(neg_op, vec![rhs]).into_id(loc)
        })
        .labelled("unary");

    let optoken = move |o: Op| {
        just(Token::Op(o))
            .try_map(|e, s| match e {
                Token::Op(o) => Ok((o, s)),
                _ => Err(Rich::custom(s, "Invalid operator used")),
            })
            .boxed()
    };
    // allow pipe opertor to absorb linebreaks so that it can be also used at
    // the head of the line.
    let pipe = just(Token::LineBreak)
        .repeated()
        .then(just(Token::Op(Op::Pipe)))
        .map_with(|_, ex| (Op::Pipe, ex.span().into_range()))
        .boxed();
    //defining binary operators in order of precedence.
    let ops = [
        optoken(Op::Exponent),
        choice((
            optoken(Op::Product),
            optoken(Op::Divide),
            optoken(Op::Modulo),
        ))
        .boxed(),
        optoken(Op::Sum).or(optoken(Op::Minus)).boxed(),
        optoken(Op::Equal).or(optoken(Op::NotEqual)).boxed(),
        optoken(Op::And),
        optoken(Op::Or),
        choice((
            optoken(Op::LessThan),
            optoken(Op::LessEqual),
            optoken(Op::GreaterThan),
            optoken(Op::GreaterEqual),
        ))
        .boxed(),
        pipe,
        optoken(Op::At),
    ];
    ops.into_iter().fold(unary.boxed(), move |acc, x| {
        binop_folder(acc, x, ctx.clone())
    })
}
fn atom_parser<'src>(
    expr: ExprParser<'src>,
    expr_group: ExprParser<'src>,
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>> + Clone {
    let lambda = lvar_parser_typed(ctx.clone())
        .separated_by(just(Token::Comma))
        .delimited_by(
            just(Token::LambdaArgBeginEnd),
            just(Token::LambdaArgBeginEnd),
        )
        .then(
            just(Token::Arrow)
                .ignore_then(type_parser(ctx.clone()))
                .or_not(),
        )
        .then(expr_group.clone())
        .map_with_span(move |((ids, r_type), body), span| {
            Expr::Lambda(ids, r_type, body).into_id(Location {
                span,
                path: ctx.file_path,
            })
        })
        .labelled("lambda");
    let macro_expand = select! { Token::MacroExpand(s) => Expr::Var(s) }
        .map_with(move |e, ex| {
            e.into_id(Location {
                span: ex.span().into_range(),
                path: ctx.file_path,
            })
        })
        .then_ignore(just(Token::ParenBegin))
        .then(expr_group.clone())
        .then_ignore(just(Token::ParenEnd))
        .map_with_span(move |(id, then), span| {
            let loc = Location {
                span,
                path: ctx.file_path,
            };
            Expr::Escape(Expr::Apply(id, vec![then]).into_id(loc.clone())).into_id(loc)
        })
        .labelled("macroexpand");

    let tuple = items_parser(expr.clone())
        .delimited_by(just(Token::ParenBegin), just(Token::ParenEnd))
        .map_with(move |e, ex| {
            Expr::Tuple(e).into_id(Location {
                span: ex.span().into_range(),
                path: ctx.file_path,
            })
        })
        .labelled("tuple");
    let parenexpr = expr
        .clone()
        .delimited_by(just(Token::ParenBegin), just(Token::ParenEnd))
        .labelled("paren_expr");
    //tuple must  lower precedence than parenexpr, not to parse single element tuple without trailing comma
    choice((
        literals_parser(ctx.clone()),
        var_parser(ctx.clone()),
        lambda,
        macro_expand,
        parenexpr,
        tuple,
    ))
}
fn expr_parser<'src>(expr_group: ExprParser<'src>, ctx: ParseContext) -> ExprParser<'src> {
    recursive(|expr: Recursive<Token, ExprNodeId, ParseError>| {
        enum FoldItem {
            Args(Vec<ExprNodeId>),
            ArrayIndex(ExprNodeId),
        }
        let parenitems = items_parser(expr.clone())
            .delimited_by(just(Token::ParenBegin), just(Token::ParenEnd))
            .map_with(|args, ex| (FoldItem::Args(args), ex.span()));
        let angle_paren_expr = expr
            .clone()
            .delimited_by(just(Token::ArrayBegin), just(Token::ArrayEnd))
            .map_with_span(|e, s| (FoldItem::ArrayIndex(e), s));

        let folder = move |f: ExprNodeId, (item, args_span): (FoldItem, Span)| {
            let f_span = f.to_span();
            let span = f_span.start..args_span.end;
            let loc = Location {
                span,
                path: ctx.file_path,
            };
            match item {
                FoldItem::Args(args) => Expr::Apply(f, args).into_id(loc),
                FoldItem::ArrayIndex(index) => Expr::ArrayAccess(f, index).into_id(loc),
            }
        };

        let apply = atom_parser(expr.clone(), expr_group, ctx.clone())
            .then(angle_paren_expr.or(parenitems).repeated())
            .foldl(folder)
            .labelled("apply");

        op_parser(apply, ctx)
    })
}
// fn expr_statement_parser<'src>(
//     expr_group: ExprParser<'src>,
//     then: ExprParser<'src>,
// ) -> impl Parser<Token, ExprNodeId, Error = ParseError> + Clone + 'src {
//     let let_stmt = just(Token::Let)
//         .ignore_then(pattern_parser().clone())
//         .then_ignore(just(Token::Assign))
//         .then(expr_group.clone())
//         .then_ignore(just(Token::LineBreak).or(just(Token::SemiColon)).repeated())
//         .then(then.clone().or_not())
//         .map_with_span(|((ident, body), then), span| Expr::Let(ident, body, then).into_id(span))
//         .labelled("let_stmt");
//     let assign = placement_parser()
//         .then_ignore(just(Token::Assign))
//         .then(expr_group.clone())
//         .then_ignore(just(Token::LineBreak).or(just(Token::SemiColon)).repeated())
//         .then(then.or_not())
//         .map_with_span(|((ident, body), then), span| {
//             Expr::Then(Expr::Assign(ident, body).into_id(span.clone()), then).into_id(span)
//         })
//         .labelled("assign");
//     let_stmt.or(assign)
// }
fn validate_reserved_pat(id: &TypedPattern, span: SimpleSpan) -> Result<(), ParseError> {
    match &id.pat {
        Pattern::Single(symbol) => validate_reserved_ident(*symbol, span),
        _ => Ok(()),
    }
}

fn validate_reserved_ident<'src>(id: Symbol, span: SimpleSpan) -> Result<(), ParseError<'src>> {
    if intrinsics::BUILTIN_SYMS.with(|syms| syms.binary_search(&id).is_ok()) {
        Err(Rich::custom(
            span,
            "Builtin functions cannot be re-defined.",
        ))
    } else {
        Ok(())
    }
}

fn statement_parser<'src>(
    expr: ExprParser<'src>,
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], (Statement, Location), extra::Err<ParseError<'src>>> + Clone {
    let let_ = just(Token::Let)
        .ignore_then(pattern_parser(ctx.clone()).validate(|pat, ex, emit| {
            if let Err(e) = validate_reserved_pat(&pat, ex.span()) {
                emit(e);
            }
            pat
        }))
        .then_ignore(just(Token::Assign))
        .then(expr.clone())
        .map_with_span(|(ident, body), span| (Statement::Let(ident, body), span))
        .labelled("let");
    let letrec = just(Token::LetRec)
        .ignore_then(lvar_parser_typed(ctx.clone()).validate(|ident, ex, emit| {
            if let Err(e) = validate_reserved_ident(ident.id, ex.span()) {
                emit(e);
            }
            ident
        }))
        .then_ignore(just(Token::Assign))
        .then(expr.clone())
        .map_with_span(|(ident, body), span| (Statement::LetRec(ident, body), span))
        .labelled("letrec");
    let assign = var_parser(ctx.clone())
        .then_ignore(just(Token::Assign))
        .then(expr.clone())
        .map_with_span(|(lvar, body), span| (Statement::Assign(lvar, body), span))
        .labelled("assign");
    let single = expr.map_with_span(|e, span| (Statement::Single(e), span));
    let_.or(letrec).or(assign).or(single).map(move |(t, span)| {
        (
            t,
            Location {
                span,
                path: ctx.file_path,
            },
        )
    })
}
fn statements_parser<'src>(
    expr: ExprParser<'src>,
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], Option<ExprNodeId>, extra::Err<ParseError<'src>>> + Clone {
    statement_parser(expr, ctx)
        .separated_by(just(Token::LineBreak).or(just(Token::SemiColon)).repeated())
        .allow_leading()
        .allow_trailing()
        .recover_with(skip_until([Token::LineBreak, Token::SemiColon], |_| vec![]))
        .map(|stmts| into_then_expr(&stmts))
}

fn block_parser<'src>(
    expr: ExprParser<'src>,
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>> + Clone {
    let stmts = statements_parser(expr, ctx.clone());
    stmts
        .delimited_by(just(Token::BlockBegin), just(Token::BlockEnd))
        .map_with(move |stmts, ex| {
            Expr::Block(stmts).into_id(Location {
                span: ex.span().into_range(),
                path: ctx.file_path,
            })
        })
        .recover_with(nested_delimiters(
            Token::BlockBegin,
            Token::BlockEnd,
            [],
            |_| Expr::Error.into_id_without_span(),
        ))
}
// expr_group contains let statement, assignment statement, function definiton,... they cannot be placed as an argument for apply directly.
fn exprgroup_parser<'src>(ctx: ParseContext) -> ExprParser<'src> {
    recursive(move |expr_group: ExprParser<'src>| {
        let expr = expr_parser(expr_group.clone(), ctx.clone());

        let block = block_parser(expr_group.clone(), ctx.clone());
        //todo: should be recursive(to paranthes be not needed)
        let if_ = just(Token::If)
            .ignore_then(
                expr_group
                    .clone()
                    .delimited_by(just(Token::ParenBegin), just(Token::ParenEnd)),
            )
            .then(expr_group.clone())
            .then(just(Token::Else).ignore_then(expr_group.clone()).or_not())
            .map_with(move |((cond, then), opt_else), ex| {
                Expr::If(cond, then, opt_else).into_id(Location {
                    span: ex.span().into_range(),
                    path: ctx.file_path,
                })
            })
            .labelled("if");

        block
            .or(if_)
            // .or(expr_statement_parser(expr_group.clone(), expr_group))
            .or(expr.clone())
    })
}

fn gen_unknown_function_type(
    ids: &[TypedId],
    r_type: Option<TypeNodeId>,
    loc: Location,
) -> TypeNodeId {
    let atypes = ids
        .iter()
        .map(|tid| {
            if !tid.is_unknown() {
                tid.ty
            } else {
                Type::Unknown.into_id_with_location(loc.clone())
            }
        })
        .collect::<Vec<_>>();
    Type::Function(
        atypes,
        r_type.unwrap_or_else(|| Type::Unknown.into_id_with_location(loc.clone())),
        None,
    )
    .into_id_with_location(loc)
}
fn func_parser<'src>(
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>> + Clone {
    let exprgroup = exprgroup_parser(ctx.clone());
    let lvar = lvar_parser_typed(ctx.clone());
    let blockstart = just(Token::BlockBegin)
        .then_ignore(just(Token::LineBreak).or(just(Token::SemiColon)).repeated());
    let blockend = just(Token::LineBreak)
        .or(just(Token::SemiColon))
        .repeated()
        .ignore_then(just(Token::BlockEnd));
    let fnparams = lvar
        .clone()
        .separated_by(just(Token::Comma))
        .delimited_by(just(Token::ParenBegin), just(Token::ParenEnd))
        .labelled("fnparams");

    let function_s = just(Token::Function)
        .ignore_then(lvar.clone().validate(|ident, ex, emit| {
            let span: SimpleSpan = ex.span();
            if let Err(e) = validate_reserved_ident(ident.id, span) {
                emit(e);
            }
            ident
        }))
        .then(fnparams.clone())
        .then(
            just(Token::Arrow)
                .ignore_then(type_parser(ctx.clone()))
                .or_not(),
        )
        .then(
            block_parser(exprgroup.clone(), ctx.clone()).map(|e| match e.to_expr() {
                Expr::Block(e) => e.unwrap(),
                _ => e,
            }),
        )
        .map_with(move |(((fname, ids), r_type), block), ex| {
            let loc = Location {
                span: ex.span().into_range(),
                path: ctx.file_path,
            };
            let fname = TypedId {
                id: fname.id,
                ty: gen_unknown_function_type(&ids, r_type, loc.clone()),
            };
            (
                Statement::LetRec(fname, Expr::Lambda(ids, r_type, block).into_id(loc.clone())),
                loc,
            )
        })
        .labelled("function decl");

    let macro_s = just(Token::Macro)
        .ignore_then(lvar.clone())
        .then(fnparams.clone())
        .then(
            exprgroup
                .clone()
                .delimited_by(blockstart.clone(), blockend.clone())
                .map(Expr::Bracket),
        )
        .map_with_span(move |((fname, ids), block), span| {
            let loc = Location {
                span,
                path: ctx.file_path,
            };
            (
                Statement::MacroExpand(
                    fname,
                    Expr::Lambda(ids, None, block.into_id(loc.clone())).into_id(loc.clone()),
                ),
                loc,
            )
        })
        .labelled("macro definition");
    let global_stmt = statement_parser(exprgroup.clone(), ctx.clone());
    let stmt = function_s.or(macro_s).or(global_stmt);
    let separator = just(Token::LineBreak).or(just(Token::SemiColon)).repeated();
    let stmts = stmt
        .map(|s: (Statement, Location)| vec![s])
        .or(preprocess_parser(ctx.clone()).map_with(move |e, ex| {
            let span: SimpleSpan = ex.span();
            stmt_from_expr_top(e)
                .into_iter()
                .map(|st| (st, Location::new(span.into_range(), ctx.file_path)))
                .collect()
        }))
        .separated_by(separator)
        .allow_leading()
        .allow_trailing()
        .recover_with(skip_until([Token::LineBreak, Token::SemiColon], |_| vec![]))
        .flatten()
        .map(|stmt| into_then_expr(&stmt).unwrap_or(Expr::Error.into_id_without_span()));
    stmts
}

fn preprocess_parser<'src>(
    ctx: ParseContext,
) -> impl Parser<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>> + Clone {
    just(Token::Include)
        .ignore_then(
            select! {Token::Str(s) => s}
                .delimited_by(just(Token::ParenBegin), just(Token::ParenEnd)),
        )
        .try_map(move |filename, span: SimpleSpan| {
            let cfile = ctx.file_path.as_str();
            let (c, errs) = resolve_include(cfile, &filename, span.into_range());
            if errs.is_empty() {
                Ok(c)
            } else {
                let e = errs.into_iter().fold(
                    Rich::<Token>::custom(
                        span.clone(),
                        format!("failed to resolve include for {filename}"),
                    ),
                    |simple_e, reportable_e| {
                        let wrapped = Rich::<Token>::custom(span.clone(), reportable_e.to_string());
                        wrapped.merge(simple_e)
                    },
                );
                Err(e)
            }
        })
}
fn parser<'src>(
    current_file: Option<PathBuf>,
) -> impl Parser<'src, &'src [Token], ExprNodeId, extra::Err<ParseError<'src>>> + Clone {
    let separator = just(Token::LineBreak)
        .ignored()
        .or(just(Token::SemiColon).ignored());
    let ctx = ParseContext {
        file_path: current_file.map_or("".to_symbol(), |p| p.to_string_lossy().to_symbol()),
    };
    func_parser(ctx)
        .padded_by(separator.repeated())
        .then_ignore(end())
}

pub(crate) fn add_global_context(ast: ExprNodeId, file_path: Symbol) -> ExprNodeId {
    let span = ast.to_span();
    let loc = Location {
        span: span.clone(),
        path: file_path,
    };
    let res = Expr::Let(
        TypedPattern {
            pat: Pattern::Single(GLOBAL_LABEL.to_symbol()),
            ty: Type::Unknown.into_id_with_location(loc.clone()),
        },
        Expr::Lambda(vec![], None, ast).into_id(loc.clone()),
        None,
    );
    res.into_id(loc)
}
pub fn parse(
    src: &str,
    current_file: Option<PathBuf>,
) -> (ExprNodeId, Vec<Box<dyn ReportableError>>) {
    let len = src.chars().count();
    let (tokens, lex_errs) = lexer::lexer().parse_recovery(src);
    let lex_errs = lex_errs.into_iter().map(|e| -> Box<dyn ReportableError> {
        Box::new(error::ParseError::<char> {
            content: e,
            file: current_file
                .clone()
                .unwrap_or_default()
                .to_string_lossy()
                .to_symbol(),
        })
    });
    if let Some(t) = tokens {
        let tokens_comment_filtered = t.into_iter().filter_map(|(tkn, span)| match tkn {
            Token::Comment(token::Comment::SingleLine(_)) => Some((Token::LineBreak, span)),
            Token::Comment(token::Comment::MultiLine(_)) => None,
            _ => Some((tkn.clone(), span)),
        });
        let (ast, parse_errs) = parser(current_file.clone()).parse_recovery(
            chumsky::Stream::from_iter(len..len + 1, tokens_comment_filtered),
        );
        let errs = parse_errs
            .into_iter()
            .map(|e| -> Box<dyn ReportableError> {
                Box::new(error::ParseError {
                    content: e,
                    file: current_file
                        .clone()
                        .unwrap_or_default()
                        .to_string_lossy()
                        .to_symbol(),
                })
            })
            .chain(lex_errs)
            .collect::<Vec<_>>();
        (ast.unwrap_or(Expr::Error.into_id_without_span()), errs)
    } else {
        (Expr::Error.into_id_without_span(), lex_errs.collect())
    }
}
