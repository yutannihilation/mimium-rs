use std::{
    cell::RefCell,
    collections::BTreeMap,
    fmt::{self, Display},
    hash::Hash,
};

use slotmap::SlotMap;
use string_interner::{backend::StringBackend, StringInterner};

use crate::{ast::Expr, dummy_span, types::Type, utils::metadata::Span};
slotmap::new_key_type! {
    pub struct ExprKey;
    pub struct TypeKey;
}

pub struct SessionGlobals {
    pub symbol_interner: StringInterner<StringBackend<usize>>,
    pub expr_storage: SlotMap<ExprKey, Expr>,
    pub type_storage: SlotMap<TypeKey, Type>,
    pub span_storage: BTreeMap<NodeId, Span>,
}

impl SessionGlobals {
    fn store_expr(&mut self, expr: Expr) -> ExprNodeId {
        let key = self.expr_storage.insert(expr);
        ExprNodeId(key)
    }

    fn store_span<T: ToNodeId>(&mut self, node_id: T, span: Span) {
        self.span_storage.insert(node_id.to_node_id(), span);
    }

    pub fn store_type(&mut self, ty: Type) -> TypeNodeId {
        let key = self.type_storage.insert(ty);
        TypeNodeId(key)
    }

    pub fn store_expr_with_span(&mut self, expr: Expr, span: Span) -> ExprNodeId {
        let expr_id = self.store_expr(expr);
        self.store_span(expr_id, span);
        expr_id
    }

    pub fn store_type_with_span(&mut self, ty: Type, span: Span) -> TypeNodeId {
        let type_id = self.store_type(ty);
        self.store_span(type_id, span);
        type_id
    }

    // TODO: in theory, instead of cloning, this can return &Expr with an
    // extended lifetime by `std::mem::transmute()` just like we do in
    // Symbol::as_str(). However, we would get segfault for some reason.
    //
    // cf. https://github.com/tomoyanonymous/mimium-rs/pull/27#issuecomment-2306226748
    pub fn get_expr(&self, expr_id: ExprNodeId) -> Expr {
        unsafe { self.expr_storage.get_unchecked(expr_id.0) }.clone()
    }

    pub fn get_type(&self, type_id: TypeNodeId) -> Type {
        unsafe { self.type_storage.get_unchecked(type_id.0) }.clone()
    }

    pub fn get_span<T: ToNodeId>(&self, node_id: T) -> Option<&Span> {
        self.span_storage.get(&node_id.to_node_id())
    }
}

thread_local!(static SESSION_GLOBALS: RefCell<SessionGlobals> =  RefCell::new(
    SessionGlobals {
        symbol_interner: StringInterner::new(),
        expr_storage: SlotMap::with_key(),
        type_storage: SlotMap::with_key(),
        span_storage: BTreeMap::new()
    }
));

pub fn with_session_globals<R, F>(f: F) -> R
where
    F: FnOnce(&mut SessionGlobals) -> R,
{
    SESSION_GLOBALS.with_borrow_mut(f)
}

#[derive(Default, Copy, Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct Symbol(pub usize); //Symbol Trait is implemented on usize

pub trait ToSymbol {
    fn to_symbol(&self) -> Symbol;
}

impl<T: AsRef<str>> ToSymbol for T {
    fn to_symbol(&self) -> Symbol {
        Symbol(with_session_globals(|session_globals| {
            session_globals.symbol_interner.get_or_intern(self.as_ref())
        }))
    }
}

impl Symbol {
    pub fn as_str(&self) -> &str {
        with_session_globals(|session_globals| unsafe {
            // This transmute is needed to convince the borrow checker. Since
            // the session_global should exist until the end of the session,
            // this &str should live sufficiently long.
            std::mem::transmute::<&str, &str>(
                session_globals
                    .symbol_interner
                    .resolve(self.0)
                    .expect("invalid symbol"),
            )
        })
    }
}

// Note: to_string() is auto-implemented by this
impl Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NodeId {
    ExprArena(ExprKey),
    TypeArena(TypeKey),
}

#[derive(Clone, Copy, Default)]
pub struct ExprNodeId(pub ExprKey);

#[derive(Clone, Copy, Default)]
pub struct TypeNodeId(pub TypeKey);

// traits required for Key trait

impl PartialEq for ExprNodeId {
    fn eq(&self, other: &Self) -> bool {
        self.to_expr() == other.to_expr() && self.to_span() == other.to_span()
    }
}

impl PartialEq for TypeNodeId {
    fn eq(&self, other: &Self) -> bool {
        self.to_type() == other.to_type() && self.to_span() == other.to_span()
    }
}
impl Eq for TypeNodeId {}
impl Hash for TypeNodeId {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl ExprNodeId {
    pub fn to_expr(&self) -> Expr {
        with_session_globals(|session_globals| session_globals.get_expr(*self))
    }

    pub fn to_span(&self) -> Span {
        with_session_globals(|session_globals| match session_globals.get_span(*self) {
            Some(span) => span.clone(),
            None => dummy_span!(),
        })
    }
}

impl TypeNodeId {
    pub fn to_type(&self) -> Type {
        with_session_globals(|session_globals| session_globals.get_type(*self))
    }

    pub fn to_span(&self) -> Span {
        with_session_globals(|session_globals| match session_globals.get_span(*self) {
            Some(span) => span.clone(),
            None => dummy_span!(),
        })
    }
    // Flatten a composite type into a list of types so that the offset of the
    // element can be calculated easily. For example:
    //
    // original:       Tuple(float, function, Tuple(float, float))
    // flattened form: [float, function, float, float]
    pub fn flatten(&self) -> Vec<Self> {
        match self.to_type() {
            Type::Tuple(t) => t.iter().flat_map(|t| t.flatten()).collect::<Vec<_>>(),
            Type::Struct(t) => t.iter().flat_map(|(_, t)| t.flatten()).collect::<Vec<_>>(),
            _ => vec![*self],
        }
    }
}

pub trait ToNodeId {
    fn to_node_id(&self) -> NodeId;
}

impl ToNodeId for ExprNodeId {
    fn to_node_id(&self) -> NodeId {
        NodeId::ExprArena(self.0)
    }
}

impl ToNodeId for TypeNodeId {
    fn to_node_id(&self) -> NodeId {
        NodeId::TypeArena(self.0)
    }
}
impl std::fmt::Display for ExprNodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let span = self.to_span();
        write!(f, "{:?},{}..{}", self.to_expr(), span.start, span.end)
    }
}
impl std::fmt::Debug for ExprNodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let span = self.to_span();
        write!(f, "{:#?},{}..{}", self.to_expr(), span.start, span.end)
    }
}
impl std::fmt::Display for TypeNodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let span = self.to_span();

        write!(f, "{:?},{}..{}", self.to_type(), span.start, span.end)
    }
}
impl std::fmt::Debug for TypeNodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let span = self.to_span();

        write!(f, "{:#?},{}..{}", self.to_type(), span.start, span.end)
    }
}
