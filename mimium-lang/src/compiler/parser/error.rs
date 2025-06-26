use crate::interner::Symbol;
use crate::utils::error::ReportableError;
use crate::utils::metadata::Location;
use chumsky;
use chumsky::span::SimpleSpan;
use std::fmt;
use std::hash::Hash;
// pub struct LexError(chumsky::error::Rich<'src, char>);
#[derive(Debug)]
pub struct ParseError<'a, T>
where
    T: Hash + std::cmp::Eq + fmt::Debug + fmt::Display,
{
    pub content: chumsky::error::Rich<'a, T>,
    pub file: Symbol,
}

impl<'a, T> From<ParseError<'a, T>> for chumsky::error::Rich<'a, T>
where
    T: Hash + std::cmp::Eq + fmt::Debug + fmt::Display,
{
    fn from(value: ParseError<'a, T>) -> Self {
        value.content
    }
}

impl<'a, T> fmt::Display for ParseError<'a, T>
where
    T: Hash + std::cmp::Eq + fmt::Debug + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.content)
    }
}

impl<'a, T> std::error::Error for ParseError<'a, T> where
    T: Hash + std::cmp::Eq + fmt::Debug + fmt::Display
{
}

impl<'a, T> ReportableError for ParseError<'a, T>
where
    T: Hash + std::cmp::Eq + fmt::Debug + fmt::Display,
{
    fn get_message(&self) -> String {
        match self.content.reason() {
            chumsky::error::RichReason::Unexpected
            | chumsky::error::RichReason::Unclosed { .. } => {
                format!(
                    "{}{}, expected {}",
                    if self.content.found().is_some() {
                        "unexpected token"
                    } else {
                        "unexpected end of input"
                    },
                    if let Some(label) = self.content.label() {
                        format!(" while parsing {label}")
                    } else {
                        " something else".to_string()
                    },
                    if self.content.expected().count() == 0 {
                        "somemething else".to_string()
                    } else {
                        self.content
                            .expected()
                            .map(|expected| match expected {
                                Some(expected) => expected.to_string(),
                                None => "end of input".to_string(),
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    }
                )
            }
            chumsky::error::RichReason::Custom(msg) => msg.clone(),
        }
    }

    fn get_labels(&self) -> Vec<(Location, String)> {
        let span: SimpleSpan = self.content.span().clone();
        vec![(
            Location {
                span: span.into_range(),
                path: self.file,
            },
            self.get_message(),
        )]
    }
}
