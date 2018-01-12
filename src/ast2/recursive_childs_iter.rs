use ast2::*;

pub mod prelude {
    pub use super::{
        YieldEvent,
        AnyExprAndEvent,
        RecursiveChildsIter
    };
}

/// States if a yielded expression in the recursive iteration
/// is entering scope (childs are not yet yielded) or leaving scope
/// (childs have been yielded).
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum YieldEvent { Entering, Leaving }

/// Iterates over all expressions of an AST recursively.
#[derive(Debug, Clone)]
pub struct RecursiveChildsIter<'it> {
    path: Vec<AnyExprAndEvent<'it>>
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct AnyExprAndEvent<'it> {
    /// The expression of this yield item.
    pub expr: &'it AnyExpr,
    /// The event of this yield item.
    pub event: YieldEvent
}

impl<'it> AnyExprAndEvent<'it> {
    /// Returns an `AnyExprAndEvent` for the given `AnyExpr` and an entering event.
    pub fn entering<'e>(expr: &'e AnyExpr) -> AnyExprAndEvent<'e> {
        AnyExprAndEvent{ event: YieldEvent::Entering, expr }
    }

    /// Returns an `AnyExprAndEvent` for the given `AnyExpr` and a leaving event.
    pub fn leaving<'e>(expr: &'e AnyExpr) -> AnyExprAndEvent<'e> {
        AnyExprAndEvent{ event: YieldEvent::Leaving, expr }
    }
}

impl<'it> RecursiveChildsIter<'it> {
    /// Returns a new `RecursiveChildsIter` for the given child iterable.
    /// 
    /// This iterator iterates over all expressions (inclusive the given expression)
    /// recursively. Every expression is yielded twice, once with an entering event
    /// and once with a leaving event.
    pub fn new<'e>(expr: &'e AnyExpr) -> RecursiveChildsIter<'e> {
        RecursiveChildsIter{ path: vec![AnyExprAndEvent::entering(expr)] }
    }
}

impl<'it> Iterator for RecursiveChildsIter<'it> {
    type Item = AnyExprAndEvent<'it>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.path.pop() {
            None => None,
            Some(item) => match item.event {
                YieldEvent::Leaving => Some(item),
                YieldEvent::Entering => {
                    self.path.push(AnyExprAndEvent::leaving(item.expr));
                    for child in item.expr.childs().rev() {
                        self.path.push(AnyExprAndEvent::entering(child));
                    }
                    Some(AnyExprAndEvent::entering(item.expr))
                }
            }
        }
    }
}
