use ast::*;

pub mod prelude {
    pub use super::{
        YieldEvent,
        AnyExprAndEvent,
        RecursiveChildsIter,
        childs_recursive_with_event,
        childs_recursive_entering,
        childs_recursive_leaving
    };
}

/// Iterate recursively over the given `AnyExpr` and all of its child expressions
/// with an indicator whether the node was entered or left.
/// 
/// # Note
/// 
/// - This iterates twice over all expression. Once for entering and once for leaving.
pub fn childs_recursive_with_event(expr: &AnyExpr) -> RecursiveChildsIter {
    RecursiveChildsIter::new(expr)
}

/// Iterate recursively over the given `AnyExpr` and all of its child expressions.
/// 
/// # Note
/// 
/// - Yields parent expressions before their childs.
pub fn childs_recursive_entering<'a>(expr: &'a AnyExpr) -> impl Iterator<Item=&'a AnyExpr> {
    childs_recursive_with_event(expr)
        .filter_map(|expr_and_event| match expr_and_event.event {
            YieldEvent::Entering => Some(expr_and_event.expr),
            YieldEvent::Leaving  => None
        })
}

/// Iterate recursively over the given `AnyExpr` and all of its child expressions.
/// 
/// # Note
/// 
/// - Yields parent expressions after their childs.
pub fn childs_recursive_leaving<'a>(expr: &'a AnyExpr) -> impl Iterator<Item=&'a AnyExpr> {
    childs_recursive_with_event(expr)
        .filter_map(|expr_and_event| match expr_and_event.event {
            YieldEvent::Leaving  => Some(expr_and_event.expr),
            YieldEvent::Entering => None
        })
}

/// States if a yielded expression in the recursive iteration
/// is entering scope (childs are not yet yielded) or leaving scope
/// (childs have been yielded).
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum YieldEvent {
    /// States that the expression was just entered.
    /// 
    /// At this point none of the expression's childs have
    /// been yielded by the iterator.
    Entering,
    /// States that the expression was just left.
    /// 
    /// At this point all of the expression's childs have
    /// been yielded by the iterator.
    Leaving
}

/// Iterates over all expressions of an AST recursively.
#[derive(Debug, Clone)]
pub struct RecursiveChildsIter<'it> {
    path: Vec<AnyExprAndEvent<'it>>
}

/// Holds an `AnyExpr` and a `YieldEvent`.
/// 
/// This type is yielded by the recursive event driven iterator over expressions.
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

#[cfg(test)]
mod tests {
    use super::*;
    use ast::factory::prelude::*;

    #[test]
    fn simple() {
        fn create_ast() -> Result<AnyExpr, String> {
            let b = PlainExprTreeBuilder::default();
            b.or(
                b.and(
                    b.bool_const(true),
                    b.bool_const(false)
                ),
                b.xor(
                    b.bool_const(false),
                    b.bool_const(true)
                )
            )
        }

        let b = PlainExprTreeBuilder::default();
        let expr = create_ast().unwrap();
        let mut rec_iter = childs_recursive_with_event(&expr);

        assert_eq!(rec_iter.next(), Some(AnyExprAndEvent::entering(&create_ast().unwrap())));
        assert_eq!(rec_iter.next(),
            Some(AnyExprAndEvent::entering(&
                b.and(
                    b.bool_const(true),
                    b.bool_const(false)
                ).unwrap()
            )));
        assert_eq!(rec_iter.next(), Some(AnyExprAndEvent::entering(&b.bool_const(true).unwrap())));
        assert_eq!(rec_iter.next(), Some(AnyExprAndEvent::leaving(&b.bool_const(true).unwrap())));
        assert_eq!(rec_iter.next(), Some(AnyExprAndEvent::entering(&b.bool_const(false).unwrap())));
        assert_eq!(rec_iter.next(), Some(AnyExprAndEvent::leaving(&b.bool_const(false).unwrap())));
        assert_eq!(rec_iter.next(),
            Some(AnyExprAndEvent::leaving(&
                b.and(
                    b.bool_const(true),
                    b.bool_const(false)
                ).unwrap()
            )));
        assert_eq!(rec_iter.next(),
            Some(AnyExprAndEvent::entering(&
                b.xor(
                    b.bool_const(false),
                    b.bool_const(true)
                ).unwrap()
            )));
        assert_eq!(rec_iter.next(), Some(AnyExprAndEvent::entering(&b.bool_const(false).unwrap())));
        assert_eq!(rec_iter.next(), Some(AnyExprAndEvent::leaving(&b.bool_const(false).unwrap())));
        assert_eq!(rec_iter.next(), Some(AnyExprAndEvent::entering(&b.bool_const(true).unwrap())));
        assert_eq!(rec_iter.next(), Some(AnyExprAndEvent::leaving(&b.bool_const(true).unwrap())));
        assert_eq!(rec_iter.next(), 
            Some(AnyExprAndEvent::leaving(&
                b.xor(
                    b.bool_const(false),
                    b.bool_const(true)
                ).unwrap()
            )));
        assert_eq!(rec_iter.next(), Some(AnyExprAndEvent::leaving(&create_ast().unwrap())));
        assert_eq!(rec_iter.next(), None);
    }
}
