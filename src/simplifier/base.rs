use ast2::prelude::*;

use std::mem;
use std::ops::BitOrAssign;

pub mod prelude {
    pub use super::{
        Transformer,
        TransformResult,
        AnyExprAndTransformResult
    };
}

/// Describes whether the result of a transformation actually transformed
/// the input or did nothing to it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TransformResult {
    /// States that the transformation had no effect on the input.
    Identity,
    /// States that the transformation transformed the input.
    Transformed
}

impl BitOrAssign for TransformResult {
    fn bitor_assign(&mut self, rhs: TransformResult) {
        match rhs {
            TransformResult::Transformed => *self = rhs,
            TransformResult::Identity    => ()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AnyExprAndTransformResult {
    pub result: TransformResult,
    pub expr: AnyExpr
}

impl AnyExprAndTransformResult {
    pub fn new(result: TransformResult, expr: AnyExpr) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult{expr, result}
    }

    pub fn identity<E>(expr: E) -> AnyExprAndTransformResult
        where E: Into<AnyExpr>
    {
        AnyExprAndTransformResult::new(TransformResult::Identity, expr.into())
    }
}

pub trait Transformer: Copy {
    fn transform_cond(self, cond: expr::IfThenElse) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(cond)
    }
    fn transform_var(self, bool_const: expr::Symbol) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bool_const)
    }

    fn transform_bool_const(self, bool_const: expr::BoolConst) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bool_const)
    }

    fn transform_bool_equals(self, bool_equals: expr::BoolEquals) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bool_equals)
    }

    fn transform_and(self, and: expr::And) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(and)
    }

    fn transform_or(self, or: expr::Or) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(or)
    }

    fn transform_not(self, not: expr::Not) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(not)
    }
}

// #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
// struct NoopTransformer;
// impl Transformer for NoopTransformer {}
// impl AutoImplAnyTransformer for NoopTransformer {}
// impl Default for NoopTransformer {
//     fn default() -> Self {
//         NoopTransformer
//     }
// }

// #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
// pub struct PrintingTransformer(char);

// impl Transformer for PrintingTransformer {
//     fn transform_cond(self, cond: expr::IfThenElse) -> AnyExprAndTransformResult {
//         println!("PrintingTransformer({:?}) - IfThenElse", self.0);
//         AnyExprAndTransformResult::identity(cond)
//     }
//     fn transform_var(self, symbol: expr::Symbol) -> AnyExprAndTransformResult {
//         println!("PrintingTransformer({:?}) - Symbol: {:?}", self.0, symbol.name);
//         AnyExprAndTransformResult::identity(symbol)
//     }

//     fn transform_bool_const(self, bool_const: expr::BoolConst) -> AnyExprAndTransformResult {
//         println!("PrintingTransformer({:?}) - BoolConst: {:?}", self.0, bool_const.val);
//         AnyExprAndTransformResult::identity(bool_const)
//     }

//     fn transform_bool_equals(self, bool_equals: expr::BoolEquals) -> AnyExprAndTransformResult {
//         println!("PrintingTransformer({:?}) - BoolEquals", self.0);
//         AnyExprAndTransformResult::identity(bool_equals)
//     }

//     fn transform_and(self, and: expr::And) -> AnyExprAndTransformResult {
//         println!("PrintingTransformer({:?}) - And", self.0);
//         AnyExprAndTransformResult::identity(and)
//     }

//     fn transform_or(self, or: expr::Or) -> AnyExprAndTransformResult {
//         println!("PrintingTransformer({:?}) - Or", self.0);
//         AnyExprAndTransformResult::identity(or)
//     }

//     fn transform_not(self, not: expr::Not) -> AnyExprAndTransformResult {
//         println!("PrintingTransformer({:?}) - Not", self.0);
//         AnyExprAndTransformResult::identity(not)
//     }
// }

// impl AutoImplAnyTransformer for PrintingTransformer {}
// impl PrintingTransformer {
//     fn new(ch: char) -> Self {
//         PrintingTransformer(ch)
//     }
// }

trait AnyTransformer: Copy {
    fn transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult;
    fn into_transform_any_expr(self, expr: AnyExpr) -> AnyExprAndTransformResult;
}

trait AutoImplAnyTransformer {}

impl<T> AnyTransformer for T where T: Transformer + AutoImplAnyTransformer {
    fn transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
        let temp = AnyExpr::from(expr::BoolConst::f());
		let input = mem::replace(expr, temp);
		let AnyExprAndTransformResult{result, expr: transformed} =
            self.into_transform_any_expr(input);
        mem::replace(expr, transformed);
        result
    }

    fn into_transform_any_expr(self, expr: AnyExpr) -> AnyExprAndTransformResult {
        use self::AnyExpr::*;
        match expr {
            IfThenElse(expr) => self.transform_cond(expr),
            Symbol(expr) => self.transform_var(expr),
            BoolConst(expr) => self.transform_bool_const(expr),
            BoolEquals(expr) => self.transform_bool_equals(expr),
            Not(expr) => self.transform_not(expr),
            And(expr) => self.transform_and(expr),
            Or(expr) => self.transform_or(expr),
            _ => unimplemented!()
        }
    }
}

// #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
// struct TransformerTraverser<T1, T2>
//     where T1: AnyTransformer,
//           T2: AnyTransformer
// {
//     fst: T1,
//     snd: T2
// }

// impl<T1, T2> TransformerTraverser<T1, T2>
//     where T1: AnyTransformer,
//           T2: AnyTransformer
// {
//     pub fn new(fst: T1, snd: T2) -> Self {
//         TransformerTraverser{fst, snd}
//     }

//     fn forward_transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
//         let mut result = TransformResult::Identity;
//         result |= self.fst.transform_any_expr(expr);
//         result |= self.snd.transform_any_expr(expr);
//         result
//     }

//     pub fn traverse_transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
//         let mut result = TransformResult::Identity;
//         for child in expr.childs_mut() {
//             result |= self.traverse_transform_any_expr(child);
//         }
//         result |= self.forward_transform_any_expr(expr);
//         result
//     }
// }

// impl<T1, T2> AnyTransformer for TransformerTraverser<T1, T2>
//     where T1: AnyTransformer,
//           T2: AnyTransformer
// {
//     fn transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
//         self.traverse_transform_any_expr(expr)
//     }

//     fn into_transform_any_expr(self, expr: AnyExpr) -> AnyExprAndTransformResult {
//         let mut expr = expr;
//         let result = self.transform_any_expr(&mut expr);
//         AnyExprAndTransformResult::new(result, expr)
//     }
// }




macro_rules! create_base_transformer {
    (struct $name:ident; $(($id:ident, $trans:ty)),*) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
        pub struct $name {
            $($id: $trans),*
        }

        impl $name {
            pub fn new($($id: $trans),*) -> Self {
                $name{
                    $($id),*
                }
            }

            fn forward_transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
                let mut result = TransformResult::Identity;
                $(result |= self.$id.transform_any_expr(expr));*;
                result
            }

            pub fn traverse_transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
                let mut result = TransformResult::Identity;
                for child in expr.childs_mut() {
                    result |= self.traverse_transform_any_expr(child);
                }
                result |= self.forward_transform_any_expr(expr);
                result
            }
        }

        impl AnyTransformer for $name {
            fn transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
                self.traverse_transform_any_expr(expr)
            }

            fn into_transform_any_expr(self, expr: AnyExpr) -> AnyExprAndTransformResult {
                let mut expr = expr;
                let result = self.transform_any_expr(&mut expr);
                AnyExprAndTransformResult::new(result, expr)
            }
        }
    }
}

create_base_transformer!{
    struct BaseTransformer;

//     (_0, PrintingTransformer),
//     (_1, PrintingTransformer),
//     (_2, PrintingTransformer),
//     (_3, PrintingTransformer)
}





// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn simple() {
//         let transformer = BaseTransformer::new(
//             PrintingTransformer::new('A'),
//             PrintingTransformer::new('B'),
//             PrintingTransformer::new('C'),
//             PrintingTransformer::new('D')
//         );
//         let b = PlainExprTreeBuilder::default();
//         let mut expr = b.cond(
//             b.not(
//                 b.bool_equals(
//                     b.bool_var("x"),
//                     b.bool_var("y")
//                 )
//             ),
//             b.and(
//                 b.bool_const(true),
//                 b.bool_var("a")
//             ),
//             b.or(
//                 b.bool_const(false),
//                 b.bool_var("b")
//             )
//         ).unwrap();
//         transformer.transform_any_expr(&mut expr);
//     }
// }
