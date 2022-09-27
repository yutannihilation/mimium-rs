#![feature(box_patterns)]

use utils::metadata::WithMeta;

pub mod closure_convert;
pub mod feedconvert;
pub mod hir_solve_stage;

pub fn generate_mir(src: WithMeta<hir::expr::Expr>) -> mir::Mir {
    mir::Mir(Vec::<mir::TopLevel>::new())
}
