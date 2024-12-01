
open Expr

type property = Getput | Putget | Disdelta

(** interatively generate a counterexample for a given property *)
val gen_counterexample: bool -> bool -> property -> int -> int -> expr -> string * rterm list
