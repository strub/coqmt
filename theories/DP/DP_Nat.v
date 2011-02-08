(*
 *  [Require Import] this module to activate the embedding, in the Coq
 * conversion, of the decision procedures on natural numbers
 *)

Require Import Arith Max Min.

Load Theory nattheory.

Bind Theory nattheory As nattheory
  Sort    Binded By nat
  Symbols Binded By
    0    for zero ,
    S    for succ ,
    plus for plus ,
    mult for time ,
    max  for max  ,
    min  for min

  Axioms Proved By
    plus_0_r,
    (fun x y => sym_eq (plus_n_Sm x y)),
    mult_0_r,
    (fun x y => sym_eq (mult_n_Sm x y)),
    min_0_r,
    min_0_l,
    succ_min_distr,
    max_0_r,
    max_0_l,
    succ_max_distr.
