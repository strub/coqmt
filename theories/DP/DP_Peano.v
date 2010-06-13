(* By [Require Import] this module, the peano decicion procedure will
 * be activated in the Coq conversion relation. *)

Require Import Arith.

Load Theory peano .

Bind Theory peano As peano
  Sort    Binded By nat
  Symbols Binded By
    0    for zero ,
    S    for succ ,
    plus for plus

  Axioms Proved By
    plus_0_r,
    (fun x y => sym_eq (plus_n_Sm x y)) .
