(*
 *  [Require Import] this module to activate the embedding, in the Coq
 * conversion, of the decision procedures on natural numbers
 *)

Require Import Arith.

Load Theory nattheory.

Bind Theory nattheory As nattheory
  Sort    Binded By nat
  Symbols Binded By
    0    for zero ,
    S    for succ ,
    plus for plus

  Axioms Proved By
    plus_0_r,
    (fun x y => sym_eq (plus_n_Sm x y)).
