(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(****************************************************************************)
(*                                                                          *)
(*                         Naive Set Theory in Coq                          *)
(*                                                                          *)
(*                     INRIA                        INRIA                   *)
(*              Rocquencourt                        Sophia-Antipolis        *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*				 Gerard Huet				    *)
(*									    *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work was started in July 1993 by F. Prost. Thanks  *)
(* to the Newton Institute for providing an exceptional work environment    *)
(* in Summer 1995. Several developments by E. Ledinot were an inspiration.  *)
(****************************************************************************)

(*i $Id: Finite_sets.v 13323 2010-07-24 15:57:30Z herbelin $ i*)

Require Import Ensembles.

Section Ensembles_finis.
  Variable U : Type.

  Inductive Finite : Ensemble U -> Prop :=
    | Empty_is_finite : Finite (Empty_set U)
    | Union_is_finite :
      forall A:Ensemble U,
        Finite A -> forall x:U, ~ In U A x -> Finite (Add U A x).

  Inductive cardinal : Ensemble U -> nat -> Prop :=
    | card_empty : cardinal (Empty_set U) 0
    | card_add :
      forall (A:Ensemble U) (n:nat),
        cardinal A n -> forall x:U, ~ In U A x -> cardinal (Add U A x) (S n).

End Ensembles_finis.

Hint Resolve Empty_is_finite Union_is_finite: sets v62.
Hint Resolve card_empty card_add: sets v62.

Require Import Constructive_sets.

Section Ensembles_finis_facts.
  Variable U : Type.

  Lemma cardinal_invert :
    forall (X:Ensemble U) (p:nat),
      cardinal U X p ->
      match p with
	| O => X = Empty_set U
	| S n =>
          exists A : _,
            (exists x : _, X = Add U A x /\ ~ In U A x /\ cardinal U A n)
      end.
  Proof.
    induction 1; simpl in |- *; auto.
    exists A; exists x; auto.
  Qed.

  Lemma cardinal_elim :
    forall (X:Ensemble U) (p:nat),
      cardinal U X p ->
      match p with
	| O => X = Empty_set U
	| S n => Inhabited U X
      end.
  Proof.
    intros X p C; elim C; simpl in |- *; trivial with sets.
  Qed.

End Ensembles_finis_facts.
