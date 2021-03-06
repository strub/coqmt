(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: Inclusion.v 13323 2010-07-24 15:57:30Z herbelin $ i*)

(** Author: Bruno Barras *)

Require Import Relation_Definitions.

Section WfInclusion.
  Variable A : Type.
  Variables R1 R2 : A -> A -> Prop.

  Lemma Acc_incl : inclusion A R1 R2 -> forall z:A, Acc R2 z -> Acc R1 z.
  Proof.
    induction 2.
    apply Acc_intro; auto with sets.
  Qed.

  Hint Resolve Acc_incl.

  Theorem wf_incl : inclusion A R1 R2 -> well_founded R2 -> well_founded R1.
  Proof.
    unfold well_founded in |- *; auto with sets.
  Qed.

End WfInclusion.
