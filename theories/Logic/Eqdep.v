(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: Eqdep.v 13332 2010-07-26 22:12:43Z msozeau $ i*)

(** This file axiomatizes the invariance by substitution of reflexive
    equality proofs [[Streicher93]] and exports its consequences, such
    as the injectivity of the projection of the dependent pair.

    [[Streicher93]] T. Streicher, Semantical Investigations into
    Intensional Type Theory, Habilitationsschrift, LMU München, 1993.
*)

Require Export EqdepFacts.

Module Eq_rect_eq.

Axiom eq_rect_eq :
  forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.

End Eq_rect_eq.

Module EqdepTheory := EqdepTheory(Eq_rect_eq).
Export EqdepTheory.

(** Exported hints *)

Hint Resolve eq_dep_eq: eqdep v62.
Hint Resolve inj_pair2 inj_pairT2: eqdep.
