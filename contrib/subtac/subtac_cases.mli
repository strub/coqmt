(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: subtac_cases.mli 10739 2008-04-01 14:45:20Z herbelin $ i*)

(*i*)
open Util
open Names
open Term
open Evd
open Environ
open Inductiveops
open Rawterm
open Evarutil
(*i*)

(*s Compilation of pattern-matching, subtac style. *)
module Cases_F(C : Coercion.S) : Cases.S
