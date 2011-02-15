(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: discharge.mli 13323 2010-07-24 15:57:30Z herbelin $ i*)

open Sign
open Cooking
open Declarations
open Entries

val process_inductive :
  named_context -> work_list -> mutual_inductive_body -> mutual_inductive_entry
