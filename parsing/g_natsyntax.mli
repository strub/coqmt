(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: g_natsyntax.mli 13323 2010-07-24 15:57:30Z herbelin $ i*)

(* Nice syntax for naturals. *)

open Notation

val nat_of_int : Bigint.bigint prim_token_interpreter
