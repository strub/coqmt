(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: coqide.mli 13323 2010-07-24 15:57:30Z herbelin $ i*)

(* The CoqIde main module. The following function [start] will parse the
   command line, initialize the load path, load the input
   state, load the files given on the command line, load the ressource file,
   produce the output state if any, and finally will launch the interface. *)

val start : unit -> unit
