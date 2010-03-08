(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Initialization functions *)
val init_dp : unit -> unit

(** Peano blackbox *)
val peano : Decproc.dpinfos

(** Parsing of first-order formulas *)
module Parsing : sig
  open Decproc

  exception ParseError of Ploc.t * exn

  val ofstring : string -> FOTerm.foformula
  val tostring : FOTerm.foformula -> string
end
