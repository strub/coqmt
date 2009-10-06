(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Pp
open Pcoq
open Genarg
open Term
open Decproc

type pid_ctr_map = string * Topconstr.constr_expr

type 'a pid_ctr_map_argtype =
    (pid_ctr_map, 'a) Genarg.abstract_argument_type

let constr_of_topconstr = fun tc ->
  Constrintern.interp_constr Evd.empty (Global.env ()) tc

let
  (wit_pid_ctr_map     : Genarg.tlevel pid_ctr_map_argtype) ,
  (globwit_pid_ctr_map : Genarg.glevel pid_ctr_map_argtype) ,
  (rawwit_pid_ctr_map  : Genarg.rlevel pid_ctr_map_argtype) =
  Genarg.create_arg "r_pid_ctr_map"

let pr_pid_ctr_map = fun _ _ _ (x, c) ->
  (Ppconstr.pr_constr_expr c) ++ (str "for") ++ (str x)

let pr_ne_pid_ctr_map = fun prc prlc prt xs ->
  Util.prlist (pr_pid_ctr_map prc prlc prt) xs

ARGUMENT EXTEND pid_ctr_map
    TYPED AS pid_ctr_map
    PRINTED BY pr_pid_ctr_map
  | [ constr(c) "for" preident(x) ] -> [ (x, c) ]
END

ARGUMENT EXTEND nelist_pid_ctr_map
    TYPED AS   pid_ctr_map list
    PRINTED BY pr_ne_pid_ctr_map

| [ pid_ctr_map(x) "," nelist_pid_ctr_map(l) ] -> [ x :: l ]
| [ pid_ctr_map(x) ]                           -> [ [x] ]
END

VERNAC COMMAND EXTEND DecProcBind
| [ "Bind" "Presburger" "As" preident(name)
      "Sort"    "Binded" "By" constr(bsort)
      "Symbols" "Binded" "By" nelist_pid_ctr_map(symbols)
  ] -> [
    let entry_of_topconstr = fun tc ->
      match kind_of_term (constr_of_topconstr tc) with
      | Const     const       -> DPE_Constant    const
      | Construct constructor -> DPE_Constructor constructor
      | Ind       inductive   -> DPE_Inductive   inductive
      | _                     -> failwith "invalid symbol" (* FIXME *)
    in
    let symbols =
      List.map
        (fun (x, c) -> (mkcname x, entry_of_topconstr c))
        symbols
    and bsort = entry_of_topconstr bsort
    and name  = Names.id_of_string name
    in
    let binding = mkbinding presburger name bsort symbols in
      Global.DP.add_binding binding 
  ]

| [ "Print" "Presburger" "Bindings" ] -> [
    List.iter
      (fun binding ->
         Printf.printf "%s\n%!" (Names.string_of_id binding.dpb_name))
      (Bindings.all (Global.DP.bindings ()))
  ]
END
