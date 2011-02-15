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

(* -------------------------------------------------------------------- *)
let _dp_constr_of_topconstr = fun tc ->
  Constrintern.interp_constr Evd.empty (Global.env ()) tc

module DPTactics : sig
  val lazy_init : unit -> unit

  val prebinding :
       theory:string -> bname:string
    -> Topconstr.constr_expr
    -> (string * Topconstr.constr_expr) list
    -> Decproc.binding
end = struct
  open Safe_typing.DP.CoqLogicBinding

  let lazy_init = fun () ->
    if coq_logic () = None then begin
      register_coq_logic {
        cql_true  = Coqlib.build_coq_True  ();
        cql_false = Coqlib.build_coq_False ();
        cql_eq    = Coqlib.build_coq_eq    ();
        cql_not   = Coqlib.build_coq_not   ();
        cql_and   = Coqlib.build_coq_and   ();
        cql_conj  = Coqlib.build_coq_conj  ();
        cql_or    = Coqlib.build_coq_or    ();
        cql_ex    = Coqlib.build_coq_ex    ();
      }
    end

  (* ---------------------------------------------------------------- *)
  let prebinding = fun ~theory ~bname bsort symbols ->
    let theory =
      match Global.DP.find_theory theory with
      | None ->
          Util.error (Printf.sprintf "cannot find theory: %s" theory)
      | Some theory -> theory
    in
    let entry_of_topconstr = fun tc ->
      match Decproc.entry_of_constr (_dp_constr_of_topconstr tc) with
      | Some entry -> entry
      | None       ->
          Util.error
            "can only bind constant, constructor and inductive types"
    in
    let symbols =
      List.map
        (fun (x, c) -> (mkcname x, entry_of_topconstr c))
        symbols
    and bsort = entry_of_topconstr bsort
    and bname = Names.id_of_string bname
    in
      try
        mkbinding theory bname bsort symbols
      with
        | Decproc.InvalidBinding s ->
            let message = Printf.sprintf "Invalid binding: %s" s in
              Util.error message
end

(* -------------------------------------------------------------------- *)
type pid_ctr_map = string * Topconstr.constr_expr

type 'a pid_ctr_map_argtype =
    (pid_ctr_map, 'a) Genarg.abstract_argument_type

let
  (wit_pid_ctr_map     : Genarg.tlevel pid_ctr_map_argtype) ,
  (globwit_pid_ctr_map : Genarg.glevel pid_ctr_map_argtype) ,
  (rawwit_pid_ctr_map  : Genarg.rlevel pid_ctr_map_argtype) =
  Genarg.create_arg "r_pid_ctr_map"

let pr_pid_ctr_map = fun _ _ _ (x, c) ->
  (Ppconstr.pr_constr_expr c) ++ (str " for ") ++ (str x)

let pr_ne_pid_ctr_map =
  fun prc prlc prt xs ->
    Util.prlist_with_sep
      Util.pr_comma (pr_pid_ctr_map prc prlc prt) xs

let pr_nelist_constr =
  fun prc _prlc _prt xs ->
    Util.prlist_with_sep Util.pr_comma prc xs

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

ARGUMENT EXTEND nelist_constr
    TYPED AS constr list
    PRINTED BY pr_nelist_constr

| [ constr(x) "," nelist_constr(xs) ] -> [ x :: xs ]
| [ constr(x) ]                       -> [ [x] ]
END

VERNAC COMMAND EXTEND DecProcBind
| [ "Load" "Theory" preident(theory) ] -> [
    match Decproc.global_find_theory theory with
    | None -> Util.error (Printf.sprintf "theory not found: %s" theory)
    | Some theory -> Global.DP.add_theory theory
  ]

| [ "Bind" "Theory" preident(theory) "As" preident(bname)
      "Sort"    "Binded" "By" constr(bsort)
      "Symbols" "Binded" "By" nelist_pid_ctr_map(symbols)
      "Axioms"  "Proved" "By" nelist_constr(witnesses)
  ] -> [
    DPTactics.lazy_init ();

    let binding   = DPTactics.prebinding theory bname bsort symbols in
    let witnesses = List.map _dp_constr_of_topconstr witnesses in
      begin
        let nwitnesses = List.length witnesses
        and naxioms    = List.length binding.dpb_theory.dpi_axioms
        in
          if nwitnesses <> naxioms then
            Util.error
              (Printf.sprintf
                 "not the right numbers of axioms proofs (%d <> %d)"
                 (List.length witnesses) (List.length binding.dpb_theory.dpi_axioms))
      end;
      Global.DP.add_binding binding witnesses
  ]
END

VERNAC COMMAND EXTEND DecProdAxioms
| [ "DP" "Axioms" "For" "Theory" preident(theory)
      "Sort"    "Binded" "By" constr(bsort)
      "Symbols" "Binded" "By" nelist_pid_ctr_map(symbols)
  ] -> [
    DPTactics.lazy_init ();

    let binding = DPTactics.prebinding theory "none" bsort symbols in
    let axioms  =
      List.map
        (fun x ->
           Safe_typing.DP.Conversion.coqformula binding (FOTerm.formula_of_safe x))
        binding.dpb_theory.dpi_axioms
    in
    let output =
      match axioms with
        | [] -> str "no axioms for theory"
        | _  ->
            List.fold_left
              (fun output x ->
                 output ++ (Printer.pr_constr x) ++ (Pp.fnl ()))
              ((str "List of axioms for theory are:") ++ (Pp.fnl ()))
              axioms
    in
      msg output
  ]
END
