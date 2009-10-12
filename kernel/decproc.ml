(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
(*i*)

(** {1 Identifiers} *)
type cname = CName of string

let _e_InvalidId = fun id ->
  Printf.sprintf "invalid identifier: [%s]" id
let _e_DuplicatedId = fun id ->
  Printf.sprintf "duplicated identifier: [%s]" id
let _e_MissingId = fun id ->
  Printf.sprintf "missing identifier: [%s]" id

let mkcname = fun name ->
  String.iter
    (fun c ->
       if c < 'a' || c > 'z' then
         raise (Invalid_argument (_e_InvalidId name)))
    name;
  CName name

let uncname = fun (CName x) -> x

module CNameMap =
  Map.Make(struct type t = cname let compare = compare end)
module CNameSet =
  Set.Make(struct type t = cname let compare = compare end)

(** {1 Variables} *)
type var_t = [ `Out of identifier | `In  of int | `Alien of int ]

module Var : Set.OrderedType with type t = var_t =
struct
  type t = var_t

  let compare =
    let _cc = function
      | `Out x          -> `Out (Names.string_of_id x)
      | (`In  _)   as v -> v
      | (`Alien _) as v -> v
    in
      fun v1 v2 -> compare (_cc v1) (_cc v2)
end

module Varset = Set.Make(Var)
module Varmap = Map.Make(Var)

(** {1 Decision procedures description - see interface documentation} *)
module FOTerm =
struct
  type status = FConstructor | FDefined

  (* Symbol description: name/arity/status *)
  type symbol = {
    s_name   : cname;
    s_arity  : int;
    s_status : status;
  }

  let mksymbol = fun name (arity, status) ->
    if arity < 0 then
      raise (Invalid_argument "[arity] must be non negative");
    { s_name = name; s_arity = arity; s_status = status; }

  type signature = symbol CNameMap.t

  exception DuplicatedSymbol of symbol * symbol

  let emptysig = CNameMap.empty

  let findsymbol = fun signature name ->
    try  Some (CNameMap.find name signature)
    with Not_found -> None

  let addsymbol = fun signature symbol ->
    match findsymbol signature symbol.s_name with
      | None ->
          CNameMap.add symbol.s_name symbol signature
      | Some osymbol ->
          raise (DuplicatedSymbol (osymbol, symbol))

  let mksig = fun symbols ->
    List.fold_left addsymbol emptysig symbols

  (* Concrete syntax for terms and formulas *)
  type term =
    | FVar  of var_t
    | FSymb of symbol * term list

  let rec string_of_term = function
    | FVar (`Out   x) -> Printf.sprintf "[%s]" (Names.string_of_id x)
    | FVar (`In    i) -> Printf.sprintf "#%d"  i
    | FVar (`Alien a) -> Printf.sprintf "~%d"  a
    | FSymb ({ s_name = CName f }, terms) ->
        let terms = List.map string_of_term terms in
          Printf.sprintf "|%s|(%s)" f (String.concat ", " terms)

  type formula =
    | FTrue
    | FFalse
    | FNeg   of formula
    | FAnd   of formula * formula
    | FOr    of formula * formula
    | FImply of formula * formula
    | FAll   of cname list * formula
    | FExist of cname list * formula

  (* Safe formulas, i.e. formulas where terms respect signature *)
  type safe_formula = {
    sf_formula   : formula;
    sf_signature : signature;
  }

  let formula_of_safe   = fun { sf_formula   = formula   } -> formula
  let signature_of_safe = fun { sf_signature = signature } -> signature

  type safe_formula_error =
    [ `UnknownSymbol   of string
    | `NWAppliedSymbol of string
    ]

  exception InvalidFormula of formula * safe_formula_error

  let formula_to_safe = fun signature formula ->
    (* FIXME *)
    { sf_formula = formula; sf_signature = signature; }

  (* Parsing functions *)
  exception ParseError of string

  let ofstring = fun _sformula -> FTrue
end

open FOTerm

type blackbox_t = term * term -> bool

type dpinfos = {
  dpi_name     : cname;
  dpi_sort     : cname;
  dpi_symbols  : FOTerm.signature;
  dpi_axioms   : FOTerm.safe_formula list;
  dpi_blackbox : blackbox_t;
}

let _e_MismatchSignature =
  "Formulas signature do not correspond to given signature"

let mkdpinfos = fun ~name ~sort signature formulas blackbox ->
  let formulas =
    match formulas with
      | `Checked formulas ->
          let pred = fun x -> x.sf_signature ==(*φ*) signature in
            if not (List.for_all pred formulas) then
              raise (Invalid_argument _e_MismatchSignature);
            formulas

      | `Unchecked formulas ->
          List.map (FOTerm.formula_to_safe signature) formulas
  in
    { dpi_name     = name      ;
      dpi_sort     = sort      ;
      dpi_symbols  = signature ;
      dpi_axioms   = formulas  ;
      dpi_blackbox = blackbox  ;
    }

module Presburger : sig
  val blackbox : (term * term) -> bool
end
=
struct
  open Num

  let zero   = num_of_int   0
  let one    = num_of_int   1
  let negone = num_of_int (-1)

  let blackbox = fun ((t1, t2) : term * term) ->
    let rec augment = fun preop (values, ctt) term ->
      match term with
      | FVar x ->
          let xvalue =
            try  Varmap.find x values
            with Not_found -> zero
          in
            (Varmap.add x (xvalue +/ (preop one)) values, ctt)
      | FSymb ({ s_name = CName "zero" }, []) -> (values, ctt)
      | FSymb ({ s_name = CName "succ" }, [t]) ->
          augment preop (values, ctt +/ (preop one)) t
      | FSymb ({ s_name = CName "plus" }, [t1; t2]) ->
          augment preop (augment preop (values, ctt) t1) t2
      | _ -> assert false
    in
    let (values, ctt) =
      augment
        (fun x -> minus_num x)
        (augment
           (fun x -> x)
           (Varmap.empty, zero)
           t1)
        t2
    in let nvars =
        Varmap.fold (fun _ _ x -> x+1) values 0

    in let solve = fun step ->
      let pb =
        Array.init (nvars+1)
          (fun i ->
             if   i = 0
             then Array.of_list (Varmap.fold (fun _ v acc -> v :: acc) values [])
             else Array.init nvars (fun j -> if (i-1) = j then one else zero))
      and bounds =
          Array.init (nvars+1)
            (fun i ->
               if   i = 0
               then (match step with
                       | `Left  -> (ctt +/ one, `Ge)
                       | `Right -> (ctt -/ one, `Le))
               else (zero, `Ge))
      in let simplex = 
          Simplex.Simplex.simplex_N pb bounds
      in
        Simplex.Simplex.solve_N simplex
    in
      match solve `Left with
      | None   -> (solve `Right) = None
      | Some _ -> false
end

let presburger =
  let name      = mkcname "presburger"
  and sort      = mkcname "nat"
  and sb_0      = mksymbol (mkcname "zero") (0, FConstructor)
  and sb_S      = mksymbol (mkcname "succ") (1, FConstructor)
  and sb_P      = mksymbol (mkcname "plus") (2, FDefined) in
  let signature = mksig [sb_0; sb_S; sb_P]
  in
    mkdpinfos ~name ~sort signature (`Checked []) Presburger.blackbox

(** {1 Theory binding - see interface documentation} *)
type entry =
  | DPE_Constructor of constructor
  | DPE_Constant    of constant
  | DPE_Inductive   of inductive

module EntryMap =
  Map.Make (struct type t = entry let compare = compare end)

type binding = {
  dpb_theory   : dpinfos;
  dpb_name     : identifier;
  dpb_bsort    : entry;
  dpb_bsymbols : (symbol * entry) list;
}

exception InvalidBinding of string

let mkbinding = fun theory name bsort bsymbols ->
  (* Collect symbols and check for duplicated/invalid ones *)
  let symbols =
    (List.fold_left
       (fun names ((CName id) as name, _) ->
          if CNameSet.mem name names then
            raise (InvalidBinding (_e_DuplicatedId id));
          if not (CNameMap.mem name theory.dpi_symbols) then
            raise (InvalidBinding (_e_InvalidId id));
          CNameSet.add name names)
       CNameSet.empty bsymbols);
  in
    (* Check for missing symbols *)
    CNameMap.iter
      (fun _ ({ s_name = ((CName id) as symbol) }) ->
         if not (CNameSet.mem symbol symbols) then
           raise (InvalidBinding (_e_MissingId id)))
      theory.dpi_symbols;
    (* Create structure *)
    { dpb_theory   = theory;
      dpb_name     = name;
      dpb_bsort    = bsort;
      dpb_bsymbols =
        List.map
          (fun (name, entry) ->
             (CNameMap.find name theory.dpi_symbols, entry))
          bsymbols;
    }

module Bindings =
struct
  open Term

  let _e_DuplicatedBindingName = fun name ->
    let name = Names.string_of_id name in
      Printf.sprintf "duplicated binding name: [%s]" name

  type revbinding =
    | RV_Symbol of binding * symbol
    | RV_Sort   of binding

  type t = {
    bds_bindings : binding list;
    bds_revmap   : revbinding EntryMap.t;
  }

  let empty = {
    bds_bindings = [];
    bds_revmap   = EntryMap.empty;
  }

  let all = fun (bds : t) -> bds.bds_bindings

  let find = fun (bds : t) (name : identifier) ->
    try  Some (List.find (fun bd -> bd.dpb_name = name) bds.bds_bindings)
    with Not_found -> None

  let add = fun (bds : t) (binding : binding) ->
    let name   = binding.dpb_name
    and revmap = bds.bds_revmap in
      (* Sanity check *)
      if find bds name <> None then
        raise (InvalidBinding (_e_DuplicatedBindingName name));
      if EntryMap.mem binding.dpb_bsort revmap then
        raise (InvalidBinding "multiple bindings");
      List.iter
        (fun (_, entry) ->
           if EntryMap.mem entry revmap then
             raise (InvalidBinding "multiple bindings"))
        binding.dpb_bsymbols;
      (* Add binding, complete revmap *)
      { bds_bindings = binding :: bds.bds_bindings;
        bds_revmap   =
          List.fold_left
            (fun revmap (symbol, entry) ->
               EntryMap.add entry (RV_Symbol (binding, symbol)) revmap)
            (EntryMap.add binding.dpb_bsort (RV_Sort binding) revmap)
            binding.dpb_bsymbols;
      }

  let revbinding = fun bds entry ->
    try  Some (EntryMap.find entry bds.bds_revmap)
    with Not_found -> None

  let revbinding_symbol = fun bds entry ->
    match revbinding bds entry with
    | Some (RV_Symbol (bd, symb)) -> Some (bd, symb)
    | _                           -> None

  let revbinding_sort = fun bds entry ->
    match revbinding bds entry with
    | Some (RV_Sort x) -> Some x
    | _                 -> None
end
