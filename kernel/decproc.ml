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
  Printf.sprintf "invalid id: [%s]" id
let _e_UnknownBoundSymbol = fun id ->
  Printf.sprintf "unknown bound symbol: [%s]" id
let _e_SymbolBoundTwice = fun id ->
  Printf.sprintf "symbol [%s] is bound at least twice" id
let _e_SymbolUnbound = fun id ->
  Printf.sprintf "symbol [%s] not bound" id

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
type var_t = [ `Named of identifier | `DeBruijn  of int | `Alien of int ]

module Var : Set.OrderedType with type t = var_t =
struct
  type t = var_t

  let compare =
    let _cc = function
      | `Named x            -> `Named (Names.string_of_id x)
      | (`DeBruijn  _) as v -> v
      | (`Alien _)     as v -> v
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
  type ('var, 'symbol) term =
    | FVar  of 'var
    | FSymb of 'symbol * (('var, 'symbol) term) list

  type foterm = (cname, cname ) term
  type sfterm = (cname, symbol) term
  type exterm = (var_t, symbol) term

  let string_of_var_t = function
    | `Named    x -> Printf.sprintf "[%s]" (Names.string_of_id x)
    | `DeBruijn i -> Printf.sprintf "#%d"  i
    | `Alien    a -> Printf.sprintf "~%d"  a

  let string_of_term =
    fun ~(ppvar : 'var -> string) ~(ppsmb : 'symbol -> string) ->
      let rec string_of_term = function
        | FVar x -> ppvar x
        | FSymb (f, terms) ->
            let terms = List.map string_of_term terms in
              Printf.sprintf "@%s(%s)" (ppsmb f) (String.concat ", " terms)
      in
        fun (t : ('var, 'symbol) term) -> string_of_term t

  let string_of_foterm =
    string_of_term ~ppvar:uncname ~ppsmb:uncname

  let string_of_exterm =
    string_of_term
      ~ppvar:string_of_var_t
      ~ppsmb:(fun { s_name = CName x } -> x)

  type 'term formula =
    | FTrue
    | FFalse
    | FEq    of 'term * 'term
    | FNeg   of 'term formula
    | FAnd   of 'term formula * 'term formula
    | FOr    of 'term formula * 'term formula
    | FImply of 'term formula * 'term formula
    | FAll   of cname list * 'term formula
    | FExist of cname list * 'term formula

  type foformula = foterm formula
  type sfformula = sfterm formula

  (* Safe formulas, i.e. formulas where terms respect signature *)
  type safe_formula = {
    sf_formula   : sfformula;
    sf_signature : signature;
  }

  let formula_of_safe   = fun { sf_formula   = formula   } -> formula
  let signature_of_safe = fun { sf_signature = signature } -> signature

  type safe_formula_error =
    [ `SymbolNotInSig  of cname
    | `NWAppliedSymbol of symbol
    | `FreeVariable    of cname
    ]

  exception InvalidFormula of safe_formula_error

  let formula_to_safe = fun signature formula ->
    let rec checkterm = fun varbinds -> function
      | FVar x ->
          if   not (List.mem x varbinds)
          then raise (InvalidFormula (`FreeVariable x))
          else (FVar x)
      | FSymb (symbol, ts) -> begin
          match findsymbol signature symbol with
          | None        -> raise (InvalidFormula (`SymbolNotInSig symbol))
          | Some symbol ->
              if   List.length ts <> symbol.s_arity
              then raise (InvalidFormula (`NWAppliedSymbol symbol))
              else FSymb (symbol, List.map (checkterm varbinds) ts)
        end

    and checkformula = fun varbinds -> function
      | FTrue  -> FTrue
      | FFalse -> FFalse

      | FNeg phi             -> FNeg   (checkformula varbinds phi)
      | FEq    (left, right) -> FEq    (checkterm varbinds left, checkterm varbinds right)
      | FAnd   (left, right) -> FAnd   (checkformula varbinds left, checkformula varbinds right)
      | FOr    (left, right) -> FOr    (checkformula varbinds left, checkformula varbinds right)
      | FImply (left, right) -> FImply (checkformula varbinds left, checkformula varbinds right)

      | FAll   (vars, phi) -> FAll   (vars, checkformula (List.rev_append vars varbinds) phi)
      | FExist (vars, phi) -> FExist (vars, checkformula (List.rev_append vars varbinds) phi)

    in let formula = checkformula [] formula
    in
      { sf_formula = formula; sf_signature = signature; }
end

open FOTerm

type blackbox_t = exterm * exterm -> bool

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

(** {1 Theory binding - see interface documentation} *)
type entry =
  | DPE_Constructor of constructor
  | DPE_Constant    of constant
  | DPE_Inductive   of inductive

let entry_of_constr = fun c ->
  match Term.kind_of_term c with
  | Term.Const     const       -> Some (DPE_Constant    const)
  | Term.Construct constructor -> Some (DPE_Constructor constructor)
  | Term.Ind       inductive   -> Some (DPE_Inductive   inductive)
  | _                          -> None

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
            raise (InvalidBinding (_e_SymbolBoundTwice id));
          if not (CNameMap.mem name theory.dpi_symbols) then
            raise (InvalidBinding (_e_UnknownBoundSymbol id));
          CNameSet.add name names)
       CNameSet.empty bsymbols);
  in
    (* Check for missing symbols *)
    CNameMap.iter
      (fun _ ({ s_name = ((CName id) as symbol) }) ->
         if not (CNameSet.mem symbol symbols) then
           raise (InvalidBinding (_e_SymbolUnbound id)))
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

(** {1 Decproc opcodes} *)
module OpCodes =
struct
  type opbinding = {
    opb_theory   : cname;
    opb_name     : identifier;
    opb_bsort    : entry;
    opb_bsymbols : (cname * entry) list;
  }

  type opcode =
    | DP_Load of cname
    | DP_Bind of opbinding

  let of_binding = fun binding ->
    let opb_bsymbols =
      List.map (fun (x, y) -> (x.s_name, y)) binding.dpb_bsymbols
    in
      { opb_theory   = binding.dpb_theory.dpi_name;
        opb_name     = binding.dpb_name           ;
        opb_bsort    = binding.dpb_bsort          ;
        opb_bsymbols = opb_bsymbols               ; }
end

(** {1 Decproc registry } *)
let global_theories = ref []

let global_find_theory = fun name ->
  try
    Some
      (List.find
         (fun x -> uncname x.dpi_name = name)
         !global_theories)
  with
    | Not_found -> None

let global_register_theory = fun theory ->
  match global_find_theory (uncname theory.dpi_name) with
  | None   -> global_theories := theory :: !global_theories
  | Some _ -> failwith "duplicated theory in registry"
