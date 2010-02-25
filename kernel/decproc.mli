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

(** Our names, i.e. string matching [a-z]+. We use a private
  * constructor so that standard ocaml equality works. *)
type cname = private CName of string

val mkcname : string -> cname    (* Raise Invalid_argument on error *)
val uncname : cname  -> string

(** Variables canonical type, either
  * - a named variable (Named of Names.identifier), or
  * - a DeBruijn variable (DeBruijn of int), or
  * - an abstraction variable (Alien of int)
  *)
type var_t = [ `Named of identifier | `DeBruijn  of int | `Alien of int ]

module Var : Set.OrderedType with type t = var_t

module Varset : Set.S with type elt = var_t
module Varmap : Map.S with type key = var_t

(** Decision procedures description
  *
  * Each decision procedure comes as a plugin, which must register
  * to the DP engine using the [dp_register] function.
  *
  * This function take a [dpinfos] structure describing the theory
  * decided, i.e. 
  *   i) the name for the base sort of the theory,
  *  ii) the symbol functions along with their arities and their
  *      status (defined or constructor)
  * iii) the axioms of the theory (in a format described later)
  *  iv) the solver function
  *
  * Axioms of the theory are given using the following concrete syntax
  *   φ, ψ ::= true                 (true)
  *          | false                (false)
  *          | not φ                (negation)
  *          | t₁ = t₂              (equation)
  *          | φ₁ ? φ₂              (? \in { /\, \/, -> }, and/or/implies connectors)
  *          | forall x₁ ... xn , φ (universal quantication)
  *          | exists x₁ ... xn , φ (existential quantification)
  *
  * where t ::= x                (variable name, x ∈ [a-z]+)
  *           | \f(t₁,...,t_n)   (function symbol)
  *
  * Notations:
  *  - φ₁ <> φ₂ stands for \not (φ₁ = φ₂)
  *
  * For any pair of constructor symbols (c₁, c₂), the axiom
  *   forall x₁ ... xn y₁ ... yk, c₁(x₁,...,xn) <> c₂(y₁,...,yk)
  * is added at load time.
  *
  * For any constructor symbol c, the axioms (for i \in {1..n})
  *   forall x₁ ... xn y₁ ... yn, c(x₁,...,xn) = c(y₁,...,yn) -> xi = yi
  * are added at load time.
  *)
module FOTerm : sig
  type status = FConstructor | FDefined

  (* Symbol description: name/arity/status *)
  type symbol = private {
    s_name   : cname;
    s_arity  : int;
    s_status : status;
  }

  (* Create a new symbol, checking for constraints on identifier and
   * arity. Raise [Invalid_argument] on error.
   *)
  val mksymbol : cname -> (int * status) -> symbol

  (* Signature, i.e. set of symbols *)
  type signature

  exception DuplicatedSymbol of symbol * symbol

  val emptysig   : signature
  val mksig      : symbol list -> signature
  val addsymbol  : signature -> symbol -> signature
  val findsymbol : signature -> cname  -> symbol option

  (* Concrete syntax for terms and formulas. *)
  type ('var, 'symbol) term =
    | FVar  of 'var
    | FSymb of 'symbol * (('var, 'symbol) term) list

  type foterm = (cname, cname ) term
  type sfterm = (cname, symbol) term
  type exterm = (var_t, symbol) term

  val string_of_var_t : var_t -> string

  val string_of_term
    :  ppvar:('var    -> string)
    -> ppsmb:('symbol -> string)
    -> ('var, 'symbol) term
    -> string

  val string_of_foterm : foterm -> string
  val string_of_exterm : exterm -> string

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
  type safe_formula

  val formula_of_safe   : safe_formula -> sfformula
  val signature_of_safe : safe_formula -> signature

  type safe_formula_error =
    [ `SymbolNotInSig  of cname
    | `NWAppliedSymbol of symbol
    | `FreeVariable    of cname
    ]

  exception InvalidFormula of safe_formula_error

  val formula_to_safe : signature -> foformula -> safe_formula
end

(** Parsing of first-order formulas *)
module Parsing : sig
  exception ParseError of Ploc.t * exn

  val ofstring : string -> FOTerm.foformula
  val tostring : FOTerm.foformula -> string
end

type blackbox_t = FOTerm.exterm * FOTerm.exterm -> bool

type dpinfos = private {
  dpi_name     : cname;
  dpi_sort     : cname;
  dpi_symbols  : FOTerm.signature;
  dpi_axioms   : FOTerm.safe_formula list;
  dpi_blackbox : blackbox_t;
}

(** Create a [dpinfos] structure. If formulas are given as safe formulas,
    their signatures must be _physically_ equal to the given signature.
    Otherwise, formulas are checked w.r.t. the given signature.
   
    Raise:
     - [Invalid_argument] if a safe formula signature is invalid
     - [FOTerm.InvalidFormula] if an unsafe formula check failed *)
val mkdpinfos
  :  name:cname
  -> sort:cname
  -> FOTerm.signature
  -> [ `Checked   of FOTerm.safe_formula list
     | `Unchecked of FOTerm.foformula    list ]
  -> blackbox_t
  -> dpinfos

(** FO theory binding to Coq symbols. A binding is:
    - a name, only used for later referencing a Coq script,
    - a Coq symbol [N] of type [Type] for the sort [nat]
    - for each first order symbol (0, S, +), a corresponding Coq symbol
      of right type (e.g., for +, a symbol of type N -> N -> N).
    - a set of Coq proof terms, proving that given symbols respect the
      axioms of the theory (FIXME: TODO)

    Provided symbols can only be inductive types, constructors and
    constants. The type [entry] represent such symbols.

    [binding] type is private and can only be constructed from the
    soft constructor [mkbinding]. *)

type entry =
  | DPE_Constructor of constructor
  | DPE_Constant    of constant
  | DPE_Inductive   of inductive

type binding = private {
  dpb_theory   : dpinfos;
  dpb_name     : identifier;
  dpb_bsort    : entry;
  dpb_bsymbols : (FOTerm.symbol * entry) list;
}

exception InvalidBinding of string

(** mkbinding expect (in order)
  * - the decision procedures binded (See [dpinfos])
  * - the binding name
  * - the entry for the decision procedures sort binding
  * - the entries for the function symbol bindings *)
val mkbinding :
  dpinfos -> identifier -> entry -> (cname * entry) list -> binding

(** Bindings map *)
module Bindings : sig
  type t

  type revbinding =
    | RV_Symbol of binding * FOTerm.symbol
    | RV_Sort   of binding

  val empty    : t
  val all      : t -> binding list
  val add      : t -> binding -> t
  val find     : t -> identifier -> binding option

  val revbinding        : t -> entry -> revbinding option
  val revbinding_symbol : t -> entry -> (binding * FOTerm.symbol) option
  val revbinding_sort   : t -> entry -> binding option
end

(** Peano natural numbers + blackbox *)
val peano : dpinfos

(** Global theories registry *)
val global_find_theory : string -> dpinfos option
