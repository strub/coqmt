(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_extend.cmo pa_extprint.cmo" i*)

(*i*)
open Names
open Decproc
open Decproc.FOTerm
(*i*)

(* -------------------------------------------------------------------- *)
module Parsing =
struct
  (* ------------------------------------------------------------------ *)
  exception ParseError of Ploc.t * exn

  (* ------------------------------------------------------------------ *)
  let grammar = Grammar.gcreate (Plexer.gmake ())
  
  let term      = Grammar.Entry.create grammar "foterm"
  and formula   = Grammar.Entry.create grammar "foformula"
  and formula_e = Grammar.Entry.create grammar "foformula_e"
  
  let pr_term    = Eprinter.make "foterm"
  and pr_formula = Eprinter.make "foformula"
  
  (* ------------------------------------------------------------------ *)
  EXTEND
  term:
  [ [ x = LIDENT -> FVar (mkcname x)
    | "@"; f = LIDENT -> FSymb (mkcname f, [])
    | "@"; f = LIDENT; "("; ts = LIST1 term SEP ","; ")" -> FSymb (mkcname f, ts)
    ]
  ]; END
  
  EXTEND
  formula:
  [
    [ "forall"; xs = LIST1 LIDENT; ","; phi = SELF
        -> FAll (List.map mkcname xs, phi)
  
    | "exists"; xs = LIST1 LIDENT; ","; phi = SELF
        -> FExist (List.map mkcname xs, phi)
    ]
  
  | RIGHTA
    [ left = SELF; "->"; right = SELF -> FImply (left, right) ]
  
  | LEFTA
    [ left = SELF; "||"; right = SELF -> FOr  (left, right) ]
  
  | LEFTA
    [ left = SELF; "&&"; right = SELF -> FAnd (left, right) ]
  
  | [ "not"; phi = SELF -> FNeg phi ]
  
  | [ "true"                          -> FTrue
    | "false"                         -> FFalse
    | left = term; "="; right = term  -> FEq (left, right)
    | left = term; "<>"; right = term -> FNeg (FEq (left, right))
    | "("; phi = SELF; ")"            -> phi
    ]
  ]; END
  
  EXTEND
  formula_e: [ [ phi = formula; EOI -> phi ] ];
  END
  
  (* ------------------------------------------------------------------ *)
  EXTEND_PRINTER
  pr_term:
  [ [ FVar x -> uncname x
    | FSymb (f, []) ->
        Printf.sprintf "@%s" (uncname f)
    | FSymb (f, ts) ->
        let args = String.concat ", " (List.map (curr pc) ts) in
          Printf.sprintf "@%s(%s)" (uncname f) args
    ]
  ]; END
  
  EXTEND_PRINTER
  pr_formula:
  [ [ FAll (xs, phi) ->
        Printf.sprintf "forall %s, %s"
          (String.concat " " (List.map uncname xs))
          (curr pc phi)
    | FExist (xs, phi) ->
        Printf.sprintf "exists %s, %s"
          (String.concat " " (List.map uncname xs))
          (curr pc phi)
    ]
  
  | [ FImply (left, right) ->
        Printf.sprintf "%s -> %s" (next pc left) (curr pc right) ]
  | [ FOr (left, right) ->
        Printf.sprintf "%s || %s" (curr pc left) (next pc right) ]
  | [ FAnd (left, right) ->
        Printf.sprintf "%s && %s" (curr pc left) (next pc right) ]
  
  | [ FNeg phi -> Printf.sprintf "not %s" (curr pc phi) ]
  
  | [ FTrue  -> "true"
    | FFalse -> "false"
    | FEq (left, right) ->
        Printf.sprintf "%s = %s"
          (Eprinter.apply pr_term pc left )
          (Eprinter.apply pr_term pc right)
    | phi -> Printf.sprintf "(%s)" (Eprinter.apply pr_formula pc phi)
    ]
  ]; END
  
  (* ------------------------------------------------------------------ *)
  let ofstring = fun input ->
    try  Grammar.Entry.parse formula_e (Stream.of_string input);
    with Ploc.Exc (loc, e) -> raise (ParseError (loc, e))
  
  let tostring = fun formula ->
    Eprinter.apply pr_formula Pprintf.empty_pc formula
end


(* -------------------------------------------------------------------- *)
module Peano : sig
  val blackbox : (exterm * exterm) -> bool
end
=
struct
  open Num

  exception InvalidProblem

  let zero   = num_of_int   0
  let one    = num_of_int   1
  let negone = num_of_int (-1)

  let blackbox = fun ((t1, t2) : exterm * exterm) ->
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
    let (coeffs, ctt) =
      augment
        (fun x -> minus_num x)
        (augment
           (fun x -> x)
           (Varmap.empty, zero)
           t1)
        t2
    in
      match ctt =/ zero with
      | false -> false
      | true  -> begin
          try
            Varmap.iter
              (fun _ value -> if value <>/ zero then raise InvalidProblem)
              coeffs;
            true
          with
          | InvalidProblem -> false
        end
end

(* -------------------------------------------------------------------- *)
let nattheory =
  let name      = mkcname "nattheory"
  and sort      = mkcname "nat"
  and sb_0      = mksymbol (mkcname "zero") (0, FConstructor)
  and sb_S      = mksymbol (mkcname "succ") (1, FConstructor)
  and sb_P      = mksymbol (mkcname "plus") (2, FDefined)
  and axioms    = [ "forall x  , @plus(x, @zero)    = x"                     ;
                    "forall x y, @plus(x, @succ(y)) = @succ(@plus(x, y))"    ]
  in
    mkdpinfos ~name ~sort
      (mksig [sb_0; sb_S; sb_P])
      (`Unchecked (List.map Parsing.ofstring axioms))
      Peano.blackbox

(* -------------------------------------------------------------------- *)
let init_dp = fun () ->
  Decproc.global_register_theory nattheory
