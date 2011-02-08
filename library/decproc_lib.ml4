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
(* Stupid implementation of a polynom data structure                    *)
(* -------------------------------------------------------------------- *)
module Polynom : sig
  type 'a rpolynom = (('a * int) list * Num.num) list

  type 'a polynom

  val pzero     : unit    -> 'a polynom
  val pone      : unit    -> 'a polynom
  val pconstant : Num.num -> 'a polynom
  val pmonom    : 'a      -> 'a polynom

  val oflist : 'a rpolynom -> 'a polynom
  val tolist : 'a polynom  -> 'a rpolynom

  val getconstant : 'a polynom -> Num.num

  val add    : 'a polynom -> 'a polynom -> 'a polynom
  val sub    : 'a polynom -> 'a polynom -> 'a polynom
  val mul    : 'a polynom -> 'a polynom -> 'a polynom

  val pcompare : 'a polynom -> 'a polynom -> int
  val peq      : 'a polynom -> 'a polynom -> bool
end = struct
  open Num

  type 'a rpolynom = (('a * int) list * Num.num) list
  type 'a polynom  = 'a rpolynom

  let zero = num_of_int 0
  let one  = num_of_int 1

  let pcompare =
    (Pervasives.compare : 'a polynom -> 'a polynom -> int)

  let peq = fun p1 p2 -> (pcompare p1 p2) = 0

  let oflist = fun p ->
    let p = List.filter (fun x -> not (snd x =/ zero)) p in
    let p = List.sort (fun m1 m2 -> compare (fst m1) (fst m2)) p in
      p

  let tolist = fun (p : 'a polynom) -> (p : 'a rpolynom)

  let getconstant = fun (p : 'a polynom) ->
    match p with
    | []           -> zero
    | ([], c) :: _ -> c
    | _            -> assert false

  let pconstant = fun c  -> oflist [([], c)]
  let pzero     = fun () -> pconstant zero
  let pone      = fun () -> pconstant one
  let pmonom    = fun x  -> oflist [([x, 1], one)]

  let addsub = fun op ->
    let rec addsub = fun p1 p2 acc ->
      match p1, p2 with
      | p, [] | [], p -> List.rev_append acc p
      | (m1 as m, c1) :: p1', (m2, c2) :: p2' ->
        let cmp = compare m1 m2 in
          if cmp == 0 then begin
            let c = op c1 c2 in
              if   c =/ zero
              then addsub p1' p2' acc
              else addsub p1' p2' ((m, c) :: acc)
          end
          else if cmp < 0 then begin
            addsub p1' p2 ((m1, c1) :: acc)
          end else begin
            addsub p1 p2' ((m2, c2) :: acc)
          end
    in
      fun p1 p2 -> addsub p1 p2 []

  let add = fun p1 p2 -> addsub Num.add_num p1 p2
  let sub = fun p1 p2 -> addsub Num.sub_num p1 p2

  let mul =
    let rec mul = fun p1 p2 acc ->
      match p1 with
      | []       -> acc
      | m1 :: p1 -> mul p1 p2 (add [m1] acc)
    in
      fun p1 p2 -> mul p1 p2 []
end

(* -------------------------------------------------------------------- *)
(* Stupid implementation of the nat blackbox based on the studid        *)
(* implementation of polynoms.                                          *)
(* -------------------------------------------------------------------- *)
module NatBox : sig
  val blackbox : (exterm * exterm) -> bool
end
  =
struct
  open Num

  let blackbox = fun ((t1, t2) : exterm * exterm) ->
    let newvar =
      let hc, current = Hashtbl.create 13, ref (-1) in
        fun (c : string) ts ->
          try  Hashtbl.find hc (c, ts)
          with Not_found ->
            incr current;
            Hashtbl.add hc (c, ts) !current;
            !current

    in let rec augment = fun term ->
      match term with
        | FVar x ->
          Polynom.pmonom (`Out x)
        | FSymb ({ s_name = CName "zero" }, []) ->
          Polynom.pzero ()
        | FSymb ({ s_name = CName "succ" }, [t]) ->
          Polynom.add (Polynom.pone ()) (augment t)
        | FSymb ({ s_name = CName "plus" }, [t1; t2]) ->
          Polynom.add (augment t1) (augment t2)
        | FSymb ({ s_name = CName "mult" }, [t1; t2]) ->
          Polynom.mul (augment t1) (augment t2)
        | FSymb ({ s_name = CName x }, [t1; t2])
            when x = "min" || x = "max"
                   ->
          let ismin = if x = "min" then true else false in

          let (p1, p2) = augment t1, augment t2 in
          let c1 = Polynom.getconstant p1
          and c2 = Polynom.getconstant p2 in
          let c  = Num.min_num c1 c2 in
          let p1 = Polynom.sub p1 (Polynom.pconstant c1)
          and p2 = Polynom.sub p2 (Polynom.pconstant c2) in
          let p =
            if Polynom.peq p1 (Polynom.pzero ()) then
              (if ismin then p1 else p2)
            else if Polynom.peq p2 (Polynom.pzero ()) then
              (if ismin then p2 else p1)
            else if Polynom.peq p1 p2 then
              p1
            else
              Polynom.pmonom (`In (newvar x [p1; p2]))
          in
            Polynom.add p (Polynom.pconstant c)
        | _ -> assert false
       in
         Polynom.peq (augment t1) (augment t2)
end

(* -------------------------------------------------------------------- *)
let nattheory =
  let name      = mkcname "nattheory"
  and sort      = mkcname "nat"
  and sb_0      = mksymbol (mkcname "zero") (0, FConstructor)
  and sb_S      = mksymbol (mkcname "succ") (1, FConstructor)
  and sb_P      = mksymbol (mkcname "plus") (2, FDefined)
  and sb_T      = mksymbol (mkcname "time") (2, FDefined)
  and sb_min    = mksymbol (mkcname "min" ) (2, FDefined)
  and sb_max    = mksymbol (mkcname "max" ) (2, FDefined)
  and axioms    = [ "forall x  , @plus(x, @zero)    = x"                       ;
                    "forall x y, @plus(x, @succ(y)) = @succ(@plus(x, y))"      ;
                    "forall x  , @time(x, @zero)    = @zero"                   ;
                    "forall x y, @time(x, @succ(y)) = @plus(@time(x, y), x)"   ;
                    "forall x  , @min(x, @zero) = @zero"                       ;
                    "forall x  , @min(@zero, x) = @zero"                       ;
                    "forall x y, @min(@succ(x), @succ(y)) = @succ(@min(x, y))" ;
                    "forall x  , @max(x, @zero) = x"                           ;
                    "forall x  , @max(@zero, x) = x"                           ;
                    "forall x y, @max(@succ(x), @succ(y)) = @succ(@max(x, y))" ]
  in
    mkdpinfos ~name ~sort
      (mksig [sb_0; sb_S; sb_P; sb_T; sb_min; sb_max])
      (`Unchecked (List.map Parsing.ofstring axioms))
      NatBox.blackbox

(* -------------------------------------------------------------------- *)
let init_dp = fun () ->
  Decproc.global_register_theory nattheory
