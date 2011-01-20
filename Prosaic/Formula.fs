module Formula

open System
open System.Collections.Generic
open Ast
open Utils

let rec PrintFormula formula =
    match formula with
    | Not (form) -> Console.Write("(! "); PrintFormula form ; Console.Write(")")
    | And (lform, rform) -> Console.Write("(") ; PrintFormula lform ; Console.Write(" & ") ; PrintFormula rform ; Console.Write(")");
    | Or (lform, rform) -> Console.Write("(") ; PrintFormula lform ; Console.Write(" | ") ; PrintFormula rform ; Console.Write(")")
    | Imp (lform, rform) -> Console.Write("( ") ; PrintFormula lform ; Console.Write(" => ") ; PrintFormula rform ; Console.Write(")")
    | ForAll (str, form) -> Console.Write("(! ") ; PrintFormula form ; Console.Write(")")
    | Exists (str, form) -> Console.Write("(! ") ; PrintFormula form ; Console.Write(")")
    | Atom a -> Console.Write(a)

let rec MapFormula f formula = 
    match formula with
    | Not (form) -> Not (MapFormula f form)
    | And (lform, rform) -> And (MapFormula f lform, MapFormula f rform)
    | Or (lform, rform) -> Or (MapFormula f lform, MapFormula f rform)
    | Imp (prec, accd) -> Imp (MapFormula f prec, MapFormula f accd)
    | Iff (lform, rform) -> Iff (MapFormula f lform, MapFormula f rform)
    | ForAll (str, form) -> ForAll (str, MapFormula f form)
    | Exists (str, form) -> Exists (str, MapFormula f form)
    | Atom a -> f a
    | _ -> formula

let rec OverAtoms f formula b =
    match formula with
    | Atom (a) -> f a b
    | Not (p) -> OverAtoms f p b
    | And (p, q) | Or (p, q) | Imp (p, q) | Iff (p, q) -> OverAtoms f p (OverAtoms f q b)
    | ForAll (x, p) | Exists (x, p) -> OverAtoms f p b
    | _ -> b

//FIXME Need to remove duplicates
let rec GetAtoms formula =
    match formula with
    | Atom (a) -> [a] |> Seq.ofList
    | Not (a) -> GetAtoms a
    | And (l, r) | Or (l, r) | Imp (l, r) | Iff (l, r) -> 
        (GetAtoms l) |> Seq.append (GetAtoms r)
    | ForAll (str, form) | Exists (str, form) -> GetAtoms form
    | _ -> [] |> Seq.ofList

let rec EvalFormula f form =
    match form with
    | Not (form) -> not (EvalFormula f form)
    | And (lform, rform) ->(EvalFormula f lform) && (EvalFormula f rform)
    | Or (lform, rform) -> (EvalFormula f lform) || (EvalFormula f rform)
    | Imp (prec, accd) -> not((EvalFormula f prec) || (EvalFormula f accd))
    | Iff (lform, rform) -> (EvalFormula f lform) = (EvalFormula f rform)
    | B b -> b
    | Atom a -> f a

let rec Eval f (values: seq<string*bool>) form =
    match form with
    | Not (form) -> not (Eval f values form)
    | And (lform, rform) ->(Eval f values lform) && (Eval f values rform)
    | Or (lform, rform) -> (Eval f values lform) || (Eval f values rform)
    | Imp (prec, accd) -> (not(Eval f values prec)) || (Eval f values accd)
    | Iff (lform, rform) -> (Eval f values lform) = (Eval f values rform)
    | B b -> b
    | Atom a -> snd (values |> Seq.filter (fun e -> (fst e) = a) |> Seq.head)

//FIXME: Need to do the ugly ToString coz atoms returns a seq of chars (?)    
//FIXME: Really ugly, do something about it
let rec GetTruthTable formula =
    let atoms = (GetAtoms formula) |> Seq.distinct
    seq { 0 .. ((intPow 2 (atoms |> Seq.length))-1)} |> Seq.map (fun e -> Seq.zip atoms (generateTruthValues 
                                                                            (Seq.append 
                                                                                (List.rev ((convertToBinaryList e) |> List.ofSeq) |> List.toSeq) (Seq.initInfinite (fun e -> 0)))))
        |> Seq.map (fun e -> Eval (fun x -> Boolean.Parse(x)) e formula)

let rec IsTautology formula =
    if (GetTruthTable formula) |> Seq.exists (fun e -> false) then false else true

let rec IsSatisfiable formula =
    if (GetTruthTable formula) |> Seq.exists (fun e -> true) then true else false

let rec IsContradiction formula =
    not (IsTautology formula)

(*TODO
let TautologyWithCounter formula =
    (GetTruthTable formula) |> Seq.tryFind
    *)

let rec SubstAtomWithFormula form atom substForm =
     MapFormula (fun e -> if e = atom then 
                            substForm else (Formula.Atom  e)) form

let rec MakeDual form =
    match form with
    | B b -> Formula.B (not b)
    | Atom a -> form
    | Not f -> Not (MakeDual f)
    | And (lform, rform) -> Or (MakeDual lform, MakeDual rform)
    | Or (lform, rform) -> And (MakeDual lform, MakeDual rform)
    | _ -> failwithf "Formula contains connectives"

let rec ReduceFormula form =
    match form with
    | Not f -> match f with
               | B b -> Formula.B (not b)
    | Not (Not p) -> p
    | And (p, b) when (b = (Formula.B false)) -> Formula.B false
    | And (b, p) when (b = (Formula.B false)) -> Formula.B false
    | And (p, b) when (b = (Formula.B true)) -> p
    | And (b, p) when (b = (Formula.B true)) -> p
    | Or (p, b) when (b = (Formula.B false)) -> p
    | Or (b, p) when (b = (Formula.B false)) -> p
    | Or (p, b) when (b = (Formula.B true)) -> Formula.B true
    | Or (b, p) when (b = (Formula.B true)) -> Formula.B true
    | Imp (b, p) when (b = (Formula.B false)) -> Formula.B true
    | Imp (p, b) when (b = (Formula.B true)) -> Formula.B true
    | Imp (b, p) when (b = (Formula.B true)) -> p
    | Imp (p, b) when (b = (Formula.B false)) -> Formula.Not p
    | Iff (b, p) when (b = (Formula.B true)) -> p
    | Iff (p, b) when (b = (Formula.B true)) -> p
    | Iff (b, p) when (b = (Formula.B false)) -> Formula.Not p
    | Iff (p, b) when (b = (Formula.B false)) -> Formula.Not p
    | _ -> form

let rec Simplify form =
    match form with
    | Not p -> ReduceFormula (Formula.Not (Simplify p))
    | And (lform,rform) -> ReduceFormula (Formula.And (Simplify lform ,Simplify rform))
    | Or (lform,rform) -> ReduceFormula (Formula.Or (Simplify lform ,Simplify rform))
    | Imp (lform,rform) -> ReduceFormula (Formula.Imp (Simplify lform ,Simplify rform))
    | Iff (lform,rform) -> ReduceFormula (Formula.Iff (Simplify lform ,Simplify rform))
    | _ -> form

let IsPositive form =
    match form with
    | Not p -> false
    | _ -> true
   
let Negate form =
    match form with
    | Not p -> p
    | _ -> Formula.Not form

let Valuation form (values: seq<string*bool>) =
    Eval (fun x -> Boolean.Parse(x)) values form

// NNF -> A statement is said to be in a Negation Normal form if it can be constructed using
// only binary connectives AND, OR or reduces to T or F. ! is applied only to atomic formulas.
// Any statement can be converted to NNF (read pg 53, 54)
let rec ConvertToNNF form =
    match form with
    | And (lform, rform) -> And (ConvertToNNF lform,ConvertToNNF rform)
    | Or (lform, rform) -> Or (ConvertToNNF lform,ConvertToNNF rform)
    | Imp (lform ,rform) -> Or (ConvertToNNF (Formula.Not lform), ConvertToNNF rform)
    | Iff (lform ,rform) -> Or (And (ConvertToNNF lform, ConvertToNNF rform),
                                    And (ConvertToNNF (Not lform), ConvertToNNF (Not rform)))
    | Not (Not p) -> ConvertToNNF p
    | Not (And (lform ,rform)) -> Or (ConvertToNNF (Not lform), ConvertToNNF (Not rform))
    | Not (Or (lform, rform)) -> And(ConvertToNNF (Not lform), ConvertToNNF (Not rform))
    | Not (Imp (lform ,rform)) -> And (ConvertToNNF lform, ConvertToNNF (Not rform))
    | Not (Iff (lform ,rform)) -> Or (And (ConvertToNNF lform, ConvertToNNF (Not rform)),
                                        And (ConvertToNNF (Not lform), ConvertToNNF rform))
    | _ -> form;;

let MapToCNF (forms: Formula list) = 
    forms |> List.fold (fun acc e -> Formula.And (acc, e)) (Formula.B true)

let MapToDNF (forms: Formula list) =
    forms |> List.fold (fun acc e -> Formula.Or (acc, e)) (Formula.B false)

let MakeConjunctionIfSatValuation (forms: Formula list) v =
    forms |> List.fold (fun acc e -> if Valuation e v then 
                                        Formula.And (acc, e) 
                                     else 
                                        Formula.And (Formula.Not (e), acc)) (Formula.B true)

//TODO: Write a function that collects all the valuations that satisfy a formula
//Also read 2.6 completely




