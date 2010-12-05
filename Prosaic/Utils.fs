module Utils

open Ast

let convertToBinaryList (n:int) = 
    System.Convert.ToString(n,2)
    |> Seq.map (fun c -> int c - int '0')

let generateTruthValues binList =
    binList |> Seq.map (fun e -> if e = 0 then true else false);;

let intPow num pow =
    [1 .. (pow-1)] |> List.fold (fun acc e -> acc * num) num

let getNthFormula prog n =
    match prog with
    | Prog p -> List.nth p n