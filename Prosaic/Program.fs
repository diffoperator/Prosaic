// This project type requires the F# PowerPack at http://fsharppowerpack.codeplex.com/releases
// Learn more about F# at http://fsharp.net
// Original project template by Jomo Fisher based on work of Brian McNamara, Don Syme and Matt Valerio
// This posting is provided "AS IS" with no warranties, and confers no rights.

open System
open Microsoft.FSharp.Text.Lexing

open Ast
open Lexer
open Parser

let parseText text =
    let lexbuf = Lexing.LexBuffer<char>.FromString text
    try
        Parser.start Lexer.token lexbuf
    with e ->
        let pos = lexbuf.EndPos 
        failwithf "Error near line %d, character %d\n" pos.Line pos.Column

let f x = Boolean.Parse(x)
let a = parseText "p <=> q"
let pierceslaw = "(((p => q) => q) => p)"
let formula = match a with 
              | Prog p -> p |> List.head
let sim = Formula.ConvertToNNF formula
(Formula.GetTruthTable formula) |> Seq.iter (fun e -> Console.WriteLine(e.ToString()))
//let dual = Formula.MakeDual formula         

Console.WriteLine (a.ToString())