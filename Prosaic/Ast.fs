namespace Ast
open System

type Formula = 
    | B of Boolean
    | Not of Formula
    | And of Formula * Formula
    | Or of Formula * Formula
    | Imp of Formula * Formula
    | Iff of Formula * Formula
    | ForAll of string * Formula
    | Exists of string * Formula
    | Atom of string

type prog = Prog of Formula list