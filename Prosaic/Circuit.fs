module Circuit

open Ast

open Formula
open BDD

type CFormula =
    { F : Formula }

    static member (&&&) (left: CFormula, right: CFormula) =
        {F = Formula.Simplify (Ast.And (left.F, right.F))}

    static member (|||) (left: CFormula, right: CFormula) =
        {F = Formula.Simplify (Ast.Or (left.F, right.F))}

    static member (^^^) (left: CFormula, right: CFormula) =
        {F = Formula.Simplify (Ast.Not (Ast.Or (Ast.And (left.F, right.F), Ast.And(Ast.Not left.F, Ast.Not right.F))))}

    static member (===) (left: CFormula, right: CFormula) =
        {F = Formula.Simplify (Ast.Iff (left.F, right.F))}

type Bit = 
    Bit of CFormula

type Bitvec = 
    BitVector of Bit[] 

let sumBit (x: CFormula) y = (x ^^^ y)
let carryBit x y = (x &&& y)

let halfAdder x y sum carry =
    (sum === (sumBit x y)) &&&
    (carry === carryBit x y)

let fullAdder x y z sum carry =
    let xy = (sumBit x y)
    (sum === sumBit xy z) &&&
    (carry === (carryBit x y ||| carryBit xy z))

let twoBitAdder (x1,x2) (y1,y2) (sum1,sum2) carryInner carry =
    halfAdder x1 y1 sum1 carryInner &&&
    fullAdder x2 y2 carryInner sum2 carry

let Lo : Bit = Bit ({F = Formula.B false})
let Hi : Bit = Bit ({F = Formula.B true})

let BitEq (b1: Bit) b2 = match b1, b2 with
                         | Bit F1, Bit F2 -> F1 === F2

let AndL l = 
    if l = [] then 
        {F = Formula.B false}
    else
        let h::t = l
        Seq.fold (fun acc e -> acc &&& e) h t
