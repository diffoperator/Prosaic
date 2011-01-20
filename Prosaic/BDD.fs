module BDD

open Formula
open Ast

open System.Collections.Generic

let memoize f =
    let tab = new Dictionary<_,_>()
    fun x -> if tab.ContainsKey(x) then tab.[x]
             else let res = f x in tab.[x] <- res; res

type BddIndex = int
type Bdd = Bdd of BddIndex

type BddNode = Node of Formula * BddIndex * BddIndex

type BddBuilder(order : Formula -> Formula -> int) =
    let uniqueTab = new Dictionary<BddNode, BddIndex> ()
    let nodeTab = new Dictionary<BddIndex, BddNode> ()

    let mutable nextIdx = 2
    let trueIdx = 1
    let falseIdx = -1

    let trueNode = Node(Formula.B true, trueIdx, trueIdx)
    let falseNode = Node(Formula.B false, falseIdx, falseIdx)

    let idxToNode(idx) =
        if idx = trueIdx then trueNode
        elif idx = falseIdx then falseNode
        elif idx > 0 then nodeTab.[idx]
        else 
            let (Node (v, l, r)) = nodeTab.[-idx]
            Node(v, -l, -r)

    let nodeToUniqueIdx(node) =
        if uniqueTab.ContainsKey(node) then uniqueTab.[node]
        else
            let idx = nextIdx
            uniqueTab.[node] <- idx
            nodeTab.[idx] <- node
            nextIdx <- nextIdx + 1
            idx

    let mkNode(v:Formula, l:BddIndex, r:BddIndex) =
        if l = r then l
        elif l >= 0 then nodeToUniqueIdx(Node(v, l, r) )
        else -nodeToUniqueIdx(Node(v, -l, -r))
    
    let rec mkAnd (m1,m2) =
        if (m1 = falseIdx || m2 = falseIdx) then falseIdx
        elif m1 = trueIdx then m2 elif m2 = trueIdx then m1
        else
            let (BddNode.Node (x, l1, r1)) = idxToNode (m1)
            let (BddNode.Node (y, l2, r2)) = idxToNode (m2)
            
            let v, (la,lb), (ra,rb) = match order x y with
                                      | c when c = 0 -> x, (l1, l2), (r1, r2)
                                      | c when c < 0 -> x, (l1, m2), (r1, m2)
                                      | c -> y, (m1, l2), (m1, r2)
            mkNode (v, mkAnd(la,lb), mkAnd(ra,rb))

    let mkAnd = memoize mkAnd

    member g.False = Bdd falseIdx
    member g.True = Bdd trueIdx
    member g.And(Bdd m1,Bdd m2) = Bdd(mkAnd(m1,m2))
    member g.Or (Bdd m1, Bdd m2) = Bdd(-mkAnd(-m1,-m2))
    member g.Implies (Bdd m1, Bdd m2) = (g.Or (Bdd -m1, Bdd m2))
    member g.Iff (Bdd m1, Bdd m2) = g.Or (g.And (Bdd -m1, Bdd -m2), g.And (Bdd m1, Bdd m2))
    member g.Not(Bdd m) = Bdd(-m)
    member g.Atom(nm) = Bdd(mkNode(nm,trueIdx,falseIdx))
    member g.NodeCount = nextIdx

    member g.Build f = match f with
                       | And (lform, rform) -> g.And (g.Build lform, g.Build rform)
                       | Or (lform, rform) -> g.Or (g.Build lform, g.Build rform)
                       | Imp (lform, rform) -> g.Or (g.Build lform, g.Build rform)
                       | Iff (lform, rform) -> g.Iff (g.Build lform, g.Build rform)
                       | Atom p -> g.Atom(Formula.Atom p)
                       | Not f -> g.Not (g.Build f)
                       | B b -> if b = false then g.False else g.True
                       | Exists (v,p) -> failwith "Exists node"

    member g.ToString(Bdd idx) =
        let rec fmt depth idx =
            if depth > 5 then "..." 
            else
                let (Node(p,l,r)) = idxToNode(idx)
                match p with
                | Formula.Atom atom -> let lhs = fmt (depth+1) l;
                                       let rhs = fmt (depth+1) r;
                                       "[" + atom + " => " + lhs + " | " + rhs + "]"   
                | _ ->  if l = trueIdx then "T" else "F"    
        fmt 1 idx

    member g.Equivalent form1 form2 =
        g.Build form1 = g.Build form2