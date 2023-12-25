Require Import Arith.

Fixpoint cubic_root_helper(n x: nat): nat :=
    match x with
    | 0 => 0
    | S x' =>  
        let i := n - x in
        let i3 := i * i * i in
        if i3 =? n then i
        else if n <=? i3 then 0
        else cubic_root_helper n x'
    end.
      
Definition cubic_root (n: nat): nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | _ => cubic_root_helper n (n-1)
    end.

Compute(cubic_root 8).

