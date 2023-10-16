Definition twice (X: Type) (f: X -> X)(n : X): X :=
    f (f n).

Arguments twice {X}.

Compute (twice (Nat.add 3) 5).

(* Fixpoint filter (X: Type) (condition : X -> bool)(l: list X) : list X:=
    match l with
    | xnil => xnil
    | xcons n l' => if condition n then n :: (filter condition l') 
                                else  (filter condition l') 
    end. *)