Definition f := fun n => S n.

Compute f 3.

Check S.

Definition f' :=
    fix div3' (n: nat) :bool :=
    match n with
    | O => true
    | S O => false
    | S(S O) => false
    | S(S(S q)) => div3' q
    end.