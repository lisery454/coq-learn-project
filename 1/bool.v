Inductive bool : Type :=
    | true
    | false.

Definition and(b1: bool)(b2: bool): bool :=
    match b1 with
    | true => b2
    | false => false
    end.

Definition or(b1: bool)(b2: bool): bool :=
    match b1 with
    | true => true
    | false => b2
    end.  

Compute (or true false).


