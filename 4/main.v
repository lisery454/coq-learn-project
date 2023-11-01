Inductive list (X: Type) :=
    | xnil
    | xcons (x: X) (l: list X).

Fixpoint app (X: Type)(l1 l2 : list X) : list X :=
    match l1 with
    | xnil _ => l2
    | xcons _ n l1' => xcons X n (app X l1' l2)
    end.

Arguments xnil {X}.

Arguments xcons {X}.

Arguments app {X}.

Notation "n :: m"  := (xcons n m)
    (at level 60, right associativity).

Notation "[]" := xnil.

Notation "[ x ; .. ; y ]" := 
    (xcons x .. (xcons y xnil) ..).

Notation "x ++ y" := (app x y) 
 (at level 60, right associativity).

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y): Y :=
    match l with
    | xnil => b
    | xcons h t => f h (fold f t b)
    end.

Definition fold1 {X : Type}(l : list X) : nat := 
    fold (fun _ n => S n) l 0.

Compute (fold1 [1;2;3;4;1]).

Definition fold2 {X : Type}(l : list (list X)) : list X := 
    fold app l [].

Compute (fold2 [[1;2;3;4];[5;6;7];[8;9]]).