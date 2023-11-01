Inductive list (X: Type) :=
    | xnil
    | xcons (x: X) (l: list X).

Definition mylist := xcons nat 1 (xnil nat).

Check mylist.

Check xnil.
Check xcons.

Fixpoint repeat(X: Type)(x: X) (count : nat): list X :=
    match count with
    | 0 => xnil X
    | S count' => xcons X x (repeat X x count')
    end.

Compute (repeat nat 3 5).

Fixpoint app (X: Type)(l1 l2 : list X) : list X :=
    match l1 with
    | xnil _ => l2
    | xcons _ n l1' => xcons X n (app X l1' l2)
    end.

Compute (app nat (repeat nat 3 1) (repeat nat 1 2)).

Arguments xnil {X}.

Arguments xcons {X}.

Arguments app {X}.

Arguments repeat {X}.

Definition mylist' := app (repeat 1 3) (repeat 2 4).

Check (repeat true 1).

Notation "n :: m"  := (xcons n m)
    (at level 60, right associativity).

Notation "[]" := xnil.

Notation "[ x ; .. ; y ]" := 
    (xcons x .. (xcons y xnil) ..).

Notation "x ++ y" := (app x y) 
 (at level 60, right associativity).


Definition hd (X: Type)(default : X)(l: list X) : X :=
    match l with
    | xnil => default
    | xcons n l' => n
    end.

Fixpoint tl (X: Type)(default : X)(l: list X) : X :=
    match l with
    | xnil => default
    | xcons n l' => tl X n l'
    end.

Fixpoint length (X: Type)(l: list X) : nat :=
    match l with
    | xnil => 0
    | xcons n l' => S(length X l')
    end.

Fixpoint rev (X: Type)(l: list X) : list X :=
    match l with 
    | xnil => xnil
    | xcons n l' => (rev X l') ++ [n]
    end.

Compute (hd nat 0 [1;2;3;4;5]).

Compute (tl nat 0 [1;2;3;4;5]).

Compute (length nat [1;2;3;4;5]).

Compute (rev nat [1;2;3;4;5]).

Inductive btree (X: Type) :=
    | xtnil
    | xbind (x: X)(t1 : btree X) (t2 : btree X).
    










