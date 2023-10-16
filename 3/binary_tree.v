Inductive bindary_tree : Type :=
    | nil
    | one_child (n : nat) (t : bindary_tree)
    | two_child (n : nat) (t1 : bindary_tree) (t2 : bindary_tree).

Check (two_child 1 nil (one_child 2 nil)).

Inductive bitree : Type :=
    | treenil
    | bind (n : nat) (t1 : bitree) (t2 : bitree).

Check (bind 1 treenil (bind 2 treenil treenil)).

Fixpoint sum(t: bitree) :nat :=
    match t with
    | treenil => 0
    | bind n t1 t2 => n + (sum t1) + (sum t2)
    end.

Compute (sum (bind 1 treenil (bind 2 treenil treenil))).