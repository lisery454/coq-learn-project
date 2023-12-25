Inductive boollist : Type :=
| bnil
| bcons (b: bool)(l: boollist).

Inductive binary_tree : Type :=
 | tnil
 | one_child (n : nat) (t : binary_tree)
 | two_children (n : nat) (t1 : binary_tree)
   (t2 : binary_tree).

Check (two_children 1 (one_child 2 tnil) 
       (one_child 3 tnil)).

Inductive bitree : Type :=
 | treenil
 | tchildren (n : nat) (t1 : bitree)
   (t2 : bitree).

Definition mytree := (tchildren 1 (tchildren 2 treenil treenil)
       (tchildren 3 treenil treenil)).

Fixpoint tree_sum (tree : bitree) : nat :=
 match tree with
 | treenil => 0
 | tchildren n l r => n + (tree_sum l) + (tree_sum r)
 end.

Compute (tree_sum mytree).

Inductive list (X : Type) :=
 | xnil
 | xcons (x : X) (l : list X).

Check xnil.
Check xcons.
Definition mylist := xcons nat 1 (xnil nat).
Check mylist.
Definition mylist2 := xcons bool true (xcons bool false (xnil bool)).
Check mylist2.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
 match count with
 | 0 => xnil X
 | S count' => xcons X x (repeat X x count')
 end.

Compute (repeat nat 3 5).

Fixpoint app (X : Type) (l1 l2 : list X) : list X :=
 match l1 with
 | xnil _ => l2
 | xcons _ x l1' => xcons X x (app X l1' l2)
 end.



Arguments xnil {X}.
Arguments xcons {X}.
Arguments repeat {X}.
Arguments app {X}.

Definition mylist3 := app (repeat 1 3) (repeat 2 4).

Compute mylist3.
Compute app (repeat true 2) (repeat false 3).

Fixpoint app' {X : Type} (l1 l2 : list X) : list X :=
 match l1 with
 | xnil  => l2
 | xcons x l1' => xcons x (app' l1' l2)
 end.

Notation "x :: l" := (xcons x l)(at level 60, right associativity).
Notation "[ ]" := xnil.
Notation "[ x ; .. ; y ]" := (xcons x .. (xcons y xnil) .. ). 

Check [1;2;3;4].
Check [true; false; true].
Definition list1 := [[1;2;3]; [4;5;6]; [7;8;9;0]].
Definition list2 := [[10;11;12]; [13;14;15]].

Compute app' list1 list2.
Compute repeat list1 3.

Definition twice {X : Type} (f : X -> X)(n : X) : X :=
 f (f n).

Check twice .

Definition plus3 := plus 3.
Compute twice plus3 5.
Compute twice S 5.

Fixpoint filter {X : Type}(test : X -> bool)(l : list X) 
  : list X :=
 match l with
 | xnil => xnil
 | h :: t => if test h then h :: (filter test t)
                       else filter test t
 end.

Fixpoint oddb (n : nat) : bool :=
 match n with
 | 0 => false
 | 1 => true
 | S (S n') => oddb n'
 end.

Compute oddb 4.

Compute filter oddb [1;2;3;4;5;6].

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y
:= 
match l with
 | [] => [ ]
 | h :: t => (f h) :: (map f t)
end.

Compute map (twice S) [1;2;3;4].
 


