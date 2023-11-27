Require Import Arith.
Require Import List.


Notation "n :: m"  := (cons n m)
    (at level 60, right associativity).


Notation "x ++ y" := (app x y) 
 (at level 60, right associativity).
Notation "[]" := nil.

Notation "[ x ; .. ; y ]" := 
    (cons x .. (cons y nil) ..).


Inductive btree : Type  :=
    | nil
    | bind (t1: btree)(t2: btree)(n: nat).


Fixpoint sum_bt (t: btree) :nat :=
    match t with
    | nil => 0
    | bind t1 t2 q => q + (sum_bt t1) + (sum_bt t2)
    end.


Theorem app_nil_r: forall {X: Type}, forall l:list X,
    l ++ [] = l .
Proof.

intros.

induction l.

- reflexivity.

- simpl. rewrite IHl. reflexivity. 

Qed.


Theorem app_assoc: forall A (l m n: list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.

intros.

induction l as [|s l IHl].

- reflexivity.

- simpl. rewrite IHl. reflexivity. 
    
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1 .
Proof.

intros.

induction l1.

- simpl. rewrite app_nil_r. reflexivity.

- simpl. rewrite IHl1. rewrite app_assoc. reflexivity. 
    
Qed.

Theorem rev_involutive: forall X:Type, forall l : list X,
    rev (rev l) = l .
Proof.

intros.

induction l.

- reflexivity. 

- simpl. rewrite rev_app_distr. simpl. rewrite IHl. reflexivity. 
    
Qed.

Check pair nat bool.

Fixpoint combine{X Y: Type} (l1: list X)(l2: list Y) : list  (X * Y) :=
    match l1 with
    | [] => []
    | cons n1 l1' =>    match l2 with 
                        | [] => []
                        | cons n2 l2' => cons (pair n1 n2) (combine l1' l2') 
                        end
    end.


Compute (combine [1;2;3] [true;false]).

Definition fst {X Y :Type} (p: X*Y): X :=
    match p with
    | (x , y) => x
    end.

Definition sed {X Y :Type} (p: X*Y): Y :=
    match p with
    | (x , y) => y
    end.

Fixpoint split {X Y :Type} (l : list (X * Y)) : (list X) * (list Y) :=
    match l with
    | [] => pair [] []
    | p :: l' => pair ((fst p)::(fst (split l'))) ((sed p)::(sed (split l')))
    end.

Compute (split [(1, true); (2, false)]).

Check filter.


Fixpoint partition {X : Type} (f : X -> bool) (l : list X) : (list X)*(list X) :=
    match l with
    | [] => pair [] []
    | n::l' => if f n then pair (n::(fst(partition f l'))) ((sed(partition f l')))
                        else pair ((fst(partition f l'))) (n::(sed(partition f l')))
    end.
    

