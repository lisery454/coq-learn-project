Require Export List.
Require Export Nat.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


(* Exercise 1. Binary tree *)

Inductive bt : Type :=
 | empty
 | br (x : nat) (l r : bt).

Check empty.
Definition mybt := br 3 (br 2 empty empty) empty.


Fixpoint sum_bt (t: bt) : nat :=
 match t with
 | empty => 0
 | br x l r => x + sum_bt l + sum_bt r
 end.

Compute sum_bt mybt.


(* Exercise 2. Appending lists*)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  (* FILL IN HERE *) 
  intros X l. induction l as [| h t IHt].
  - reflexivity.  
  - simpl. rewrite IHt; reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* FILL IN HERE *) 
  intros A l m n. induction l as [| h t IHt].
  - reflexivity.
  - simpl. rewrite IHt. reflexivity. 
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* FILL IN HERE *) 
  intros X l1 l2. induction l1 as [| h t IHt].
  - reflexivity. 
  - simpl. rewrite IHt. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* FILL IN HERE *) 
 intros X l1 l2. induction l1 as [| h t IHt].
  - simpl. rewrite app_nil_r. reflexivity. 
  - simpl. rewrite IHt. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) 
  intros X l. induction l as [| h t IHt].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHt. reflexivity.
Qed. 

(* Exercise 3. Combining two lists *)
(** The following function takes two lists and combines them
    into a list of pairs.  In other functional languages, it is often
    called [zip]; we call it [combine] for consistency with Coq's
    standard library. *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Compute (combine [1;2] [false;false;true;true]).


Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(* Exercise 4. Splitting a combined list *)
(** **** Exercise: 2 stars, standard, especially useful (split) 

    The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Fill in the definition of [split] below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
 :=  match l with 
  | nil => (nil, nil)
  | (x, y) :: t => (x :: fst (split t), y :: snd (split t))
  end.


Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* FILL IN HERE *) 
  reflexivity.
Qed.

(* Exercise 5. Partition of a list *)
(** **** Exercise: 

    Use [filter] to write a Coq function [partition]:

      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X

   Given a set [X], a predicate of type [X -> bool] and a [list X],
   [partition] should return a pair of lists.  The first member of the
   pair is the sublist of the original list containing the elements
   that satisfy the test, and the second is the sublist containing
   those that fail the test.  The order of elements in the two
   sublists should be the same as their order in the original list. *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
 :=  (filter test l, filter (fun a => negb (test a)) l).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
(* FILL IN HERE *) 
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* FILL IN HERE *) 
Proof. reflexivity. Qed.
(** [] *)


(* Exercise 6. Map functions *)
Definition f (n: nat) : nat :=
  if even n then 2 * n
  else 3 * n.

Definition changelist (l : list nat) : list nat :=
  map f l.

Example test: changelist [1;2;3;4;5;6] = [3; 4; 9; 8; 15; 12].
Proof. unfold changelist. reflexivity. Qed.


