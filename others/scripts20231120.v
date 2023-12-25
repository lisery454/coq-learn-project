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
  intros X l. induction l as [ | h t IHt].
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

(* Exercise 7. Fold function *)
Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Compute fold plus [1;2;3;4] 0.

Definition sumPair (l : list nat) : nat * nat :=
  (fold plus (filter odd l) 0, fold plus (filter even l) 0).

Example test_sumPair : sumPair [1;2;3;4;5] = (9,6).
Proof. unfold sumPair. reflexivity. Qed.


(* Exercise 8. BigIntersection of lists *)
Fixpoint create (n : nat) :=
  match n with
  | 0 => [0]
  | S n' => create n' ++ [n]
  end.

Compute create 10.

Fixpoint ismember (a : nat)(l : list nat) : bool :=
  match l with
  | nil => false
  | h :: l' => if eqb a h then true
               else ismember a l'
  end.

Fixpoint inter (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => []
  | h :: t => if ismember h l2 then h :: inter t l2
              else inter t l2
  end.
Definition bigInter (l : list (list nat)) (n : nat) : list nat :=
  fold inter l (create n).

Example test_bigInter: bigInter [[1;3;5]; [2;3;7;6;5]; [3;9;8;5]] 10 = [3;5].
Proof. unfold bigInter. reflexivity. Qed.

(* Exercise 9. Relations *)
Inductive CE : nat -> nat -> Prop :=
 | CE1: CE 0 2
 | CE2: forall n m, CE n m -> CE (S (S n)) (S (S m)).

Example CE_SS : forall n m, CE (S (S n)) (S (S m)) -> CE n m.
Proof. intros n m E. 
inversion E as [| n' m' E']. apply E'. 
Qed.

Theorem testCE : CE 4 6.
Proof. (* Fill in here *) 
  repeat constructor.
Qed.

(* Exercise 10. Subsequence relation *)

Inductive subseq : list nat -> list nat -> Prop :=
(* FILL IN HERE *)
  | sub1 l : subseq nil l
  | sub2 l1 l2 a (H : subseq l1 l2) : subseq l1 (a :: l2)
  | sub3 l1 l2 a (H : subseq l1 l2) : subseq (a :: l1) (a :: l2).

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  (* FILL IN HERE *) 
  induction l as [ | a t IHt].
  - apply sub1.
  - apply sub3. apply IHt.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  (* FILL IN HERE *) 
  intros l1 l2 l3 H. induction H; simpl. 
  - constructor.
  - apply sub2. apply IHsubseq.
  - apply sub3. apply IHsubseq.
Qed.

Lemma subseq_nil : forall l,
    subseq l [ ] -> l = [].
Proof. intros [| h t] e.
  - reflexivity.
  - inversion e.
Qed.

Lemma noeq : eqb 1 0 = true -> 1=300.
Proof. intro H. inversion H. Qed.

Lemma subseq_hd : forall h t l, 
   subseq (h :: t) l -> subseq t l.
Proof. intros h t l H. induction l as [ | a tl IHtl].
  - inversion H. 
  - inversion H.
    + apply IHtl in H2. apply sub2; apply H2.
    + apply sub2. apply H1.
Qed. 
 
Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  (* FILL IN HERE *) 
  intros l1 l2 l3. generalize l2. generalize l1.
  induction l3 as [| h3 t3 IHt3].
  - intros la lb eqa eqb.
    apply subseq_nil in eqb. rewrite eqb in eqa.
    apply subseq_nil in eqa. rewrite eqa. apply sub1.
  - intros la lb eqa eqb.
    inversion eqb.
    + rewrite <- H in eqa. apply subseq_nil in eqa. 
      rewrite eqa. apply sub1.
    + apply sub2. apply (IHt3 _ _ eqa H1).
    + inversion eqa.
      * apply sub1.
      * apply sub2. apply (IHt3 _ _ H3).
        rewrite <- H5 in H0. inversion H0. 
        rewrite H8 in H1. apply H1.
      * rewrite <- H5 in H0. inversion H0.
        rewrite <- H. rewrite H7. apply sub3.
        rewrite H8 in H1. apply (IHt3 _ _ H3 H1).
Qed.

(* Exercise 11. Regular expressions *)
Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : [0;1;0;1] =~ Star (App (Char 0) (Char 1)).
Proof. apply (MStarApp [0;1] [0;1]).
  - apply (MApp [0]).
    + apply MChar.
    + apply MChar.
  - apply (MStarApp [0;1] []).
    + apply (MApp [0]).
     ++ apply MChar.
     ++ apply MChar.
    + apply MStar0.
Qed.

(* Exercise 12. IMP *)
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

Example test_beval1:
  beval (BLe (APlus (ANum 1) (ANum 2)) (AMult (ANum 1) (ANum 2))) = false.
Proof. reflexivity. Qed.

(** We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0 + e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)
Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

(** To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
 :=   match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.


Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  (* FILL IN HERE *) 
  intro b. induction b; 
    try (simpl; reflexivity);
     try (simpl; repeat (rewrite optimize_0plus_sound); reflexivity);
     try (simpl; rewrite IHb; reflexivity).
     simpl; rewrite IHb1; rewrite IHb2; reflexivity.
Qed.  

