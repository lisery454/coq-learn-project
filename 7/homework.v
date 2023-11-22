Require Import Nat.

Inductive arith_exp : Type :=
    | Num(n: nat)
    | Add(a1 a2: arith_exp)
    | Sub(a1 a2: arith_exp)
    | Mul(a1 a2: arith_exp)
    | Div(a1 a2: arith_exp)
    | Mod(a1 a2: arith_exp)
    | Exp(a1 a2: arith_exp)
    | Gcd(a1 a2: arith_exp).

Fixpoint aeval(a : arith_exp) : nat :=
    match a with
    | Num n => n
    | Add a1 a2 => add (aeval a1) (aeval a2)
    | Sub a1 a2 => sub (aeval a1) (aeval a2)
    | Mul a1 a2 => mul (aeval a1) (aeval a2)
    | Div a1 a2 => div (aeval a1) (aeval a2)
    | Mod a1 a2 => modulo (aeval a1) (aeval a2)
    | Exp a1 a2 => pow (aeval a1) (aeval a2)
    | Gcd a1 a2 => gcd (aeval a1)  (aeval a2)
    end.


Definition myexp := Gcd (Exp (Div (Num 5) (Num 2)) (Mod (Num 7)(Num 4)))
                        (Mul (Num 2) (Num 6)).


Example test_aeval : aeval myexp = 4.

Proof. reflexivity. Qed.


                        
