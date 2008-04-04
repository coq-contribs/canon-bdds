(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* A few extra lemmas concerning arithmetic and booleans                    *)
(*   -- ought to be integrated in ARITH and BOOL libraries                  *)
(*                                                                          *)
(****************************************************************************)
(*                                Prelude1.v                                *)
(****************************************************************************)

Require Import Compare.
Require Import Lt.

Lemma le_dec_0 : forall n m : nat, n <= m \/ m <= n.
Proof.
intros n m.
elim (le_dec n m); auto with arith. 
Qed.
Hint Resolve le_dec_0.

Lemma le_nSm_le_nm_or_eq : forall m n : nat, n <= S m -> n <= m \/ n = S m.
Proof.
intros m n H.
cut (n < S m \/ n = S m).
simple induction 1; auto with arith.
apply le_lt_or_eq; trivial with arith.
Qed.

Lemma le_ne_gt : forall m n : nat, m <= n -> m <> n -> n > m.
Proof.
intros m n H1 H2.
cut (m < n \/ m = n).
simple induction 1; auto with arith.
intro; absurd (m = n); auto with arith.
apply le_lt_or_eq; trivial with arith.
Qed.

Require Import Bool.

Lemma eq_bool_dec : forall b1 b2 : bool, b1 = b2 \/ b1 <> b2.
Proof.
simple induction b1; simple induction b2; auto with arith bool.
Qed.
