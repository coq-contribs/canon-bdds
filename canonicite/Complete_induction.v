(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* Course of values induction                                               *)
(* To be integrated in ARITH library                                        *)
(*                                                                          *)
(****************************************************************************)
(*                           Complete_induction.v                           *)
(****************************************************************************)

Require Import Lt.
Require Import Le.

Definition lt_hereditary (P : nat -> Prop) :=
  forall n : nat, (forall m : nat, m < n -> P m) -> P n.

Lemma le_split : forall m n : nat, m <= S n -> m <= n \/ m = S n.
Proof.
intros m n H; elim (le_lt_or_eq m (S n)); auto with arith.
Qed.

Lemma course_of_values :
 forall P : nat -> Prop, lt_hereditary P -> forall n m : nat, m <= n -> P m.
Proof.
unfold lt_hereditary in |- *; simple induction n.
intros; apply H.
elim (le_n_O_eq m); trivial with arith.
intros p abs; elim lt_n_O with p; trivial with arith.
intros p lemp m lemSp; elim le_split with m p; auto with arith.
intro E; rewrite E; auto with arith. (* using lt_n_Sm_le *)
Qed.

Lemma complete_induction :
 forall P : nat -> Prop, lt_hereditary P -> forall n : nat, P n.
Proof.
intros; apply course_of_values with (m := n) (n := n); auto with arith.
Qed.

(* Version Ledinot *)
Lemma nat_wf_ind :
 forall P : nat -> Prop,
 P 0 ->
 (forall k : nat, (forall l : nat, l <= k -> P l) -> P (S k)) ->
 forall n : nat, P n.
Proof.
intros P H0 Hk.
cut (forall n k : nat, k <= n -> P k).
intros HC n.
apply HC with (n := n); auto with arith.
simple induction n.
intros k Def_k.
elimtype (0 = k); auto with arith.
clear n.
intros n Hn k k_le_Sn.
elim (le_split k n); auto with arith.
intro Def_k.
rewrite Def_k.
auto with arith.
Qed.
