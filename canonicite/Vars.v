(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*             Sets of variables indexed by natural numbers                 *)
(*                     representing their order                             *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                  Vars.v                                  *)
(****************************************************************************)

Require Import Peano_dec.
Require Import Compare_dec.
Require Import Compare.
Require Import Le.
Require Import Gt.
Require Import Prelude1.
Require Import CanonBDDs.canonicite.Finite_sets.

Section Intervals.

Variable n : nat.

Inductive Var (n : nat) : Set :=
    Var_intro : forall k : nat, k > 0 -> k <= n -> Var n.

Definition Order (xi : Var n) : nat :=
  match xi return nat with
  | Var_intro i pi qi => i
  end.

Lemma Ordering_surj :
 forall k : nat, k > 0 -> k <= n -> exists x : Var n, k = Order x.
Proof.
intros k H1 H2.
exists (Var_intro n k H1 H2); auto with arith.
Qed.
Hint Resolve Ordering_surj.

Definition eq_Var (xi xj : Var n) := Order xi = Order xj.
Definition le_Var (xi xj : Var n) := Order xi <= Order xj.
Definition gt_Var (xi xj : Var n) := Order xi > Order xj.

Lemma same_order_eq_Var :
 forall (k : nat) (xi xj : Var n),
 Order xi = k -> Order xj = k -> eq_Var xi xj.
Proof.
intros k xi xj Ind_xi Ind_xj.
unfold eq_Var in |- *.
replace (Order xi) with k.
replace (Order xj) with k.
trivial with arith.
Qed.

Lemma eq_Var_same_order :
 forall xi xj : Var n, eq_Var xi xj -> Order xi = Order xj.
Proof.
unfold eq_Var in |- *; auto with arith.
Qed.
Hint Resolve eq_Var_same_order.

Lemma eq_Var_refl : forall x : Var n, eq_Var x x.
Proof.
simple induction x.
unfold eq_Var in |- *; auto with arith.
Qed.
Hint Resolve eq_Var_refl.

Lemma eq_Var_sym : forall x1 x2 : Var n, eq_Var x1 x2 -> eq_Var x2 x1.
Proof.
intros x1 x2 eq_x1_x2.
apply same_order_eq_Var with (k := Order x2); auto with arith.
Qed.
Hint Immediate eq_Var_sym: bdd.

Lemma eq_Var_trans :
 forall x1 x2 x3 : Var n, eq_Var x1 x2 -> eq_Var x2 x3 -> eq_Var x1 x3.
Proof.
intros x1 x2 x3 eq_12 eq_13.
cut (Order x1 = Order x2); auto with arith.
cut (Order x2 = Order x3); auto with arith.
intros H23 H12.
apply same_order_eq_Var with (k := Order x2); auto with arith.
Qed.

Lemma eq_Var_dec : forall xi xj : Var n, {eq_Var xi xj} + {~ eq_Var xi xj}.
Proof.
unfold eq_Var in |- *.
intros xi xj.
apply eq_nat_dec.
Qed.
Hint Resolve eq_Var_dec.

Lemma le_or_gt_Var : forall xi xj : Var n, le_Var xi xj \/ gt_Var xi xj.
Proof.
intros xi xj.
elim (le_gt_dec (Order xi) (Order xj)); intro.
left.
unfold le_Var in |- *; trivial with arith.
right.
unfold gt_Var in |- *; trivial with arith.
Qed.

Lemma Order_le_n : forall x : Var n, Order x <= n.
Proof.
simple induction x; simpl in |- *; auto with arith.
Qed.
Hint Resolve Order_le_n.

Lemma Order_gt_O : forall x : Var n, Order x > 0.
Proof.
simple induction x; simpl in |- *; auto with arith.
Qed.
Hint Resolve Order_gt_O.

Lemma Order_S : forall x : Var n, exists m : nat, Order x = S m.
Proof.
intros.
generalize (Order_gt_O x).
elim (Order x).
intro; absurd (0 > 0); auto with arith.
intros p H1 H2; exists p; trivial with arith.
Qed.

Lemma le_Var_total_order : total_order (Var n) le_Var eq_Var.
Proof.
unfold total_order in |- *.
split.
(*  (order (Var n) le_Var eq_Var) *)
unfold order in |- *.
split; try split.
    (* (reflexivity (Var n) le_Var) *)
unfold reflexivity, le_Var in |- *; auto with arith.
    (* (anti_symetry (Var n) le_Var eq_Var) *)
unfold anti_symetry, le_Var, eq_Var in |- *; auto with arith.
    (* (transitivity (Var n) le_Var) *)
unfold transitivity, le_Var in |- *.
intros xi xj xk xi_le_xj xj_le_xk.
apply le_trans with (m := Order xj); auto with arith.
(*  (totality (Var n) le_Var)     *)
unfold totality, le_Var in |- *; auto with arith.
Qed.
Hint Resolve le_Var_total_order.

(*-----------------       Sets of indexed variables      ------------------*)


Definition Varset (n : nat) := set (Var n).


(*-------------------------------------------------------------------------*)

Axiom
  Proof_irrelevance :
    forall (x : Var n) (P : Varset n),
    P x -> forall a : Var n, eq_Var x a -> P a.

(*-------------------------------------------------------------------------*)

Definition Var_le (k : nat) (x : Var n) : Prop := Order x <= k.


Lemma Var_k_finite : forall k : nat, k <= n -> finite (Var n) (Var_le k).
Proof.
simple induction k.
(* k = O *)
intro H_triv.
apply (extensionality (Var n) (empty (Var n)) (Var_le 0)); auto with arith.
apply Def_set_eq; unfold incl, empty, Var_le, In in |- *; try contradiction.
intros x H_abs.
absurd (Order x <= 0); auto with arith.
(* k -> (S k) *)
clear k.
intros k Hk Sk_le_n.
elimtype (exists x : Var n, S k = Order x); auto with arith.
intros x Order_x.
apply (extensionality (Var n) (add (Var n) (Var_le k) x) (Var_le (S k))).
  (* (set_eq (Var n) (add (Var n) (Var_le k) x) (Var_le (S k))) *)
apply Def_set_eq; unfold incl, empty, Var_le, add, In in |- *.
intro xi.
simple induction 1; auto with arith.
simple induction 1; elim Order_x; auto with arith.
intros xi Oxi_le_Sk.
elim (le_nSm_le_nm_or_eq k (Order xi)); auto with arith.
intro Order_xi.
right.
pattern xi in |- *.
apply Proof_irrelevance with (x := x); auto with arith.
apply same_order_eq_Var with (k := S k); trivial with arith.
symmetry  in |- *; trivial with arith.
  (* (finite (Var n) (add (Var n) (Var_le k) x)) *)
apply finite_add; auto with arith.
unfold In, Var_le in |- *.
elim Order_x; auto with arith.
Qed.

Lemma Var_n_finite : finite (Var n) (all_ (Var n)).
Proof.
apply (extensionality (Var n) (Var_le n) (all_ (Var n))).
apply Def_set_eq; unfold incl, Var_le, all_, In in |- *; auto with arith.
apply Var_k_finite; auto with arith.
Qed.

End Intervals.

Hint Resolve Ordering_surj eq_Var_same_order eq_Var_refl eq_Var_dec
  Order_le_n Order_gt_O le_Var_total_order Var_n_finite.

Hint Immediate eq_Var_sym: bdd.



