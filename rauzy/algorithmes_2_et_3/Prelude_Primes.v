(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*           Definitions and lemmas about prime implicants  (Primes)        *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                             Prelude_Primes.v                             *)
(****************************************************************************)

Require Import Prelude_BDT.
Require Import CanonBDDs.rauzy.algorithme1.Boolean_functions.
Require Import CanonBDDs.rauzy.algorithme1.BDTs.
Require Import Prelude_Paths.
Require Import Prelude_Implicants.
Require Import Monotony.

Definition Prime (p : Path) (f : BF) :=
  Implicant p f /\
  (forall p' : Path, Implicant p' f -> Divides p' p -> Divides p p').



(*---------------           Prime of functions          --------------------*)


Lemma Prime_implicant :
 forall (p : Path) (f : BF), Prime p f -> Implicant p f.
Proof.
unfold Prime in |- *.
simple induction 1; auto with v62.
Qed.
Hint Resolve Prime_implicant.

Lemma Prime_ordered : forall (p : Path) (f : BF), Prime p f -> Ordered p.
Proof.
intros p f Hp.
elim (inv_Implicant p f (Prime_implicant p f Hp)); auto with v62.
Qed.

Lemma No_prime_FALSE : forall p : Path, ~ Prime p FALSE.
Proof.
intro p.
unfold Prime in |- *.
apply deMorgan_not_and.
left; exact (No_implicant_FALSE p).
Qed.

Lemma Nil_prime_of_TRUE : Prime Nil TRUE.
Proof.
unfold Prime in |- *.
split;
 [ apply Implicants_TRUE; trivial with v62
 | intros p H1p H2p; exact (Nil_divides_all p) ].
Qed.

Lemma Nil_only_prime_of_TRUE : forall p : Path, Prime p TRUE -> p = Nil.
Proof.
intro p.
unfold Prime in |- *.
simple induction 1; intros H1 H2; clear H.
apply (incl_nil_eq nat); change (Divides p Nil) in |- *.
apply H2;
 [ apply Implicants_TRUE; trivial with v62 | exact (Nil_divides_all p) ].
Qed.


(*-----------           Prime of bdt functions               ----------*)

Lemma Vars_prime_le_dim :
 forall b : BDT,
 OBDT b -> forall p : Path, Prime p (Fun b) -> Head p <= Dim b.
Proof.
intros b HO p Hp.
elim (le_or_lt (Head p) (Dim b)); [ trivial with v62 | intro Habsurde ].
elim (Nil_or_not_Nil p);
 [ intro H; rewrite H; auto with v62 | simple induction 1; intros i Hi ].
absurd (Of (Head p) p); [ idtac | exact (Head_of_p_in_p p i Hi) ].
apply Contra with (Of (Head p) (Sub p (Head p)));
 [ idtac | exact (I_out_of_Sub_ip p (Head p)) ].
unfold Prime in Hp.
elim Hp; intros H1p H2p; clear Hp.
unfold Divides at 2 in H2p.
intro Hhead; apply H2p; try assumption.
  (* p-head(p) Implicant of Fun(b)  *)
exact (L14bis b HO p H1p (Head p) (lt_gt (Dim b) (Head p) Habsurde)).
  (* p-head(p) Divides p *)
exact (Of_sub_pi_of_p p (Head p)).
Qed.

Lemma Dim_highest_var_of_prime :
 forall b : BDT,
 OBDT b ->
 forall p : Path, Prime p (Fun b) -> forall i : nat, i > Dim b -> ~ Of i p.
Proof.
intros b HO p Hp i Hi.
unfold not in |- *; intro Habs.
absurd (i <= Dim b);
 [ exact (gt_not_le i (Dim b) Hi) | apply le_trans with (Head p) ].
exact (Head_max_of_ordered_path p (Prime_ordered p (Fun b) Hp) i Habs).
exact (Vars_prime_le_dim b HO p Hp).
Qed.

Lemma Prime_h_cons_ip_ordered :
 forall (i : nat) (h l : BDT),
 OBDT (Node i h l) -> forall p : Path, Prime p (Fun h) -> Ordered (Cons i p).
Proof.
intros i h l HO p Def_p.
apply Cons_ordered;
 [ exact (Prime_ordered p (Fun h) Def_p) | apply gt_le_trans with (Dim h) ].
elim (dim_node_dim_sons i h l HO); auto with v62.
apply Vars_prime_le_dim;
 [ elim (ordered_node_ordered_sons i h l HO); auto with v62 | assumption ].
Qed.


(*-------                   From node to sons               -------------*)

Section Node_to_Sons.

Variable i : nat.
Variable h l : BDT.
Hypothesis HO : OBDT (Node i h l).
Hint Resolve HO.

Variable p : Path.

Remark Lb_4bis :
 Prime p (Fun (Node i h l)) -> Of i p -> forall j : nat, j > i -> ~ Of j p.
Proof. 
intros Def_p Hi.
unfold Prime in Def_p; elim Def_p; intros H1 H2; clear Def_p.
unfold not in |- *; intros j H1j H2j.
absurd (Of j (Sub p j));
 [ exact (I_out_of_Sub_ip p j) | unfold Divides at 2 in H2 ].
apply H2;
 [ apply L14bis; auto with v62
 | unfold Divides in |- *; exact (Of_sub_pi_of_p p j)
 | assumption ].
Qed.

Remark Lc_4bis : Prime p (Fun (Node i h l)) -> Of i p -> i = Head p.
Proof.
intros Def_p Hi.
generalize Def_p.
unfold Prime in Def_p; elim Def_p; intros H1 H2.
(* Change (Prime p (Fun (Node i h l))) in Def_p. *)
clear Def_p; intro Def_p.
elim (inv_Implicant p (Fun (Node i h l)) H1); intros H11 H12.
apply La_4bis; try assumption.
exact (Lb_4bis Def_p Hi).
Qed.

Remark Ld_4bis :
 Prime p (Fun (Node i h l)) ->
 Of i p -> exists p' : Path, p = Cons i p' /\ Ordered (Cons i p').
Proof.
intros Def_p Hi.
generalize Def_p.
unfold Prime in Def_p; elim Def_p; intros H1 H2.
(* Change (Prime p (Fun (Node i h l))) in Def_p. *)
clear Def_p; intro Def_p.
elim (Tail_exists p i Hi); intros p' Def_p'.
exists p'; split; [ rewrite (Lc_4bis Def_p Hi); assumption | idtac ]. 
rewrite (Lc_4bis Def_p Hi).
rewrite <- Def_p'. 
elim (inv_Implicant p (Fun (Node i h l)) H1); auto with v62.
Qed.

Remark Le_4bis :
 forall p : Path,
 Ordered (Cons i p) ->
 forall p' : Path,
 Implicant p' (Fun h) -> Divides p' p -> Ordered (Cons i p').
Proof.
intros p1 Hp p' H1p' H2p'.
apply Cons_ordered;
 [ elim (inv_Implicant p' (Fun h) H1p'); auto with v62 | idtac ].
elim (Nil_or_not_Nil p').
     (* Case p'=Nil *)
intro Def_p'; rewrite Def_p'; simpl in |- *.
exact (Dim_node_gt_O i h l HO).
    (* Case p'=/=Nil *)
simple induction 1; intros k Def_k.
apply gt_le_trans with (Head p1).
elim (p_inv_Ordered (Cons i p1) Hp); auto with v62.
apply Head_max_of_ordered_path.
elim (p_inv_Ordered (Cons i p1) Hp); auto with v62.
unfold Divides in H2p'.
apply H2p'.
apply Head_of_p_in_p with k; assumption.
Qed.

Lemma L4bis :
 Prime p (Fun (Node i h l)) ->
 Of i p -> exists p' : Path, p = Cons i p' /\ Prime p' (Fun h).
Proof.
intros Def_p Hi.
generalize Def_p.
unfold Prime in Def_p; elim Def_p; intros H1 H2.
(* Change (Prime p (Fun (Node i h l))) in Def_p. *)
clear Def_p; intro Def_p.
elim (Ld_4bis Def_p Hi).
intros p' Hp'.
elim Hp'; intros Def_p' H.
exists p'; split; [ elim Hp'; auto with v62 | idtac ].
unfold Prime in |- *; split.
(*--- (Implicant p' (Fun h)) ---*)
apply L40 with i l; [ auto with v62 | idtac ].
rewrite <- Def_p'; assumption.
(*--- p' least implicant of (Fun h) ---*)
intros p'' H1p'' H2p''.
apply Divides_cons_divides_tail with i; [ assumption | idtac | idtac ].
(* (Ordered (Cons i p'')) *)
exact (Le_4bis p' H p'' H1p'' H2p'').
(* (Divides (Cons i p') (Cons i p'')) *)
elim Def_p'; apply H2.
apply L2; auto with v62.
elim (p_inv_Ordered (Cons i p'') (Le_4bis p' H p'' H1p'' H2p''));
 auto with v62.
rewrite Def_p'; apply Divides_tail_divides_cons; trivial with v62.
Qed.

Lemma L5bis : Prime p (Fun (Node i h l)) -> ~ Of i p -> Prime p (Fun l).
Proof.
intros Def_p Hi.
unfold Prime in Def_p; elim Def_p; intros H1 H2; clear Def_p.
unfold Prime in |- *; split;
 [ apply L5 with i h; assumption | intros p' H1p' H2p' ].
apply H2;
 [ apply L10; [ apply L80 with p; trivial with v62 | assumption ]
 | assumption ].
Qed.

Lemma L12 : Prime (Cons i p) (Fun (Node i h l)) -> ~ Implicant p (Fun l).
Proof.
intro Def_p.
unfold not in |- *; intro Habsurde.
unfold Prime in Def_p; elim Def_p; intros H1 H2; clear Def_p.
absurd (Of i p).
(*  ~(Of i p)  *)
apply L11.
elim (inv_Implicant (Cons i p) (Fun (Node i h l)) H1); auto with v62.
(*   (Of i p)  *) 
unfold Divides at 2 in H2.
apply H2; [ idtac | unfold Divides in |- *; auto with v62 | auto with v62 ].
apply L10; auto with v62.
apply L11.
elim (inv_Implicant (Cons i p) (Fun (Node i h l)) H1); auto with v62.
Qed.

End Node_to_Sons.


(*-------------              From sons to node              ---------------*)

Section Sons_to_Node.

Variable i : nat.
Variable h l : BDT.
Hypothesis HO : OBDT (Node i h l).
Hint Resolve HO.

Variable p : Path.

Lemma Prime_l_prime_node : Prime p (Fun l) -> Prime p (Fun (Node i h l)).
Proof.
unfold Prime in |- *; simple induction 1; intros H1p H2p; clear H.
split.
  (* p Implicant of Fun(Node) *)
apply (L10 i h l p); try assumption.
apply (Dim_highest_var_of_prime l);
 [ elim (ordered_node_ordered_sons i h l HO); auto with v62
 | unfold Prime in |- *; auto with v62
 | elim (dim_node_dim_sons i h l HO); auto with v62 ].
  (* p smallest *)
intros p' H1p' H2p'.
apply H2p; try assumption.
apply (L5 i h l p' H1p').
apply Contra with (Of i p);
 [ unfold Divides in H2p'; exact (H2p' i) | idtac ].
apply (Dim_highest_var_of_prime l);
 [ elim (ordered_node_ordered_sons i h l HO); auto with v62
 | unfold Prime in |- *; auto with v62
 | elim (dim_node_dim_sons i h l HO); auto with v62 ].
Qed.

Lemma Prime_h_prime_node :
 Prime p (Fun h) ->
 Monotonic (Fun l) ->
 ~ Implicant p (Fun l) -> Prime (Cons i p) (Fun (Node i h l)).
Proof.
intros H1p Hmon H2p.
unfold Prime in H1p; elim H1p; intros H1p_impl H1p_min; clear H1p.
unfold Prime in |- *; split.
(* Implicant *)
apply (L2 i h l HO p H1p_impl).
apply gt_le_trans with (Dim h);
 [ elim (dim_node_dim_sons i h l HO); trivial with v62
 | apply Vars_prime_le_dim ].
elim (ordered_node_ordered_sons i h l); auto with v62.
unfold Prime in |- *; auto with v62.
(* smallest *)
intros p' H1p' H2p'.
elim (Of_path_dec p' i); intro Cas.
  (*-- i in p' --*)
elim (Ordered_divisor_of_cons_ip i p) with p';
 [ intros tl' Def_tl'
 | apply (Prime_h_cons_ip_ordered i h l HO); unfold Prime in |- *;
    auto with v62
 | assumption
 | elim (inv_Implicant p' (Fun (Node i h l)) H1p'); auto with v62
 | assumption ].
rewrite Def_tl'; apply Divides_tail_divides_cons.
apply H1p_min;
 [ apply (L40 i h l HO); elim Def_tl'; assumption
 | apply Divides_cons_divides_tail with i ].
elim Def_tl'; elim (inv_Implicant p' (Fun (Node i h l)) H1p'); auto with v62.
apply (Prime_h_cons_ip_ordered i h l HO); unfold Prime in |- *; auto with v62.
elim Def_tl'; assumption.
  (*-- i not in p' --*)
absurd (Implicant p (Fun l));
 [ assumption | apply Divides_implic_implic with p' ].
assumption.
exact (L5 i h l p' H1p' Cas).
exact (L8 p' p i H2p' Cas).
elim (inv_Implicant p (Fun h) H1p_impl); auto with v62.
Qed.

End Sons_to_Node.

Lemma Prime_exists :
 forall b : BDT, OBDT b -> b <> Zero -> exists p : Path, Prime p (Fun b).
Proof.
simple induction 1.
(* b=Zero *)
simple induction 1; trivial with v62.
(* b=One  *)
intro H1; exists Nil; simpl in |- *; exact Nil_prime_of_TRUE.
(* b=Node *)
clear H b;
 intros bh bl HObh Hrec_bh HObl Hrec_bl i H1i H2i Hneq_sons Hneq_rec.
elim (eq_BDT_decidable bl Zero); intro Cas_bl.
  (*-- bl=Zero --*)
elim (eq_BDT_decidable bh Zero); intro Cas_bh.
      (*-- bh=Zero --*) 
absurd (bh = bl);
 [ assumption | rewrite Cas_bh; rewrite Cas_bl; trivial with v62 ].
      (*-- bh=/=Zero --*)
elim (Hrec_bh Cas_bh); intros ph Def_ph. 
exists (Cons i ph).
apply (Prime_h_prime_node i bh bl) with (p := ph);
 [ auto with v62
 | assumption
 | rewrite Cas_bl; simpl in |- *; exact (Fcst_monotonic false)
 | rewrite Cas_bl; simpl in |- *; exact (No_implicant_FALSE ph) ].
  (*-- bl=/=Zero --*)
elim (Hrec_bl Cas_bl); intros pl Def_pl. 
exists pl.
apply (Prime_l_prime_node i bh bl) with (p := pl); auto with v62. 
Qed.


