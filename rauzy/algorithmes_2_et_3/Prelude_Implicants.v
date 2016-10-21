(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                   Definitions and lemmas about Implicants                *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                           Prelude_Implicants.v                           *)
(****************************************************************************)

Require Import Prelude_BDT.
Require Import CanonBDDs.rauzy.algorithme1.Boolean_functions.
Require Import CanonBDDs.rauzy.algorithme1.BDTs.
Require Import Prelude_Paths.

(*--------        A classer: Node->Sons, Sons->Node, etc           ---------*)

Inductive Implicant : Path -> BF -> Prop :=
    Def_Implicant :
      forall p : Path,
      Ordered p ->
      forall f : BF,
      (forall A : Assign, Assignment_of p A -> f A = true) -> Implicant p f.

Lemma inv_Implicant :
 forall (p : Path) (f : BF),
 Implicant p f ->
 Ordered p /\ (forall A : Assign, Assignment_of p A -> f A = true).
Proof.
simple induction 1; auto with arith.
Qed.

Lemma inv_notImplicant :
 forall (p : Path) (f : BF),
 ~ Implicant p f ->
 ~ Ordered p \/ ~ (forall A : Assign, Assignment_of p A -> f A = true).
Proof.
intros p f H.
apply deMorgan_or_not.
apply Contra with (Implicant p f);
 [ simple induction 1; intros; apply Def_Implicant; trivial with arith
 | assumption ].
Qed.

Lemma Def_notImplicant :
 forall (p : Path) (f : BF),
 ~ Ordered p \/ ~ (forall A : Assign, Assignment_of p A -> f A = true) ->
 ~ Implicant p f.
Proof.
intros p f H.
apply
 Contra
  with (Ordered p /\ (forall A : Assign, Assignment_of p A -> f A = true));
 [ exact (inv_Implicant p f) | apply deMorgan_not_and; assumption ].
Qed.

Lemma Implicants_TRUE : forall p : Path, Ordered p -> Implicant p TRUE.
Proof.
intros p Hp.
apply Def_Implicant; auto with arith.
Qed.

Lemma No_implicant_FALSE : forall p : Path, ~ Implicant p FALSE.
Proof.
intro p.
unfold not in |- *; intro Habsurde.
absurd (true = false);
 [ exact diff_true_false | elim (inv_Implicant p FALSE Habsurde) ].
intros H1 H2.
elim (Ass_of_well_defined p); intros Ap Def_Ap.
symmetry  in |- *; exact (H2 Ap Def_Ap).
Qed.

Lemma L9 :
 forall p1 p2 : Path,
 Divides p1 p2 ->
 Divides p2 p1 ->
 Ordered p2 -> forall f : BF, Implicant p1 f -> Implicant p2 f.
Proof.
intros p1 p2 H12 H21 H2 f Hp1.
apply Def_Implicant; try assumption.
elim (inv_Implicant p1 f Hp1); intros H1 Hp2.
intros A2 Def_A2.
elim (Ass_of_well_defined p1); intros A1 Def_A1.
rewrite <-
 (Extensionality_Assignments A1 A2
    (Div_div_ass_eq p1 p2 H12 H21 A1 Def_A1 A2 Def_A2))
 ; auto with arith.
Qed.

Lemma L14 :
 forall b : BDT,
 OBDT b ->
 forall p : Path,
 ~ Implicant p (Fun b) ->
 forall i : nat, i > Dim b -> ~ Implicant (Cons i p) (Fun b).
Proof.
intros b Hb p Hp i Hi.
apply Def_notImplicant.
elim (inv_notImplicant p (Fun b) Hp); [ intro; left | intro; right ].
apply Contra with (Ordered p);
 [ exact (Ordered_cons_ordered_tail i p) | assumption ].
apply Contra with (forall A : Assign, Assignment_of p A -> Fun b A = true);
 [ intro Hcons | assumption ].
intros Ap Def_Ap.
elim (Ass_of_well_defined (Cons i p)); intros Aip Def_Aip.
apply (trans_equal (A:=bool)) with (Fun b Aip);
 [ apply Cons_of_non_depvar with p i; try assumption
 | apply Hcons; assumption ].
apply Dim_is_depvar_max; assumption.
Qed.


(*--------------   Lemmas concluding on Fun(Node)    ------------------*)

Section Impl_Node.

Variable i : nat.
Variable h l : BDT.

(* Impl_node1 *)
Lemma L1 :
 forall p : Path,
 Of i p -> Implicant p (Fun h) -> Implicant p (Fun (Node i h l)).
Proof.
intros p Hi Hp.
elim (inv_Implicant p (Fun h) Hp); intros H1 H2.
apply Def_Implicant; try assumption.
intros Ap Def_Ap.
generalize Def_Ap; unfold Assignment_of in |- *; simple induction 1.
intros H_in H_out; simpl in |- *; unfold IF_, F in |- *.
rewrite (H_in i Hi); auto with arith.
Qed.

Lemma L2 :
 OBDT (Node i h l) ->
 forall p : Path,
 Implicant p (Fun h) -> i > Head p -> Implicant (Cons i p) (Fun (Node i h l)).
Proof.
intros HO p Def_p Hi.
elim (inv_Implicant p (Fun h) Def_p); intros H1 H2.
apply Def_Implicant; [ auto with arith | intros Aip Def_Aip ].
elim (Ass_of_well_defined p); intros Ap Def_Ap.
rewrite (Assign_of_cons_eq p Ap Def_Ap i Aip Def_Aip).
change (Frestr (Fun (Node i h l)) i true Ap = true) in |- *.
apply (trans_equal (A:=bool)) with (Fun h Ap); [ idtac | auto with arith ].
pattern h at 2 in |- *; rewrite (Choice_left i h l).
generalize Ap;
 change
   (BF_eq (Frestr (Fun (Node i h l)) i true)
      (Fun (Choice (Node i h l) i true))) in |- *.
apply Choice_Fun_eq_Fun_Choice; auto with arith.
Qed.

Lemma L10 :
 forall p : Path,
 ~ Of i p -> Implicant p (Fun l) -> Implicant p (Fun (Node i h l)).
Proof.
intros p Hi Hp.
elim (inv_Implicant p (Fun l) Hp); intros H1 H2.
apply Def_Implicant; try assumption.
intros Ap Def_Ap.
generalize Def_Ap; unfold Assignment_of in |- *; simple induction 1.
intros H_in H_out; simpl in |- *; unfold IF_, F in |- *.
rewrite (H_out i Hi); auto with arith.
Qed.

End Impl_Node.


(*--------------   Lemmas concluding on Fun(Sons)    ------------------*)


Section Impl_Sons.

Variable i : nat.
Variable h l : BDT.

Lemma L4 :
 forall p : Path,
 Implicant p (Fun (Node i h l)) -> Of i p -> Implicant p (Fun h).
Proof.
intros p Def_p Hi.
elim (inv_Implicant p (Fun (Node i h l)) Def_p); intros H1 H2.
apply Def_Implicant; [ assumption | intros Ap Def_Ap ].
apply (trans_equal (A:=bool)) with (Fun (Node i h l) Ap);
 [ idtac | auto with arith ].
simpl in |- *; unfold IF_, F in |- *.
unfold Assignment_of in Def_Ap; elim Def_Ap; intros H_in H_out; clear Def_Ap.
rewrite (H_in i Hi); trivial with arith.
Qed.

Lemma L5 :
 forall p : Path,
 Implicant p (Fun (Node i h l)) -> ~ Of i p -> Implicant p (Fun l).
Proof.
intros p Def_p Hi.
elim (inv_Implicant p (Fun (Node i h l)) Def_p); intros H1 H2.
apply Def_Implicant; [ assumption | intros Ap Def_Ap ].
apply (trans_equal (A:=bool)) with (Fun (Node i h l) Ap);
 [ idtac | auto with arith ].
simpl in |- *; unfold IF_, F in |- *.
unfold Assignment_of in Def_Ap; elim Def_Ap; intros H_in H_out; clear Def_Ap.
rewrite (H_out i Hi); trivial with arith.
Qed.

Hypothesis HO : OBDT (Node i h l).

Lemma L40 :
 forall p : Path,
 Implicant (Cons i p) (Fun (Node i h l)) -> Implicant p (Fun h).
Proof.
intros p Def_p.
elim
 (inv_Implicant (Cons i p) (Fun h) (L4 (Cons i p) Def_p (I_of_cons_ip p i)));
 intros H1 H2.
apply Def_Implicant;
 [ apply Ordered_cons_ordered_tail with i; assumption | intros Ap Def_Ap ].
elim (Ass_of_well_defined (Cons i p)); intros Aip Def_Aip.
apply (trans_equal (A:=bool)) with (Fun h Aip); [ idtac | auto with arith ].
apply Cons_of_non_depvar with p i; try assumption.
elim (Fun_sons_dim_nondep i h l HO); auto with arith.
Qed.

End Impl_Sons.


(*----------      Lemma used for proofs on primes      -----------------*)

Lemma L14bis :
 forall b : BDT,
 OBDT b ->
 forall p : Path,
 Implicant p (Fun b) ->
 forall i : nat, i > Dim b -> Implicant (Sub p i) (Fun b).
Proof.
intros b Hb p Hp i Hi.
elim (inv_Implicant p (Fun b) Hp); intros H1 H2.
apply Def_Implicant.
apply Ordered_p_ordered_sub_pi; assumption.
intros Asub Def_Asub.
elim (Ass_of_well_defined p); intros Ap Def_Ap.
apply (trans_equal (A:=bool)) with (Fun b Ap);
 [ symmetry  in |- *; apply Sub_of_non_depvar with p i; try assumption
 | auto with arith ].
apply Dim_is_depvar_max; assumption.
Qed.
