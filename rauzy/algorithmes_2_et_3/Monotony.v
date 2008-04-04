(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                        Monotonic functions                               *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                Monotony.v                                *)
(****************************************************************************)

Require Import Prelude_Paths.
Require Import Prelude_Implicants.
Require Import Prelude_BDT.
Require Import bdd.rauzy.algorithme1.Boolean_functions.
Require Import bdd.rauzy.algorithme1.BDTs.


(*----------              Order on Assignments                    -----------*)

Definition Inf (A1 A2 : Assign) := forall i : nat, A1 i = true -> A2 i = true.

Lemma Inf_refl : forall A : Assign, Inf A A.
Proof.
unfold Inf in |- *; auto with v62.
Qed.

Lemma Inf_trans :
 forall A1 A2 A3 : Assign, Inf A1 A2 -> Inf A2 A3 -> Inf A1 A3.
Proof.
unfold Inf in |- *; auto with v62.
Qed.

Lemma Upd_preserves_Inf :
 forall A1 A2 : Assign,
 Inf A1 A2 -> forall (i : nat) (b : bool), Inf (Upd A1 i b) (Upd A2 i b).
Proof.
intros A1 A2 A1_Inf_A2 i b.
unfold Inf in |- *.
intro j.
unfold Inf in A1_Inf_A2.
unfold Upd in |- *; elim (eq_nat_dec i j); auto with v62.
Qed.

Lemma Divides_Inf :
 forall p1 p2 : Path,
 Divides p1 p2 ->
 forall A1 A2 : Assign,
 Assignment_of p1 A1 -> Assignment_of p2 A2 -> Inf A1 A2.
Proof.
intros p1 p2.
unfold Divides in |- *; intro Hd.
intros A1 A2 H1.
elim H1; intros H1_true H1_false.
intro H2; elim H2; intros H2_true H2_false.
unfold Inf in |- *; intros i Hi.
apply H2_true.
apply Hd; apply Inv_Assignment_of_true with A1; assumption.
Qed.

Lemma Anil_lowest : forall An A : Assign, Assignment_of Nil An -> Inf An A.
Proof.
intros An A.
unfold Assignment_of, Inf in |- *.
simple induction 1; intros H1 H2 i Hi.
absurd (true = false);
 [ exact diff_true_false | elim Hi; apply H2; exact (in_nil (a:=i)) ].
Qed.



(*----------------        Monotony        ----------------------------*)

Definition Monotonic (f : BF) :=
  forall A1 A2 : Assign, Inf A1 A2 -> f A1 = true -> f A2 = true.

Lemma BF_eq_Mon_Mon :
 forall f1 f2 : BF, BF_eq f1 f2 -> Monotonic f1 -> Monotonic f2.
Proof.
intros f1 f2 Heq.
unfold Monotonic in |- *; intro H_f1.
intros A1 A2 A1_Inf_A2 H1.
unfold BF_eq in Heq.
apply trans_equal with (f1 A2);
 [ auto with v62 | apply H_f1 with A1; try assumption ]. 
apply trans_equal with (f2 A1); auto with v62.
Qed.


Lemma Mon_Frestr_Mon :
 forall (f : BF) (i : nat) (b : bool),
 Monotonic f -> Monotonic (Frestr f i b).
Proof.
intros f i b.
unfold Monotonic, Frestr in |- *; intros f_Mon A1 A2 A1_Inf_A2.
intro; apply f_Mon with (Upd A1 i b); try assumption.
apply Upd_preserves_Inf; trivial with v62.
Qed.

Lemma Mon_node_Mon_sons :
 forall (i : nat) (h l : BDT),
 OBDT (Node i h l) ->
 Monotonic (Fun (Node i h l)) -> Monotonic (Fun h) /\ Monotonic (Fun l).
Proof.
intros i h l Node_ordered Node_Mon.
split.
(*  left  *)
rewrite (Choice_left i h l).
apply BF_eq_Mon_Mon with (Frestr (Fun (Node i h l)) i true);
 [ apply Choice_Fun_eq_Fun_Choice; auto with v62
 | apply Mon_Frestr_Mon; assumption ].
(*  right *)
rewrite (Choice_right i h l).
apply BF_eq_Mon_Mon with (Frestr (Fun (Node i h l)) i false);
 [ apply Choice_Fun_eq_Fun_Choice; auto with v62
 | apply Mon_Frestr_Mon; assumption ].
Qed.

Lemma Bottom_implicant :
 forall f : BF, Monotonic f -> Implicant Nil f -> BF_eq f TRUE.
Proof.
intros f H1f H2f.
unfold BF_eq in |- *; intro A; unfold TRUE in |- *; simpl in |- *.
elim (Ass_of_well_defined Nil); intros An Def_An.
unfold Monotonic in H1f.
apply H1f with An;
 [ apply Anil_lowest; trivial with v62
 | elim (inv_Implicant Nil f H2f); intros Ha Hb; apply Hb; trivial with v62 ].
Qed.

Lemma Divides_implic_implic :
 forall f : BF,
 Monotonic f ->
 forall p : Path,
 Implicant p f ->
 forall p' : Path, Divides p p' -> Ordered p' -> Implicant p' f.
Proof.
intros f Hf p Hp p' HDp' HOp'.
apply Def_Implicant; [ assumption | idtac ].
intros Ap' Def_Ap'.
elim (Ass_of_well_defined p); intros Ap Def_Ap.
unfold Monotonic in Hf; apply Hf with Ap.
apply Divides_Inf with p p'; try assumption.
elim (inv_Implicant p f Hp); auto with v62.
Qed.

Lemma L13 :
 forall f : BF,
 Monotonic f ->
 forall p : Path,
 ~ Implicant p f ->
 Ordered p -> forall p' : Path, Divides p' p -> ~ Implicant p' f.
Proof.
intros f Hf p HIp HOp p' Hp'.
apply Contra with (Implicant p f);
 [ intro H; apply Divides_implic_implic with p'; assumption | assumption ].
Qed.

Lemma L15 :
 forall (i : nat) (h l : BDT),
 OBDT (Node i h l) ->
 Monotonic (Fun (Node i h l)) ->
 forall p : Path,
 Ordered (Cons i p) -> Implicant p (Fun l) -> Implicant p (Fun h).
Proof.
intros i h l HO HM p H1p H2p.
apply L40 with i l; [ assumption | idtac ].
apply Divides_implic_implic with p;
 [ assumption | idtac | trivial with v62 | assumption ].
apply L10; [ apply L11; trivial with v62 | assumption ].
Qed.

Lemma Fcst_monotonic : forall b : bool, Monotonic (Fcst b).
Proof.
unfold Monotonic in |- *; auto with v62.
Qed.
