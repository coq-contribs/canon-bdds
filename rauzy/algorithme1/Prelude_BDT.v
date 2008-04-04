(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                    Prelude  Synthese Algorithmes Rauzy                   *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                               Prelude_BDT.v                              *)
(****************************************************************************)

(* Uses Axiom  Classic : (A:Prop)~(~A)->A. *)

Require Export Bool. 
Require Export Compare.
Require Export Compare_dec.
Require Export Le.
Require Export Lt.
Require Export Gt.
Require Export Wf_nat.


(*********************           Logic               *************************)

Lemma Contra : forall P Q : Prop, (P -> Q) -> ~ Q -> ~ P.
Proof.
unfold not in |- *; auto.
Qed.


Lemma deMorgan_not_or : forall P Q : Prop, ~ P -> ~ Q -> ~ (P \/ Q).
Proof.
unfold not in |- *.
intros P Q notP notQ.
simple induction 1; auto.
Qed.


Lemma deMorgan_and_not : forall P Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
unfold not in |- *.
intros.
split; auto.
Qed.


Lemma deMorgan_not_and : forall P Q : Prop, ~ P \/ ~ Q -> ~ (P /\ Q).
Proof.
simple induction 1; intro H1; unfold not in |- *; simple induction 1; intros.
absurd P; trivial.
absurd Q; trivial.
Qed.


Lemma P_notnotP : forall P : Prop, P -> ~ ~ P.
Proof.
unfold not in |- *; auto.
Qed.


(*--------------           Classical   identities         -------------------*)

Axiom Classic : forall A : Prop, ~ ~ A -> A.

Lemma excluded_middle : forall A : Prop, A \/ ~ A.
Proof.
intro A.
apply Classic.
unfold not at 1 in |- *; intro H.
elim (deMorgan_and_not A (~ A) H).
intros; absurd (~ A); trivial.
Qed.


Lemma not_all_exist_not :
 forall (A : Set) (P : A -> Prop),
 ~ (forall a : A, P a) -> exists x : A, ~ P x.
Proof.
intros A P H.
apply Classic.
unfold not at 1 in |- *; intro Habsurde.
absurd (forall a : A, P a); try trivial.
intro a.
elim (excluded_middle (P a)); try trivial.
intro Habsurde2.
absurd (exists x : A, ~ P x); [ assumption | exists a; exact Habsurde2 ].
Qed.


Lemma deMorgan_or_not : forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
intros P Q H.
elim (excluded_middle P); elim (excluded_middle Q); auto.
Qed.


(***********                   Booleans                  ********************)

Lemma Commutative_andb : forall b1 b2 : bool, b1 && b2 = b2 && b1.
Proof.
simple induction b1; simple induction b2; auto.
Qed.

Lemma Commutative_orb : forall b1 b2 : bool, b1 || b2 = b2 || b1.
Proof.
simple induction b1; simple induction b2; auto.
Qed.


(***********              Basic  specifications          ********************)

Inductive Case3 (A B C : Prop) : Set :=
  | case_left : A -> Case3 A B C
  | case_middle : B -> Case3 A B C
  | case_right : C -> Case3 A B C.



(*********************           Lists               *************************)


Require Export List.

(*  Restoring hints from List.v and Inlist.v *)
Hint Resolve in_eq in_cons in_or_app incl_refl incl_cons incl_app app_nil_end
  app_ass ass_app lel_refl lel_cons_cons lel_cons lel_nil nil_cons.

Hint Immediate in_app_or incl_tl incl_appl incl_appr: bdd.

Hint Unfold incl.


Lemma nil_included_all : forall (A : Set) (l : list A), incl nil l.
Proof.
intros A l.
unfold incl in |- *.
unfold In in |- *; contradiction.
Qed.


Lemma Nil_or_cons :
 forall (A : Set) (l : list A),
 l = nil \/ (exists a : A, (exists m : list A, l = a :: m)).
Proof.
intro A.
simple induction l;
 [ auto | intros a m Hm; right; exists a; exists m; trivial ].
Qed.

Lemma incl_nil_eq : forall (A : Set) (l : list A), incl l nil -> l = nil.
Proof.
intros A l Hincl.
elim (Nil_or_cons A l); [ trivial | idtac ].
simple induction 1; intro a.
simple induction 1; intros m Def_l.
clear H0 H.
absurd (In a nil).
(* not In *)
exact (in_nil (a:=a)).
(*  In  *)
unfold incl in Hincl.
apply Hincl with (a := a).
rewrite Def_l; auto.
Qed.


Definition eq_decidable (A : Set) := forall a b : A, {a = b} + {a <> b}.


Lemma In_list_dec :
 forall A : Set,
 eq_decidable A -> forall (l : list A) (a : A), In a l \/ ~ In a l.
Proof.
intros A Heq.
simple induction l.
  (* l = nil *)
intro a; right; eapply in_nil.
clear l; intros b l Hl.
intro a.
unfold eq_decidable in Heq.
elim (Heq a b); intro Hab.
  (* l = (cons b l) *)
(* Case a=b *)
elim Hab; left; auto.
(* Case a=/=b *)
elim (Hl a); intro Ha.
left; auto.
right; simpl in |- *; apply deMorgan_not_or; try assumption.
apply Contra with (a = b); auto.
Qed.


 

(***********                   Arithmetic                *******************)


Lemma eq_O_or_gt_O : forall n : nat, {0 = n} + {n > 0}.
Proof.
simple induction n; auto with arith.
Qed.


Lemma lt_gt : forall m n : nat, m < n -> n > m.
Proof.
auto with arith.
Qed.


Lemma gt_lt : forall m n : nat, m > n -> n < m.
Proof.
auto with arith.
Qed.


Lemma gt_neq : forall m n : nat, m > n -> m <> n.
Proof.
unfold not in |- *; intros m n H Habs.
absurd (m < m);
 [ exact (lt_irrefl m)
 | apply gt_lt; pattern m at 2 in |- *; rewrite Habs; trivial ].
Qed.


Lemma le_dec : forall m n : nat, {m <= n} + {~ m <= n}.
Proof.
intros m n.
elim (le_le_S_dec m n); intro Cas.
auto with arith.
right; unfold not in |- *; intro Habs.
elim (le_Sn_n n); apply le_trans with m; auto with arith.
Qed.


Lemma gt_le_weak : forall m n : nat, m > n -> n <= m.
Proof.
intros m n H.
apply lt_le_weak.
apply gt_lt; trivial.
Qed.

Lemma Compar : forall m n : nat, Case3 (m > n) (m = n) (n > m).
Proof.
intros m n.
elim (le_gt_dec m n); intros Cas.
elim (le_lt_eq_dec m n Cas);
 [ intro H; exact (case_right (m > n) (m = n) (n > m) (lt_gt m n H))
 | intro H; exact (case_middle (m > n) (m = n) (n > m) H) ].
exact (case_left (m > n) (m = n) (n > m) Cas).
Qed.


Definition Max (n m : nat) :=
  match le_gt_dec n m return nat with
  | left p => m
  | right q => n
  end.


Lemma Max_le : forall m n : nat, m <= Max m n /\ n <= Max m n.
Proof.
intros m n.
unfold Max in |- *; elim (le_gt_dec m n); auto with arith.
Qed.


Lemma gt_Max : forall m n : nat, m > n -> m = Max m n.
Proof.
intros m n H.
unfold Max in |- *; elim (le_gt_dec m n); auto with arith.
intro Habs.
absurd (m <= n); [ exact (gt_not_le m n H) | assumption ].
Qed.
 

Lemma gt_mn_gt_Max_mn : forall i m n : nat, i > m -> i > n -> i > Max m n.
Proof.
intros i m n H1i H2i.
unfold Max in |- *; elim (le_gt_dec m n); auto with arith.
Qed.


Lemma le_Max : forall m n : nat, m <= n -> n = Max m n.
Proof.
intros m n H.
unfold Max in |- *; elim (le_gt_dec m n); auto with arith.
intro Habs.
absurd (m > n); [ exact (le_not_gt m n H) | assumption ].
Qed.


Lemma Max_sym : forall n1 n2 : nat, Max n1 n2 = Max n2 n1.
Proof.
intros n1 n2.
unfold Max in |- *; elim (le_gt_dec n1 n2); elim (le_gt_dec n2 n1);
 auto with arith.
intros H1 H2.
absurd (n2 > n1); [ exact (gt_asym n1 n2 H2) | assumption ].
Qed.


Lemma eq_Max : forall n1 n2 : nat, n1 = n2 -> n1 = Max n1 n2.
Proof.
intros n1 n2 H.
elim H; unfold Max in |- *; elim (le_gt_dec n1 n1); auto with arith.
Qed.


Lemma Max_mon_left :
 forall n1 n'1 : nat,
 n1 > n'1 -> forall n2 : nat, n1 > n2 -> Max n1 n2 > Max n'1 n2.
Proof.
intros n1 n'1 H1 n2 H2.
unfold Max at 2 in |- *; elim (le_gt_dec n'1 n2); elim (gt_Max n1 n2);
 auto with arith.
Qed.


Lemma Max_mon_right :
 forall n2 n'2 : nat,
 n2 > n'2 -> forall n1 : nat, n2 > n1 -> Max n1 n2 > Max n1 n'2.
Proof.
intros n2 n'2 H2 n1 H1.
unfold Max at 2 in |- *; elim (le_gt_dec n1 n'2); elim (Max_sym n2 n1);
 elim (gt_Max n2 n1); auto with arith.
Qed.


Lemma Max_mon_middle :
 forall n1 n'1 : nat,
 n1 > n'1 -> forall n2 n'2 : nat, n2 > n'2 -> Max n1 n2 > Max n'1 n'2.
Proof.
intros n1 n'1 H1 n2 n'2 H2.
unfold Max in |- *; elim (le_gt_dec n'1 n'2); elim (le_gt_dec n1 n2);
 auto with arith.
intros; apply gt_trans with n2; auto with arith.
intros; apply le_gt_trans with n1; auto with arith.
Qed.
