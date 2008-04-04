(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                Uniqueness of the reduced Shannon Tree                    *)
(*                               Canonicity                                 *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                               Canonicity.v                               *)
(****************************************************************************)


Require Import Prelude_BDT.
Require Import bdd.rauzy.algorithme1.Boolean_functions.
Require Import bdd.rauzy.algorithme1.BDTs.
Require Import Inductions.
Require Import Formula_to_BDT.


Lemma Unique_Zero :
 forall b : BDT, OBDT b -> BF_eq (Fun Zero) (Fun b) -> Zero = b.
Proof.
simple induction b; [ trivial with v62 | idtac | idtac ].
simpl in |- *; intros; absurd (BF_eq TRUE FALSE); auto with v62.
exact TRUE_neq_FALSE.
(*   Case b=Node(i,h,l)  *)
intros i h Hh l Hl HO HF.
absurd (h = l).
   (*  ~ h=l *)
apply ordered_node_neq_sons with (i := i); trivial with v62.
   (*    h=l  *)
cut (BF_eq (Fun Zero) (IF F i then Fun h else Fun l)); trivial with v62.
clear HF; intro HF.
apply trans_equal with Zero.
symmetry  in |- *; apply Hh.
elim (ordered_node_ordered_sons i h l HO); trivial with v62.
apply BF_eq_sym; elim (FB12bis i) with (Fun h) (Fun l) (Fun Zero);
 [ trivial with v62
 | elim (Fun_sons_dim_nondep i h l); trivial with v62
 | elim (Fun_sons_dim_nondep i h l); trivial with v62
 | exact (Fcst_no_depvar i false)
 | auto with v62 ].
apply Hl.
elim (ordered_node_ordered_sons i h l HO); trivial with v62.
elim (FB12bis i) with (Fun h) (Fun l) (Fun Zero);
 [ auto with v62
 | elim (Fun_sons_dim_nondep i h l); trivial with v62
 | elim (Fun_sons_dim_nondep i h l); trivial with v62
 | exact (Fcst_no_depvar i false)
 | auto with v62 ].
Qed.


Lemma Unique_One :
 forall b : BDT, OBDT b -> BF_eq (Fun One) (Fun b) -> One = b.
Proof.
simple induction b; [ idtac | trivial with v62 | idtac ].
simpl in |- *; intros; absurd (BF_eq TRUE FALSE); auto with v62.
exact TRUE_neq_FALSE.
(*   Case b=Node(i,h,l)  *)
intros i h Hh l Hl HO HF.
absurd (h = l).
   (*  ~h=l *)
apply ordered_node_neq_sons with (i := i); trivial with v62.
   (*   h=l  *)
cut (BF_eq (Fun One) (IF F i then Fun h else Fun l)); trivial with v62.
clear HF. intro HF.
apply trans_equal with One.
symmetry  in |- *; apply Hh.
elim (ordered_node_ordered_sons i h l HO); trivial with v62.
apply BF_eq_sym; elim (FB12bis i) with (Fun h) (Fun l) (Fun One);
 [ trivial with v62
 | elim (Fun_sons_dim_nondep i h l); trivial with v62
 | elim (Fun_sons_dim_nondep i h l); trivial with v62
 | exact (Fcst_no_depvar i true)
 | auto with v62 ].
apply Hl.
elim (ordered_node_ordered_sons i h l HO); trivial with v62.
elim (FB12bis i) with (Fun h) (Fun l) (Fun One);
 [ auto with v62
 | elim (Fun_sons_dim_nondep i h l); trivial with v62
 | elim (Fun_sons_dim_nondep i h l); trivial with v62
 | exact (Fcst_no_depvar i true)
 | auto with v62 ].
Qed.

Lemma Choices_eq_bdts_eq :
 forall b1 : BDT,
 OBDT b1 ->
 Dim b1 > 0 ->
 forall b2 : BDT,
 OBDT b2 ->
 Dim b2 > 0 ->
 forall i : nat,
 i = Maxdim b1 b2 ->
 (forall b : bool, Choice b1 i b = Choice b2 i b) -> b1 = b2.
Proof.
intros b1 HO1 Hd1 b2 HO2 Hd2 m Def_m HChoices.
unfold Maxdim in Def_m.
apply node_decomposition_ind with b1;
 [ idtac | apply Dim_gt_O_node_decomposition; assumption ].
intros i1 l1 h1 Def_b1.
apply node_decomposition_ind with b2;
 [ idtac | apply Dim_gt_O_node_decomposition; assumption ].
intros i2 l2 h2 Def_b2.
elim (gt_eq_gt_dec i1 i2).
simple induction 1.
(*---  Case  i2 > i1  ---*)
intro Hi2supi1.
absurd (h2 = l2).
apply ordered_node_neq_sons with i2; rewrite Def_b2; assumption.
apply trans_equal with b1.
   (* h2 = b1 *)
replace b1 with (Choice b1 i2 true);
 [ idtac
 | symmetry  in |- *; apply Choice_invariant; elim Def_b1; trivial with v62 ].
replace h2 with (Choice b2 i2 true).
rewrite (gt_Max i2 i1 Hi2supi1).
change
  (Choice b2 (Max (Dim (Node i2 h2 l2)) (Dim (Node i1 h1 l1))) true =
   Choice b1 (Max (Dim (Node i2 h2 l2)) (Dim (Node i1 h1 l1))) true) 
 in |- *.
rewrite Def_b1; rewrite Def_b2.
elim (Max_sym (Dim b1) (Dim b2)).
elim Def_m; symmetry  in |- *; apply HChoices.
symmetry  in |- *; elim Def_b2; apply Choice_left.
   (* l2 = b1 *)
replace b1 with (Choice b1 i2 false);
 [ idtac
 | symmetry  in |- *; apply Choice_invariant; elim Def_b1; trivial with v62 ].
replace l2 with (Choice b2 i2 false).
rewrite (gt_Max i2 i1 Hi2supi1).
change
  (Choice b1 (Max (Dim (Node i2 h2 l2)) (Dim (Node i1 h1 l1))) false =
   Choice b2 (Max (Dim (Node i2 h2 l2)) (Dim (Node i1 h1 l1))) false) 
 in |- *.
rewrite Def_b1; rewrite Def_b2.
elim (Max_sym (Dim b1) (Dim b2)).
elim Def_m; apply HChoices.
symmetry  in |- *; elim Def_b2; apply Choice_right.
(*---  Case  i1 = i2  ---*)
intro H_i1eqi2.
elim Def_b1; elim Def_b2; apply Components_eq_nodes_eq; try assumption.
   (* h1 = h2 *)
replace h1 with (Choice b1 i1 true).
replace h2 with (Choice b2 i2 true).
rewrite (eq_Max i1 i2 H_i1eqi2).
pattern i2 at 2 in |- *; rewrite (eq_Max i2 i1);
 [ idtac | symmetry  in |- *; trivial with v62 ].
change
  (Choice b1 (Max (Dim (Node i1 h1 l1)) (Dim (Node i2 h2 l2))) true =
   Choice b2 (Max (Dim (Node i2 h2 l2)) (Dim (Node i1 h1 l1))) true) 
 in |- *.
rewrite Def_b1; rewrite Def_b2.
pattern (Max (Dim b2) (Dim b1)) in |- *; elim (Max_sym (Dim b1) (Dim b2)).
elim Def_m; apply HChoices.
symmetry  in |- *; elim Def_b2; apply Choice_left.
symmetry  in |- *; elim Def_b1; apply Choice_left.
   (* l1 = l2 *)
replace l1 with (Choice b1 i1 false).
replace l2 with (Choice b2 i2 false).
rewrite (eq_Max i1 i2 H_i1eqi2).
pattern i2 at 2 in |- *; rewrite (eq_Max i2 i1);
 [ idtac | symmetry  in |- *; trivial with v62 ].
change
  (Choice b1 (Max (Dim (Node i1 h1 l1)) (Dim (Node i2 h2 l2))) false =
   Choice b2 (Max (Dim (Node i2 h2 l2)) (Dim (Node i1 h1 l1))) false) 
 in |- *.
rewrite Def_b1; rewrite Def_b2.
pattern (Max (Dim b2) (Dim b1)) in |- *; elim (Max_sym (Dim b1) (Dim b2)).
elim Def_m; apply HChoices.
symmetry  in |- *; elim Def_b2; apply Choice_right.
symmetry  in |- *; elim Def_b1; apply Choice_right.
(*---  Case  i1 > i2  ---*)
intro Hi1supi2.
absurd (h1 = l1).
apply ordered_node_neq_sons with i1; rewrite Def_b1; assumption.
apply trans_equal with b2.
   (* h1 = b2 *)
replace b2 with (Choice b2 i1 true);
 [ idtac
 | symmetry  in |- *; apply Choice_invariant; elim Def_b2; trivial with v62 ].
replace h1 with (Choice b1 i1 true).
rewrite (gt_Max i1 i2 Hi1supi2).
change
  (Choice b1 (Max (Dim (Node i1 h1 l1)) (Dim (Node i2 h2 l2))) true =
   Choice b2 (Max (Dim (Node i1 h1 l1)) (Dim (Node i2 h2 l2))) true) 
 in |- *.
rewrite Def_b1; rewrite Def_b2.
elim Def_m; apply HChoices.
symmetry  in |- *; elim Def_b1; apply Choice_left.
   (* b2 = l1 *)
symmetry  in |- *.
replace b2 with (Choice b2 i1 false);
 [ idtac
 | symmetry  in |- *; apply Choice_invariant; elim Def_b2; trivial with v62 ].
replace l1 with (Choice b1 i1 false).
rewrite (gt_Max i1 i2 Hi1supi2).
change
  (Choice b1 (Max (Dim (Node i1 h1 l1)) (Dim (Node i2 h2 l2))) false =
   Choice b2 (Max (Dim (Node i1 h1 l1)) (Dim (Node i2 h2 l2))) false) 
 in |- *.
rewrite Def_b1; rewrite Def_b2.
elim (Max_sym (Dim b1) (Dim b2)).
elim Def_m; apply HChoices.
symmetry  in |- *; elim Def_b1; apply Choice_right.
Qed.


Theorem Uniqueness :
 forall t1 t2 : BDT, OBDT t1 -> OBDT t2 -> BF_eq (Fun t1) (Fun t2) -> t1 = t2.
Proof.
intros t1 t2 Ht1 Ht2.
pattern t1, t2 in |- *; apply Induction1_prop; try assumption.
(*   Base cases  *)
exact Unique_Zero.
exact Unique_One.
intros b1 H1 Heq.
symmetry  in |- *; apply Unique_Zero; try assumption.
apply BF_eq_sym; assumption.
intros b1 H1 Heq.
symmetry  in |- *; apply Unique_One; try assumption.
apply BF_eq_sym; assumption.
(*  Induction step  *)
clear Ht1 Ht2 t1 t2.
intros b1 b2 HO1 Hd1 HO2 Hd2 m Def_m Hrec_true Hrec_false H_eq.
apply Choices_eq_bdts_eq with m; try assumption.
simple induction b;
 [ apply Hrec_true; apply Fun_eq_Fun_choice_eq; trivial with v62
 | apply Hrec_false; apply Fun_eq_Fun_choice_eq; trivial with v62 ].
Qed.

Remark Canonicity_BF :
 forall (f1 : BF) (t1 : BDT),
 OBDT t1 ->
 BF_eq (Fun t1) f1 ->
 forall (f2 : BF) (t2 : BDT),
 OBDT t2 -> BF_eq (Fun t2) f2 -> BF_eq f1 f2 -> t1 = t2.
Proof.
intros f1 t1 HO1 Def_t1 f2 t2 HO2 Def_t2 Hf1f2.
apply Uniqueness; try assumption.
apply BF_eq_trans with (f2 := f1); try assumption.
apply BF_eq_trans with (f2 := f2); try assumption.
apply BF_eq_sym; assumption.
Qed.


Remark Canonicity_Boolexp :
 forall (e : Bool_exp) (t1 t2 : BDT),
 Sh_tree_of e t1 -> Sh_tree_of e t2 -> t1 = t2.
Proof.
intros e t1 t2.
unfold Sh_tree_of in |- *.
simple induction 1; intros HO1 HF1.
simple induction 1; intros HO2 HF2.
apply Canonicity_BF with (f1 := Fun_Bexp e) (f2 := Fun_Bexp e); auto with v62.
Qed.


(*---------------------------------------------------------------------------*)
(*           Byproduct of Canonicity: A tautology checker                    *)
(*---------------------------------------------------------------------------*)


Definition Tautology (e : Bool_exp) := BF_eq (Fun_Bexp e) TRUE.


Remark Tautology_decidable :
 forall e : Bool_exp, {Tautology e} + {~ Tautology e}.
Proof.
intro e.
elim (Existence e); unfold Sh_tree_of in |- *; intros te Def_te.
elim (eq_BDT_decidable te One).
(* Case te = One *)
intro H_is; left.
unfold Tautology in |- *.
elim Def_te; rewrite H_is; simpl in |- *; auto with v62.
(* Case te =/= One *)
intro H_isnot; right.
unfold Tautology in |- *.
unfold not in |- *; unfold not in H_isnot.
intro H_absurd.
apply H_isnot.
elim Def_te; intros HO HF.
apply Canonicity_BF with (f1 := Fun te) (f2 := Fun One); try trivial with v62.
simpl in |- *; apply BF_eq_trans with (f2 := Fun_Bexp e); auto with v62.
Qed.
