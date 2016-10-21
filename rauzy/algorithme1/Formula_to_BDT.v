(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*   Computation of the BDT of the function defined by a boolean expression *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                             Formula_to_BDT.v                             *)
(****************************************************************************)

Require Import Prelude_BDT.
Require Import CanonBDDs.rauzy.algorithme1.Boolean_functions.
Require Import CanonBDDs.rauzy.algorithme1.BDTs.
Require Import Inductions.



(*-------------- Boolean expressions ---------------*)

Inductive Bool_exp : Set :=
  | Tr : Bool_exp
  | Fa : Bool_exp
  | Var : forall i : nat, i > 0 -> Bool_exp
  | ANd : Bool_exp -> Bool_exp -> Bool_exp
  | Or : Bool_exp -> Bool_exp -> Bool_exp
  | Not : Bool_exp -> Bool_exp.


(*-----------  Boolean function defined by a boolean expression  ---------*)

Definition Fun_Bexp (E : Bool_exp) : BF :=
  (fix F (b : Bool_exp) : BF :=
     match b with
     | Tr => TRUE
     | Fa => FALSE
     | Var i _ => Boolean_functions.F i
     | ANd b0 b1 => AND (F b0) (F b1)
     | Or b0 b1 => OR (F b0) (F b1)
     | Not b0 => NOT (F b0)
     end) E.
(* Tr *) 
(* Fa *) 
(* Var(i,p)   *) 
(* And(e1,e2) *) 
(* Or(e1,e2)  *) 
(* Not(e)     *) 


(*-----------     Shannon tree of a boolean expression *)

Definition Sh_tree_of (E : Bool_exp) (bdt : BDT) : Prop :=
  OBDT bdt /\ BF_eq (Fun_Bexp E) (Fun bdt).



(*                 Binary boolean operators on BDTs                    *)


Lemma Op2_BDT_overloaded :
 forall Op : BF -> BF -> BF,
 Boolean Op ->
 forall b1 : BDT,
 OBDT b1 ->
 forall b2 : BDT,
 OBDT b2 ->
 Dim b1 > 0 ->
 Dim b2 > 0 ->
 forall i : nat,
 i = Maxdim b1 b2 ->
 (forall b : bool,
  {bb : BDT |
  OBDT bb /\
  Dim bb <= Maxdim (Choice b1 i b) (Choice b2 i b) /\
  BF_eq (Fun bb) (Op (Fun (Choice b1 i b)) (Fun (Choice b2 i b)))}) ->
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Maxdim b1 b2 /\ BF_eq (Fun b3) (Op (Fun b1) (Fun b2))}.
Proof.
intros Op H_Op b1 H1 b2 H2 Hdim1 Hdim2 i Def_i H.
elim (H true).
intro bh; simple induction 1; intro bh_ordered; simple induction 1;
 intros Sup_dimh Fbh_correct.
elim (H false).
intro bl; simple induction 1; intro bl_ordered; simple induction 1;
 intros Sup_diml Fbl_correct.
clear H3 H0 H.
(* Elimination of non dependent variables in the BDT *)
elim (eq_BDT_decidable bh bl).
   (* Case bh = bl *)
intro bh_eq_bl.
exists bh.
split; try assumption.
split.
apply gt_le_weak.
apply gt_le_trans with (m := Maxdim (Choice b1 i true) (Choice b2 i true));
 [ elim Def_i; apply Measure_decrease; assumption | assumption ].
apply BF_eq_trans with (f2 := IF F i then Fun bh else Fun bh);
 try apply eq_f_iff.
pattern bh at 2 in |- *.
replace bh with bl.
apply Corr_hl_Corr_node; assumption.
   (* Case bh =/= bl *)
intro bh_neq_bl.
exists (Node i bh bl).
split.
apply order_node; try assumption; rewrite Def_i.
apply gt_le_trans with (Maxdim (Choice b1 i true) (Choice b2 i true));
 try assumption; elim Def_i; apply Measure_decrease; 
 assumption.
apply gt_le_trans with (Maxdim (Choice b1 i false) (Choice b2 i false));
 try assumption; elim Def_i; apply Measure_decrease; 
 assumption.
split; simpl in |- *.
rewrite Def_i; auto with arith.
apply Corr_hl_Corr_node; assumption.
Qed.


Lemma And_BDT_Zero_b2 :
 forall b2 : BDT,
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b2 /\ BF_eq (Fun b3) (AND (Fun Zero) (Fun b2))}.
Proof.
intro b2.
exists Zero; auto with arith.
Qed.


Lemma And_BDT_One_b2 :
 forall b2 : BDT,
 OBDT b2 ->
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b2 /\ BF_eq (Fun b3) (AND (Fun One) (Fun b2))}.
Proof.
intros b2 H2.
exists b2; auto with arith.
Qed.


Lemma And_BDT_b1_Zero :
 forall b1 : BDT,
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b1 /\ BF_eq (Fun b3) (AND (Fun b1) (Fun Zero))}.
Proof.
intro b1.
exists Zero.
split; try split; auto with arith.
apply BF_eq_trans with (f2 := AND FALSE (Fun b1)); try apply Commutative_AND;
 auto with arith.
Qed.


Lemma And_BDT_b1_One :
 forall b1 : BDT,
 OBDT b1 ->
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b1 /\ BF_eq (Fun b3) (AND (Fun b1) (Fun One))}.
Proof.
intros b1 H1.
exists b1.
split; try split; auto with arith.
simpl in |- *.
apply BF_eq_trans with (f2 := AND TRUE (Fun b1)); try apply Commutative_AND;
 auto with arith.
Qed.


Lemma And_BDT_overloaded :
 forall b1 : BDT,
 OBDT b1 ->
 forall b2 : BDT,
 OBDT b2 ->
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Maxdim b1 b2 /\ BF_eq (Fun b3) (AND (Fun b1) (Fun b2))}.
Proof.
intros b1 H1 b2 H2.
pattern b1, b2 in |- *; apply Induction1 with (b1 := b1) (b2 := b2);
 try assumption.
clear H1 b1 H2 b2; intros b2 H2.
unfold Maxdim in |- *; elim (le_Max (Dim Zero) (Dim b2));
 [ exact (And_BDT_Zero_b2 b2) | auto with arith ].
clear H1 b1 H2 b2; intros b2 H2.
unfold Maxdim in |- *; elim (le_Max (Dim One) (Dim b2));
 [ exact (And_BDT_One_b2 b2 H2) | auto with arith ].
clear H1 b1 H2 b2; intros b1 H1.
unfold Maxdim in |- *; elim Max_sym; elim (le_Max (Dim Zero) (Dim b1));
 [ exact (And_BDT_b1_Zero b1) | auto with arith ].
clear H1 b1 H2 b2; intros b1 H1.
unfold Maxdim in |- *; elim Max_sym; elim (le_Max (Dim One) (Dim b1));
 [ exact (And_BDT_b1_One b1 H1) | auto with arith ].
clear H1 b1 H2 b2; intros b1 b2 HO1 HD1 HO2 HD2.
intros i Def_i Htrue Hfalse.
apply Op2_BDT_overloaded with i; auto with arith.
simple induction b; assumption.
Qed.


Lemma And_BDT :
 forall b1 : BDT,
 OBDT b1 ->
 forall b2 : BDT,
 OBDT b2 -> {b3 : BDT | OBDT b3 /\ BF_eq (Fun b3) (AND (Fun b1) (Fun b2))}.
Proof.
intros b1 H1 b2 H2.
elim (And_BDT_overloaded b1 H1 b2 H2).
intro b3.
intro H; elim H; intro H3.
simple induction 1.
exists b3; auto with arith.
Qed.

Lemma Or_BDT_Zero_b2 :
 forall b2 : BDT,
 OBDT b2 ->
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b2 /\ BF_eq (Fun b3) (OR (Fun Zero) (Fun b2))}.
Proof.
intros b2 H2.
exists b2; auto with arith.
Qed.


Lemma Or_BDT_One_b2 :
 forall b2 : BDT,
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b2 /\ BF_eq (Fun b3) (OR (Fun One) (Fun b2))}.
Proof.
intros b2.
exists One; auto with arith.
Qed.


Lemma Or_BDT_b1_Zero :
 forall b1 : BDT,
 OBDT b1 ->
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b1 /\ BF_eq (Fun b3) (OR (Fun b1) (Fun Zero))}.
Proof.
intros b1 H1.
exists b1.
split; try split; auto with arith.
simpl in |- *.
apply BF_eq_trans with (f2 := OR FALSE (Fun b1)); try apply Commutative_OR;
 auto with arith.
Qed.


Lemma Or_BDT_b1_One :
 forall b1 : BDT,
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b1 /\ BF_eq (Fun b3) (OR (Fun b1) (Fun One))}.
Proof.
intro b1.
exists One.
split; try split; auto with arith.
apply BF_eq_trans with (f2 := OR TRUE (Fun b1)); try apply Commutative_OR;
 auto with arith.
Qed.


Lemma Or_BDT_overloaded :
 forall b1 : BDT,
 OBDT b1 ->
 forall b2 : BDT,
 OBDT b2 ->
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Maxdim b1 b2 /\ BF_eq (Fun b3) (OR (Fun b1) (Fun b2))}.
Proof.
intros b1 H1 b2 H2.
pattern b1, b2 in |- *; apply Induction1 with (b1 := b1) (b2 := b2);
 try assumption.
clear H1 b1 H2 b2; intros b2 H2.
unfold Maxdim in |- *; elim (le_Max (Dim Zero) (Dim b2));
 [ exact (Or_BDT_Zero_b2 b2 H2) | auto with arith ].
clear H1 b1 H2 b2; intros b2 H2.
unfold Maxdim in |- *; elim (le_Max (Dim One) (Dim b2));
 [ exact (Or_BDT_One_b2 b2) | auto with arith ].
clear H1 b1 H2 b2; intros b1 H1.
unfold Maxdim in |- *; elim Max_sym; elim (le_Max (Dim Zero) (Dim b1));
 [ exact (Or_BDT_b1_Zero b1 H1) | auto with arith ].
clear H1 b1 H2 b2; intros b1 H1.
unfold Maxdim in |- *; elim Max_sym; elim (le_Max (Dim One) (Dim b1));
 [ exact (Or_BDT_b1_One b1) | auto with arith ].
clear H1 b1 H2 b2; intros b1 b2 HO1 HD1 HO2 HD2.
intros i Def_i Htrue Hfalse.
apply Op2_BDT_overloaded with i; auto with arith.
simple induction b; assumption.
Qed.


Lemma Or_BDT :
 forall b1 : BDT,
 OBDT b1 ->
 forall b2 : BDT,
 OBDT b2 -> {b3 : BDT | OBDT b3 /\ BF_eq (Fun b3) (OR (Fun b1) (Fun b2))}.
Proof.
intros b1 H1 b2 H2.
elim (Or_BDT_overloaded b1 H1 b2 H2).
intro b3.
intro H; elim H; intro H3.
simple induction 1.
exists b3; auto with arith.
Qed.


(*                The single unary boolean operator on BDTs           *)

Lemma Existence_Not_BDT :
 forall t : BDT,
 OBDT t ->
 {t' : BDT | OBDT t' /\ Dim t' <= Dim t /\ BF_eq (Fun t') (NOT (Fun t))}.
Proof.
simple induction t.
(*  t = Zero *)
intro Zero_ordered.
exists One; simpl in |- *; auto with arith.
(*  t = One *)
intro One_ordered.
exists Zero; simpl in |- *; auto with arith.
(*  t = Node(i,bh,bl) *)
intros i bh Hrec_bh bl Hrec_bl Node_ordered.
elim Hrec_bl;
 [ idtac | elim (ordered_node_ordered_sons i bh bl); auto with arith ].
intro tnot_l.
simple induction 1; intro tnot_l_ordered; simple induction 1;
 intros H_dimtnot_l H_Funtnot_l.
elim Hrec_bh;
 [ idtac | elim (ordered_node_ordered_sons i bh bl); auto with arith ]. 
intro tnot_h.
simple induction 1; intro tnot_h_ordered; simple induction 1;
 intros H_dimtnot_h H_Funtnot_h.
clear H0 p0 H p Hrec_bl Hrec_bh.
(* Two cases: Not left = Not right or not *)
elim (eq_BDT_decidable tnot_h tnot_l).
  (* Case Not left= Not right *)
intro tnot_h_eq_tnot_l.
exists tnot_h.
split; try trivial with arith.
split; simpl in |- *.
apply gt_le_weak.
apply gt_le_trans with (m := Dim bh); auto with arith.
elim (dim_node_dim_sons i bh bl Node_ordered); auto with arith.
apply BF_eq_sym.
apply BF_eq_trans with (f2 := IF F i then NOT (Fun bh) else NOT (Fun bl));
 try apply Commute_if_not.
unfold BF_eq in |- *; intro A.
unfold BF_eq in H_Funtnot_h.
unfold BF_eq in H_Funtnot_l.
unfold IF_ in |- *; elim (F i A); auto with arith.
rewrite tnot_h_eq_tnot_l; auto with arith.
  (* Case Not left =/= right *)
intro tnot_h_neq_tnot_l.
exists (Node i tnot_h tnot_l).
split.
apply order_node; try assumption.
apply gt_le_trans with (m := Dim bh); try assumption.
elim (dim_node_dim_sons i bh bl Node_ordered); auto with arith.
apply gt_le_trans with (m := Dim bl); try assumption.
elim (dim_node_dim_sons i bh bl Node_ordered); auto with arith.
simpl in |- *; split; try apply le_n.
apply BF_eq_sym.
apply BF_eq_trans with (f2 := IF F i then NOT (Fun bh) else NOT (Fun bl));
 try apply Commute_if_not.
apply BF_eq_congruence_op3; auto with arith.
Qed.


Lemma Not_BDT :
 forall t : BDT,
 OBDT t -> {t' : BDT | OBDT t' /\ BF_eq (Fun t') (NOT (Fun t))}.
Proof.
intros t Ht.
elim (Existence_Not_BDT t Ht).
intro nt.
simple induction 1; intro nt_ordered; simple induction 1; intros.
exists nt; auto with arith.
Qed.


Lemma Shtree_Tr : {T : BDT | Sh_tree_of Tr T}.
Proof.
exists One.
unfold Sh_tree_of in |- *; auto with arith.
Qed.


Lemma Shtree_Fa : {T : BDT | Sh_tree_of Fa T}.
Proof.
exists Zero.
unfold Sh_tree_of in |- *; auto with arith.
Qed.


Lemma Shtree_Var :
 forall (i : nat) (p : i > 0), {T : BDT | Sh_tree_of (Var i p) T}.
Proof.
intros i Hi.
exists (Node i One Zero).
unfold Sh_tree_of in |- *; simpl in |- *; auto with arith.
(* Use: def OBDT and eq_Fi_if_i *)
Qed.


Lemma Shtree_And :
 forall e1 : Bool_exp,
 {T : BDT | Sh_tree_of e1 T} ->
 forall e2 : Bool_exp,
 {T : BDT | Sh_tree_of e2 T} -> {T : BDT | Sh_tree_of (ANd e1 e2) T}.
Proof.
intros e1 H_e1 e2 H_e2.
elim H_e1; intros t1 Def_t1.
unfold Sh_tree_of in Def_t1.
elim Def_t1; intros t1_ordered Funt1_correct.
elim H_e2; intros t2 Def_t2.
unfold Sh_tree_of in Def_t2.
elim Def_t2; intros t2_ordered Funt2_correct.
elim (And_BDT t1 t1_ordered t2 t2_ordered); intros t3 Def_t3.
exists t3.
unfold Sh_tree_of in |- *; simpl in |- *.
elim Def_t3; intros t3_ordered Funt3_correct.
split; auto with arith.
apply BF_eq_trans with (f2 := AND (Fun t1) (Fun t2)); auto with arith.
apply BF_eq_congruence_op2; auto with arith.
Qed.


Lemma Shtree_Or :
 forall e1 : Bool_exp,
 {T : BDT | Sh_tree_of e1 T} ->
 forall e2 : Bool_exp,
 {T : BDT | Sh_tree_of e2 T} -> {T : BDT | Sh_tree_of (Or e1 e2) T}.
Proof.
intros e1 H_e1 e2 H_e2.
elim H_e1; intros t1 Def_t1.
unfold Sh_tree_of in Def_t1.
elim Def_t1; intros t1_ordered Funt1_correct.
elim H_e2; intros t2 Def_t2.
unfold Sh_tree_of in Def_t2.
elim Def_t2; intros t2_ordered Funt2_correct.
elim (Or_BDT t1 t1_ordered t2 t2_ordered); intros t3 Def_t3.
exists t3.
unfold Sh_tree_of in |- *; simpl in |- *.
elim Def_t3; intros t3_ordered Funt3_correct.
split; auto with arith.
apply BF_eq_trans with (f2 := OR (Fun t1) (Fun t2)); auto with arith.
apply BF_eq_congruence_op2; auto with arith.
Qed.



Lemma Shtree_Not :
 forall e : Bool_exp,
 {T : BDT | Sh_tree_of e T} -> {T : BDT | Sh_tree_of (Not e) T}.
Proof.
simple induction 1.
intro Te.
simple induction 1.
intros Te_ordered FunTe_correct.
elim (Not_BDT Te Te_ordered).
intros TNot_e.
simple induction 1.
intros TNot_e_ordered FunTNot_e_correct.
exists TNot_e.
unfold Sh_tree_of in |- *; simpl in |- *.
split; try apply BF_eq_trans with (NOT (Fun Te)); auto with arith.
apply BF_eq_congruence_op1; auto with arith.
Qed.

                   
(* Development of a program computing
   the Shannon Tree of a Boolean Expression  *)

Theorem Existence : forall e : Bool_exp, {t : BDT | Sh_tree_of e t}.

Proof.
simple induction e.
exact Shtree_Tr.
exact Shtree_Fa.
exact Shtree_Var.
exact Shtree_And.
exact Shtree_Or.
exact Shtree_Not.
Qed.





