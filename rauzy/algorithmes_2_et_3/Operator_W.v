(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                          Operator Without (noted W)                      *)
(*                b1 W b2 is approximatively the BDT coding                 *)
(*             the solutions of b1 that are not solution of b2              *)
(*                                                                          *)
(*            Algorithm designed by A.Rauzy of LaBRI (Bordeaux University)  *)
(*                                                                          *)
(****************************************************************************)
(*                               Operator_W.v                               *)
(****************************************************************************)

Require Import Prelude_BDT.
Require Import bdd.rauzy.algorithme1.Boolean_functions.
Require Import bdd.rauzy.algorithme1.BDTs.
Require Import Inductions.
Require Import Canonicity.
Require Import Prelude_Paths.
Require Import Prelude_Implicants.
Require Import Monotony.


(*----------------     Specification of the operator W   -------------------*)
(*                               b1 W b2 = b3                               *)
      
                           
Definition W_sound (b1 b2 b3 : BDT) :=
  forall p : Path, Solution p b3 -> Solution p b1 /\ ~ Implicant p (Fun b2).


Definition W_complete (b1 b2 b3 : BDT) :=
  forall p : Path,
  Solution p b1 ->
  ~ Implicant p (Fun b2) -> exists p' : Path, Solution p' b3 /\ Divides p' p.


Definition W_correct (b1 b2 b3 : BDT) :=
  W_sound b1 b2 b3 /\ W_complete b1 b2 b3.


Hint Unfold W_correct.


(*------------     A Property of W's Specification       ------------------*)


(* Spec_without1 *)
Lemma LP2 : forall b : BDT, OBDT b -> W_complete b Zero Zero -> b = Zero.
Proof.
intros b Hb.
elim (LT1 b Hb);
 [ simple induction 1; trivial with v62
 | unfold W_complete in |- *; simple induction 1;
    intros solb Def_solb Hcomplete ].
elim (Hcomplete solb Def_solb (No_implicant_FALSE solb)).
intro sol_absurde; simple induction 1; intros H1 H2.
absurd (Solution sol_absurde Zero);
 [ exact (No_solution_Zero sol_absurde) | assumption ].
Qed.


(*--------------------------------------------------------------------------*)
(*   Proof-programming of Rauzy's intermediate procedure named Operator W   *)
(*--------------------------------------------------------------------------*)

(*--------------     Definition of b1 Without Zero: b1      --------------*)

Lemma b1_W_Zero :
 forall b1 : BDT,
 OBDT b1 ->
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b1 /\ W_sound b1 Zero b3 /\ W_complete b1 Zero b3}.
Proof.
intros b1 H1.
exists b1.
split; [ assumption | split; [ trivial with v62 | split ] ].
(*  sound   *)
unfold W_sound in |- *.
intro; split; [ assumption | exact (No_implicant_FALSE p) ].
(* complete *)
unfold W_complete in |- *.
intros p H1p H2p; exists p; auto with v62.
Qed.


(*--------------     Definition of b1 Without One: Zero      --------------*)

Lemma b1_W_One :
 forall b1 : BDT,
 OBDT b1 ->
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b1 /\ W_sound b1 One b3 /\ W_complete b1 One b3}.
Proof.
intros b1 H1.
exists Zero.
split; [ trivial with v62 | split; [ trivial with v62 | split ] ].
(*  sound   *)
unfold W_sound in |- *.
intros p Habsurde.
absurd (Solution p Zero); [ exact (No_solution_Zero p) | assumption ].
(* complete *)
unfold W_complete in |- *.
intros p Def_p H; elim H.
apply Implicants_TRUE.
apply Solution_OBDT_ordered with b1; assumption.
Qed.


(*--------------     Definition of Zero Without b2: Zero      --------------*)

Lemma Zero_W_Node :
 forall (i2 : nat) (h2 l2 : BDT),
 OBDT (Node i2 h2 l2) ->
 {b3 : BDT |
 OBDT b3 /\
 Dim b3 <= Dim Zero /\
 W_sound Zero (Node i2 h2 l2) b3 /\ W_complete Zero (Node i2 h2 l2) b3}.
Proof.
intros i2 h2 l2 HO.
exists Zero.
split; [ trivial with v62 | split; [ trivial with v62 | split ] ].
(*  sound   *)
unfold W_sound in |- *.
intros p Habsurde.
absurd (Solution p Zero); [ exact (No_solution_Zero p) | assumption ].
(* complete *)
unfold W_complete in |- *.
intros p Habsurde.
absurd (Solution p Zero); [ exact (No_solution_Zero p) | assumption ].
Qed.


(*--------------     Definition of One Without b2: One      --------------*)

Lemma One_W_Node :
 forall (i2 : nat) (h2 l2 : BDT),
 OBDT (Node i2 h2 l2) ->
 Monotonic (Fun (Node i2 h2 l2)) ->
 {b3 : BDT |
 OBDT b3 /\
 Dim b3 <= Dim One /\
 W_sound One (Node i2 h2 l2) b3 /\ W_complete One (Node i2 h2 l2) b3}.
Proof.
intros i2 h2 l2 HO.
exists One.
split; [ trivial with v62 | split; [ trivial with v62 | split ] ].
(*  sound   *)
unfold W_sound in |- *.
intros p Def_p; split; try assumption.
rewrite (Solution_of_One_is_Nil p Def_p).
unfold not in |- *; intro Habsurde.
absurd (One = Node i2 h2 l2).
apply Contra with (Node i2 h2 l2 = One);
 [ auto with v62 | exact (neq_Node_One i2 h2 l2) ].
apply Uniqueness;
 [ trivial with v62
 | assumption
 | apply BF_eq_sym; apply Bottom_implicant; assumption ].
(* complete *)
unfold W_complete in |- *.
intros p H1p H2p; exists p; auto with v62.
Qed.



Section Recursion_W.

Variable i1 i2 : nat.
Variable h1 h2 l1 l2 : BDT.

Hypothesis HO1 : OBDT (Node i1 h1 l1).
Hypothesis HO2 : OBDT (Node i2 h2 l2).
Hypothesis Hmon : Monotonic (Fun (Node i2 h2 l2)).

Hint Resolve HO1 HO2 Hmon.


(*----      Lemmas for h1--i1--l1 Without h2--i2--l2 when i1 > i2      ------*)

Section Greater_i1.

Hypothesis Hgt : i1 > i2.
Variable bh : BDT.
Hypothesis
  Hh :
    OBDT bh /\
    Dim bh <= Dim h1 /\
    W_sound h1 (Node i2 h2 l2) bh /\ W_complete h1 (Node i2 h2 l2) bh.
Variable bl : BDT.
Hypothesis
  Hl :
    OBDT bl /\
    Dim bl <= Dim l1 /\
    W_sound l1 (Node i2 h2 l2) bl /\ W_complete l1 (Node i2 h2 l2) bl.

Hint Resolve Hgt.

Lemma Node_W_Node_i1_gt_i2_eq :
 bh = bl ->
 {bn : BDT |
 OBDT bn /\
 Dim bn <= Dim (Node i1 h1 l1) /\
 W_sound (Node i1 h1 l1) (Node i2 h2 l2) bn /\
 W_complete (Node i1 h1 l1) (Node i2 h2 l2) bn}.
Proof.
elim Hh; intro HO_h.
simple induction 1; intro Hd_h; clear H.
simple induction 1; intros HS_h HC_h; clear H.
unfold W_sound in HS_h.
unfold W_complete in HC_h.
elim Hl; intro HO_l.
simple induction 1; intro Hd_l; clear H.
simple induction 1; intros HS_l HC_l; clear H.
unfold W_sound in HS_l.
unfold W_complete in HC_l.
intro Heq.
exists bh.
split.
        (*  OBDT  *)
assumption.
split.
  (* Dim(bh) <= i1 *)
apply le_trans with (Dim h1);
 [ assumption
 | apply gt_le_weak; elim (dim_node_dim_sons i1 h1 l1); auto with v62 ].
split.
       (* Soundness *)
unfold W_sound in |- *.
intros p Def_p; split.
apply Sol_Right.
elim (HS_l p); [ auto with v62 | elim Heq; trivial with v62 ].
elim (HS_h p); [ auto with v62 | elim Heq; trivial with v62 ].
      (* Completeness *)
unfold W_complete in |- *.
intros p H1p H2p.
elim (p_inv_Solution p (Node i1 h1 l1) H1p); intro Hside.
(*-- Case p Solution of l1 ---*)
elim (HC_l p Hside H2p); intro p'; simple induction 1; intros H1p' H2p'.
rewrite Heq; exists p'; auto with v62.
(*-- Case p=(Cons i1 tlp) --*)
elim Hside; intro tlp; simple induction 1; intros Htlp Def_tlp.
elim (HC_h tlp Htlp);
 [ intro p'; simple induction 1; intros H1p' H2p' | idtac ].
exists p'; split;
 [ assumption
 | rewrite Def_tlp; apply Divides_trans with tlp; auto with v62 ].
apply L13 with (Cons i1 tlp);
 [ auto with v62
 | elim Def_tlp; assumption
 | elim Def_tlp; exact (Solution_OBDT_ordered (Node i1 h1 l1) p H1p HO1)
 | trivial with v62 ].
Qed.


Lemma Node_W_Node_i1_gt_i2_neq :
 bh <> bl ->
 {bn : BDT |
 OBDT bn /\
 Dim bn <= Dim (Node i1 h1 l1) /\
 W_sound (Node i1 h1 l1) (Node i2 h2 l2) bn /\
 W_complete (Node i1 h1 l1) (Node i2 h2 l2) bn}.
Proof.
elim Hh; intro HO_h.
simple induction 1; intro Hd_h; clear H.
simple induction 1; intros HS_h HC_h; clear H.
unfold W_sound in HS_h.
unfold W_complete in HC_h.
elim Hl; intro HO_l.
simple induction 1; intro Hd_l; clear H.
simple induction 1; intros HS_l HC_l; clear H.
unfold W_sound in HS_l.
unfold W_complete in HC_l.
intro Hneq.
exists (Node i1 bh bl).
split.
        (*  OBDT  *)
apply order_node; try assumption.
apply gt_le_trans with (Dim h1);
 [ elim (dim_node_dim_sons i1 h1 l1 HO1); trivial with v62 | assumption ].
apply gt_le_trans with (Dim l1);
 [ elim (dim_node_dim_sons i1 h1 l1 HO1); trivial with v62 | assumption ].
split.
  (* Dim(Node(i1,bh,bl)) <= i1 *)
auto with v62.
split.
       (* Soundness *)
unfold W_sound in |- *.
intros p Def_p.
elim (p_inv_Solution p (Node i1 bh bl) Def_p); intro Hside.
elim (HS_l p Hside); auto with v62.
elim Hside; intro tlp; simple induction 1; intros Htlp Def_tlp.
elim (HS_h tlp Htlp); intros H1tlp H2tlp.
rewrite Def_tlp; split; [ auto with v62 | apply L14; auto with v62 ].
      (* Completeness *)
unfold W_complete in |- *.
intros p H1p H2p.
elim (p_inv_Solution p (Node i1 h1 l1) H1p); intro Hside.
elim (HC_l p Hside H2p); intro p'; simple induction 1; intros H1p' H2p'.
exists p'; auto with v62. 
elim Hside; intro tlp; simple induction 1; intros Htlp Def_tlp.
elim (HC_h tlp Htlp);
 [ intro p'; simple induction 1; intros H1p' H2p' | idtac ].
exists (Cons i1 p'); split;
 [ auto with v62
 | rewrite Def_tlp; apply Divides_trans with (Cons i1 tlp); auto with v62 ].
apply L13 with p;
 [ auto with v62
 | assumption
 | exact (Solution_OBDT_ordered (Node i1 h1 l1) p H1p HO1)
 | rewrite Def_tlp; trivial with v62 ].
Qed.


(*----     Definition of h1--i1--l1 Without h2--i2--l2 when i1 > i2     -----*)

Lemma Node_W_Node_i1_gt_i2 :
 {b3 : BDT |
 OBDT b3 /\
 Dim b3 <= Dim (Node i1 h1 l1) /\
 W_sound (Node i1 h1 l1) (Node i2 h2 l2) b3 /\
 W_complete (Node i1 h1 l1) (Node i2 h2 l2) b3}.
Proof.
elim (eq_BDT_decidable bh bl).
exact Node_W_Node_i1_gt_i2_eq. 
exact Node_W_Node_i1_gt_i2_neq.
Qed.

End Greater_i1.


(*----      Lemmas for h1--i1--l1 Without h2--i2--l2 when i1 = i2      ------*)

Section Equal_i1_i2.

Hypothesis Heq_dims : i1 = i2.
Variable bh : BDT.
Hypothesis
  Hh : OBDT bh /\ Dim bh <= Dim h1 /\ W_sound h1 h2 bh /\ W_complete h1 h2 bh.
Variable bl : BDT.
Hypothesis
  Hl : OBDT bl /\ Dim bl <= Dim l1 /\ W_sound l1 l2 bl /\ W_complete l1 l2 bl.

Hint Resolve Heq_dims.


Lemma Node_W_Node_i1_eq_i2_eq :
 bh = bl ->
 {bn : BDT |
 OBDT bn /\
 Dim bn <= Dim (Node i1 h1 l1) /\
 W_sound (Node i1 h1 l1) (Node i2 h2 l2) bn /\
 W_complete (Node i1 h1 l1) (Node i2 h2 l2) bn}.
Proof.
elim Hh; intro HO_h.
simple induction 1; intro Hd_h; clear H.
simple induction 1; intros HS_h HC_h; clear H.
unfold W_sound in HS_h.
unfold W_complete in HC_h.
elim Hl; intro HO_l.
simple induction 1; intro Hd_l; clear H.
simple induction 1; intros HS_l HC_l; clear H.
unfold W_sound in HS_l.
unfold W_complete in HC_l.
intro Heq_sons.
exists bh.
split.
        (*  OBDT  *)
assumption.
split.
  (* Dim(bh) <= i1 *)
apply le_trans with (Dim h1);
 [ assumption
 | apply gt_le_weak; elim (dim_node_dim_sons i1 h1 l1); auto with v62 ].
split.
       (* Soundness *)
unfold W_sound in |- *.
intros p Def_p; split.
apply Sol_Right.
elim (HS_l p); [ auto with v62 | elim Heq_sons; trivial with v62 ].
apply Contra with (Implicant p (Fun l2));
 [ intro H; apply L5 with i2 h2; try assumption | idtac ].
elim Heq_dims; apply Gt_dim_out_of_solution with bh; try assumption.
apply gt_le_trans with (Dim h1);
 [ elim (dim_node_dim_sons i1 h1 l1 HO1); trivial with v62 | assumption ].
elim (HS_l p); [ auto with v62 | elim Heq_sons; assumption ].
      (* Completeness *)
unfold W_complete in |- *.
intros p H1p H2p.
elim (p_inv_Solution p (Node i1 h1 l1) H1p); intro Hside.
(*-- Case p Solution of l1 ---*)
elim (HC_l p Hside);
 [ intro p'; simple induction 1; intros H1p' H2p' | idtac ].
rewrite Heq_sons; exists p'; auto with v62.
apply Contra with (Implicant p (Fun (Node i2 h2 l2)));
 [ intro H; apply L10; try assumption | assumption ].
elim Heq_dims; apply Gt_dim_out_of_solution with l1;
 [ assumption
 | elim (ordered_node_ordered_sons i1 h1 l1 HO1); trivial with v62
 | elim (dim_node_dim_sons i1 h1 l1 HO1); trivial with v62 ].
(*-- Case p=(Cons i1 tlp) --*)
elim Hside; intro tlp; simple induction 1; intros Htlp Def_tlp.
elim (HC_h tlp Htlp);
 [ intro p'; simple induction 1; intros H1p' H2p' | idtac ].
exists p'; split;
 [ assumption
 | rewrite Def_tlp; apply Divides_trans with tlp; auto with v62 ].
apply Contra with (Implicant p (Fun (Node i2 h2 l2)));
 [ intro HC; rewrite Def_tlp; rewrite Heq_dims; apply L2; auto with v62
 | auto with v62 ].
elim Heq_dims; apply gt_le_trans with (Dim h1);
 [ elim (dim_node_dim_sons i1 h1 l1 HO1); trivial with v62
 | apply Head_of_solution_le_dim;
    [ assumption
    | elim (ordered_node_ordered_sons i1 h1 l1 HO1); trivial with v62 ] ].
Qed.

Lemma Node_W_Node_i1_eq_i2_neq :
 bh <> bl ->
 {bn : BDT |
 OBDT bn /\
 Dim bn <= Dim (Node i1 h1 l1) /\
 W_sound (Node i1 h1 l1) (Node i2 h2 l2) bn /\
 W_complete (Node i1 h1 l1) (Node i2 h2 l2) bn}.
Proof.
elim Hh; intro HO_h.
simple induction 1; intro Hd_h; clear H.
simple induction 1; intros HS_h HC_h; clear H.
unfold W_sound in HS_h.
unfold W_complete in HC_h.
elim Hl; intro HO_l.
simple induction 1; intro Hd_l; clear H.
simple induction 1; intros HS_l HC_l; clear H.
unfold W_sound in HS_l.
unfold W_complete in HC_l.
intro Hneq_sons.
exists (Node i1 bh bl).
split.
        (*  OBDT  *)
apply order_node; try assumption.
apply gt_le_trans with (Dim h1);
 [ elim (dim_node_dim_sons i1 h1 l1 HO1); trivial with v62 | assumption ].
apply gt_le_trans with (Dim l1);
 [ elim (dim_node_dim_sons i1 h1 l1 HO1); trivial with v62 | assumption ].
split.
  (* Dim(bh) <= i1 *)
auto with v62.
split.
       (* Soundness *)
unfold W_sound in |- *.
intros p Def_p.
elim (p_inv_Solution p (Node i1 bh bl) Def_p); intro Hside.
(*-- Case p Solution of bl --*)
elim (HS_l p Hside); intros H1p H2p; split; [ auto with v62 | idtac ].
apply Contra with (Implicant p (Fun l2));
 [ intro H; apply L5 with i2 h2; try assumption | assumption ].
elim Heq_dims; apply Gt_dim_out_of_solution with l1;
 [ assumption
 | elim (ordered_node_ordered_sons i1 h1 l1 HO1); trivial with v62
 | apply gt_le_trans with (Dim l1);
    [ elim (dim_node_dim_sons i1 h1 l1 HO1); trivial with v62
    | trivial with v62 ] ].
(*-- Case p=(Cons i1 tlp) --*)
elim Hside; intro tlp; simple induction 1; intros Htlp Def_tlp.
elim (HS_h tlp Htlp); intros H1tlp H2tlp.
rewrite Def_tlp; split; [ auto with v62 | idtac ].
rewrite Heq_dims; apply Contra with (Implicant (Cons i2 tlp) (Fun h2));
 [ intro H3tlp; apply L4 with i2 l2; auto with v62 | idtac ].
apply L14;
 [ elim (ordered_node_ordered_sons i2 h2 l2 HO2); trivial with v62
 | assumption
 | elim (dim_node_dim_sons i2 h2 l2 HO2); trivial with v62 ]. 
      (* Completeness *)
unfold W_complete in |- *.
intros p H1p H2p.
elim (p_inv_Solution p (Node i1 h1 l1) H1p); intro Hside.
(*-- Case p Solution of l1 ---*)
elim (HC_l p Hside);
 [ intro p'; simple induction 1; intros H1p' H2p' | idtac ].
exists p'; auto with v62.
apply Contra with (Implicant p (Fun (Node i2 h2 l2)));
 [ intro H; apply L10; try assumption | assumption ].
elim Heq_dims; apply Gt_dim_out_of_solution with l1;
 [ assumption
 | elim (ordered_node_ordered_sons i1 h1 l1 HO1); trivial with v62
 | elim (dim_node_dim_sons i1 h1 l1 HO1); trivial with v62 ].
(*-- Case p=(Cons i1 tlp) --*)
elim Hside; intro tlp; simple induction 1; intros Htlp Def_tlp.
elim (HC_h tlp Htlp);
 [ intro p'; simple induction 1; intros H1p' H2p' | idtac ].
exists (Cons i1 p'); split;
 [ auto with v62 | rewrite Def_tlp; auto with v62 ].
apply Contra with (Implicant (Cons i2 tlp) (Fun (Node i2 h2 l2)));
 [ intro HC; apply L2; auto with v62
 | pattern i2 at 1 in |- *; elim Heq_dims; elim Def_tlp; auto with v62 ].
elim Heq_dims; apply gt_le_trans with (Dim h1);
 [ elim (dim_node_dim_sons i1 h1 l1 HO1); trivial with v62 | idtac ].
apply Head_of_solution_le_dim;
 [ assumption
 | elim (ordered_node_ordered_sons i1 h1 l1 HO1); trivial with v62 ].
Qed.


Lemma Node_W_Node_i1_eq_i2 :
 {b3 : BDT |
 OBDT b3 /\
 Dim b3 <= Dim (Node i1 h1 l1) /\
 W_sound (Node i1 h1 l1) (Node i2 h2 l2) b3 /\
 W_complete (Node i1 h1 l1) (Node i2 h2 l2) b3}.

Proof.
elim (eq_BDT_decidable bh bl).
exact Node_W_Node_i1_eq_i2_eq. 
exact Node_W_Node_i1_eq_i2_neq.
Qed.

End Equal_i1_i2.

Section Greater_i2.

Hypothesis Hgt : i2 > i1.
Hint Resolve Hgt.

Lemma Node_W_Node_i2_gt_i1 :
 {b3 : BDT |
 OBDT b3 /\
 Dim b3 <= Dim (Node i1 h1 l1) /\
 W_sound (Node i1 h1 l1) l2 b3 /\ W_complete (Node i1 h1 l1) l2 b3} ->
 {b3 : BDT |
 OBDT b3 /\
 Dim b3 <= Dim (Node i1 h1 l1) /\
 W_sound (Node i1 h1 l1) (Node i2 h2 l2) b3 /\
 W_complete (Node i1 h1 l1) (Node i2 h2 l2) b3}.
Proof.
simple induction 1; intros b1_W_l2 Def_b1_W_l2.
elim Def_b1_W_l2; intro Hdef1; simple induction 1; intro Hdef2;
 simple induction 1; intros Hdef3 Hdef4; clear H1; 
 clear H0; clear H; clear Def_b1_W_l2.
exists b1_W_l2.
split; [ assumption | split; [ assumption | split ] ].
(*  Soundness  *)
unfold W_sound in |- *.
unfold W_sound in Hdef3.
intros p Def_p.
elim (Hdef3 p Def_p); intros H1p H2p.
split; [ assumption | idtac ].
apply Contra with (Implicant p (Fun l2));
 [ intro H; apply L5 with i2 h2; try assumption | assumption ].
apply Gt_dim_out_of_solution with (Node i1 h1 l1); auto with v62.
(* Completeness *)
unfold W_complete in |- *.
unfold W_complete in Hdef4.
intros p H1p H2p.
elim (Hdef4 p H1p);
 [ intro p'; simple induction 1; intros H1p' H2p' | idtac ].
exists p'; auto with v62.
apply Contra with (Implicant p (Fun (Node i2 h2 l2)));
 [ intro H; apply L10; try assumption | assumption ].
apply Gt_dim_out_of_solution with (Node i1 h1 l1); auto with v62.
Qed.

End Greater_i2.
End Recursion_W.


Lemma Existence_Op_W :
 forall b1 b2 : BDT,
 OBDT b1 ->
 OBDT b2 ->
 Monotonic (Fun b2) ->
 {b3 : BDT |
 OBDT b3 /\ Dim b3 <= Dim b1 /\ W_sound b1 b2 b3 /\ W_complete b1 b2 b3}.
Proof.
intros b1 b2 Hb1 Hb2; pattern b1, b2 in |- *.
apply Induction2; try assumption; clear Hb1 Hb2 b1 b2.
(* 4 base cases *)
intros b1 HO1 Hmon.
exact (b1_W_Zero b1 HO1).
intros b1 HO1 Hmon.
exact (b1_W_One b1 HO1).
intros i2 h2 l2 HO2 Hmon.
exact (Zero_W_Node i2 h2 l2 HO2).
intros i2 h2 l2 HO2 Hmon.
exact (One_W_Node i2 h2 l2 HO2 Hmon).
(* 3 induction cases *)
    (* i1 > i2 *)
intros i1 i2 Hgt h1 l1 HO1 h2 l2 HO2 Hrec_h Hrec_l Hmon.
elim (Hrec_h Hmon); intros bh Def_bh; clear Hrec_h.
elim (Hrec_l Hmon); intros bl Def_bl; clear Hrec_l.
exact
 (Node_W_Node_i1_gt_i2 i1 i2 h1 h2 l1 l2 HO1 HO2 Hmon Hgt bh Def_bh bl Def_bl).
    (* i1 = i2 *)
intros i1 i2 Heq h1 l1 HO1 h2 l2 HO2 Hrec_h Hrec_l Hmon.
elim (Mon_node_Mon_sons i2 h2 l2 HO2 Hmon); intros Hmon_h2 Hmon_l2.
elim (Hrec_h Hmon_h2); intros bh Def_bh; clear Hrec_h.
elim (Hrec_l Hmon_l2); intros bl Def_bl; clear Hrec_l.
exact
 (Node_W_Node_i1_eq_i2 i1 i2 h1 h2 l1 l2 HO1 HO2 Heq bh Def_bh bl Def_bl).     
    (* i1 < i2 *)
intros i1 i2 Hgt h1 l1 HO1 h2 l2 HO2 Hrec_l Hmon.
elim (Mon_node_Mon_sons i2 h2 l2 HO2 Hmon); intros Hmon_h2 Hmon_l2.
exact (Node_W_Node_i2_gt_i1 i1 i2 h1 h2 l1 l2 HO1 Hgt (Hrec_l Hmon_l2)).
Qed.
