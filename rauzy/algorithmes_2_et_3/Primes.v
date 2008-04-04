(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                Computing a BDT coding the prime implicants               *)
(*      (also called minimal solutions) of a function given by its BDT      *)
(*                                                                          *)
(*            Algorithm designed by A.Rauzy of LaBRI Bordeaux               *)
(*                    restricted to monotonic functions                     *)
(*                                                                          *)
(****************************************************************************)
(*                                 Primes.v                                 *)
(****************************************************************************)

Require Import Prelude_BDT.
Require Import bdd.rauzy.algorithme1.Boolean_functions.
Require Import bdd.rauzy.algorithme1.BDTs.
Require Import Prelude_Paths.
Require Import Prelude_Implicants.
Require Import Prelude_Primes.
Require Import Operator_W.
Require Import Monotony.


(*--------------------------------------------------------------------------*)
(*                Specification of procedures computing Primes      
   An algorithm A is correct iff A(b) is Sound and Complete with respect to b
   for all BDT b. Notation: (Sound b A(b))/\(Complete b A(b))               *)
(*--------------------------------------------------------------------------*)
 
Definition Sound (b1 b2 : BDT) :=
  forall p : Path, Solution p b2 -> Prime p (Fun b1).
Definition Complete (b1 b2 : BDT) :=
  forall p : Path, Prime p (Fun b1) -> Solution p b2.
Definition Correct (b1 b2 : BDT) := Sound b1 b2 /\ Complete b1 b2.


Hint Unfold Correct.


(*---------       Needed properties of the specification         ------------*)

Lemma LC2_S_fac1 :
 forall p1 b1 : BDT,
 Sound b1 p1 ->
 forall b2 b3 : BDT,
 W_sound p1 b2 b3 -> forall p : Path, Solution p b3 -> Prime p (Fun b1).
Proof.
intros p1 b1 Def_p1 b2 b3 Def_b3 p Def_p.
unfold W_sound in Def_b3.
unfold Sound in Def_p1.
apply Def_p1; elim (Def_b3 p Def_p); trivial with v62.
Qed.


Lemma LC2_C_fac1 :
 forall pb1 b1 : BDT,
 Complete b1 pb1 ->
 forall b2 b3 : BDT,
 W_complete pb1 b2 b3 ->
 forall p : Path,
 Prime p (Fun b1) ->
 ~ Implicant p (Fun b2) -> exists p' : Path, Solution p' b3 /\ Divides p' p.
Proof.
intros pb1 b1 Def_pb1 b2 b3 Def_b3 p H1p H2p.
unfold W_complete in Def_b3.
unfold Complete in Def_pb1.
exact (Def_b3 p (Def_pb1 p H1p) H2p).
Qed.


Lemma Zero_complete : forall b : BDT, OBDT b -> Complete b Zero -> b = Zero.
Proof.
intros b Hb.
elim (eq_BDT_decidable b Zero); intro Cas.
elim Cas; trivial with v62.
unfold Complete in |- *; intro H.
elim (Prime_exists b Hb Cas); intros p Def_p.
absurd (Solution p Zero); [ exact (No_solution_Zero p) | exact (H p Def_p) ].
Qed.



(*--------------------------------------------------------------------------*)
(*                  Rauzy's solution for A based on Operaor W               *)
(*             
        A(Zero)= Zero                               (E1)
        A(One) = One                                (E2)
        A(Node(i,l,r)) = Node(i,W(A(l),r),A(r))     (E3)
                                                                            *)
(*--------------------------------------------------------------------------*)


(*--------------        Correctness equations E1 and E2        --------------*)

Lemma BDT2_of_Zero : Sound Zero Zero /\ Complete Zero Zero.
Proof.
split.
(* Soundness *)
unfold Sound in |- *.
intros p H_absurde.
absurd (Solution p Zero); [ exact (No_solution_Zero p) | assumption ].
(* Completeness *)
unfold Complete in |- *; simpl in |- *.
intros p H_absurde.
absurd (Prime p FALSE); [ exact (No_prime_FALSE p) | assumption ].
Qed.


Lemma BDT2_of_One : Sound One One /\ Complete One One.
Proof.
split.
(* Soundness *)
unfold Sound in |- *.
intros p Def_p; unfold Prime in |- *.
split.
apply Implicants_TRUE.
apply Solution_OBDT_ordered with One; trivial with v62.
intros p' H1_p' H2_p'.
rewrite (Solution_of_One_is_Nil p Def_p).
exact (Nil_divides_all p').
(* Completeness *)
unfold Complete in |- *; simpl in |- *.
intros p Def_p.
rewrite (Nil_only_prime_of_TRUE p Def_p).
exact Sol_One.
Qed.


(*---------------------------------------------------------------------------*)
(*----------            Correctness of equation E3               ------------*)
(*---------------------------------------------------------------------------*)


Section Case_recursion.

Variable i : nat.
Variable l r : BDT.

Hypothesis HO : OBDT (Node i l r).
Hint Resolve HO.

Variable pl pr : BDT.

Hypothesis HOpl : OBDT pl.
Hint Resolve HOpl.

Hypothesis HOpr : OBDT pr.
Hint Resolve HOpr.

Hypothesis HDpl : Dim pl <= Dim l.
Hint Resolve HDpl.

Hypothesis HDpr : Dim pr <= Dim r.
Hint Resolve HDpr.

Variable w : BDT.

Hypothesis HOw : OBDT w.
Hint Resolve HOw.

Hypothesis HDw : Dim w <= Dim pl.
Hint Resolve HDw.


(*--------   Proof of the correctness of the optimisation    -------*)
(*                   No need to check left=right                    *)

Lemma Result_Ordered :
 Correct l pl -> Correct r pr -> W_correct pl r w -> OBDT (Node i w pr).
Proof.
intros HCpl HCpr HCw.
apply order_node; auto with v62.
apply gt_le_trans with (Dim l);
 [ elim (dim_node_dim_sons i l r); auto with v62
 | apply le_trans with (Dim pl); auto with v62 ].
apply gt_le_trans with (Dim r);
 [ elim (dim_node_dim_sons i l r); auto with v62 | auto with v62 ].
(*---- ~w=pr -----*)
unfold not in |- *; intro Habsurde.
elim (LT1 w HOw); intro Hcas.
   (* Case w = Zero  *)
absurd (OBDT (Node i l r)); auto with v62.
apply Contra with (l = r);
 [ intro H; clear H | apply ordered_node_neq_sons with i; auto with v62 ].
apply (trans_equal (A:=BDT)) with Zero.
apply Zero_complete;
 [ elim (ordered_node_ordered_sons i l r HO); trivial with v62 | idtac ].
elim (LP2 pl HOpl); [ elim HCpl; auto with v62 | idtac ].
pattern Zero at 2 in |- *; elim Hcas.
elim (Zero_complete r);
 [ elim HCw; trivial with v62
 | elim (ordered_node_ordered_sons i l r HO); trivial with v62
 | elim Hcas; rewrite Habsurde; elim HCpr; trivial with v62 ].
symmetry  in |- *; apply Zero_complete;
 [ elim (ordered_node_ordered_sons i l r HO); trivial with v62
 | elim Hcas; rewrite Habsurde; elim HCpr; trivial with v62 ].
   (* Case w=/=Zero *)
elim Hcas; intros p Def_p. 
absurd (Implicant p (Fun r)). 
elim HCw; unfold W_sound in |- *; intros HCSw HCCw.
elim (HCSw p Def_p); trivial with v62.
apply Prime_implicant.
elim HCpr; unfold Sound in |- *; intros HCSpr HCCpr.
apply HCSpr; elim Habsurde; assumption.
Qed.

Lemma Soundness_right :
 Sound l pl ->
 Sound r pr ->
 W_sound pl r w ->
 forall p : Path, Solution p pr -> Prime p (Fun (Node i l r)).
Proof.
intros HSpl HSpr HSw p Def_p.
unfold Sound in HSpr.
unfold Prime in |- *; split.
(*  Implicant *)
apply L10; [ idtac | auto with v62 ].
apply Gt_dim_out_of_solution with pr; [ assumption | auto with v62 | idtac ].
apply gt_le_trans with (Dim r);
 [ elim (dim_node_dim_sons i l r HO); trivial with v62 | auto with v62 ].
(*  Smallest  *)
intros p' H1p' H2p'.
elim (HSpr p Def_p); intros Hp_Impl Hp_Smallest. 
apply Hp_Smallest; [ idtac | assumption ].
apply (L5 i l r p' H1p').
apply L80 with p; [ assumption | idtac ].
apply Gt_dim_out_of_solution with pr; [ assumption | auto with v62 | idtac ].
apply gt_le_trans with (Dim r);
 [ elim (dim_node_dim_sons i l r HO); trivial with v62 | auto with v62 ].
Qed.

Lemma Soundness_left_impl :
 Sound l pl ->
 W_sound pl r w ->
 forall tl : Path,
 Solution tl w ->
 forall p : Path, p = Cons i tl -> Implicant p (Fun (Node i l r)).
Proof.
intros HSpl HSw tl Def_tl p Def_p.
rewrite Def_p; apply (L2 i l r HO tl).
apply Prime_implicant.
exact (LC2_S_fac1 pl l HSpl r w HSw tl Def_tl).
apply gt_le_trans with (Dim w);
 [ idtac | apply Head_of_solution_le_dim; auto with v62 ].
apply gt_le_trans with (Dim l);
 [ elim (dim_node_dim_sons i l r HO); trivial with v62
 | apply le_trans with (Dim pl); auto with v62 ].
Qed.


Lemma Soundness_left_smallest_order :
 forall tl : Path, Solution tl w -> Ordered (Cons i tl).
Proof.
intros tl Def_tl.
apply Cons_ordered; [ exact (Solution_OBDT_ordered w tl Def_tl HOw) | idtac ].
apply gt_le_trans with (Dim l);
 [ elim (dim_node_dim_sons i l r HO); trivial with v62
 | apply le_trans with (Dim w);
    [ exact (Head_of_solution_le_dim tl w Def_tl HOw)
    | apply le_trans with (Dim pl); auto with v62 ] ].
Qed.


Lemma Soundness_left_smallest_in :
 Correct l pl ->
 Correct r pr ->
 W_correct pl r w ->
 forall tl : Path,
 Solution tl w ->
 forall p : Path,
 p = Cons i tl ->
 forall p' : Path,
 Implicant p' (Fun (Node i l r)) -> Divides p' p -> Of i p' -> Divides p p'.
Proof.
intros HCpl HCpr HCw tl Def_tl p Def_p.
elim HCpl; intros HCSpl HCCpl.
elim HCpr; intros HCSpr HCCpr.
elim HCw; intros HCSw HCCw.
intros p' H1p' H2p' Hi.
rewrite Def_p.
elim (Tail_exists_with_dim_head i w pr) with p p';
 [ intros tl' Def_p'; rewrite Def_p'
 | exact (Result_Ordered HCpl HCpr HCw)
 | rewrite Def_p; auto with v62
 | elim (inv_Implicant p' (Fun (Node i l r)) H1p'); auto with v62
 | assumption
 | assumption ].
apply Divides_tail_divides_cons;
 elim (LC2_S_fac1 pl l HCSpl r w HCSw tl Def_tl); intros H1tl H2tl.
apply H2tl; [ apply (L40 i l r HO tl'); elim Def_p'; assumption | idtac ].
apply Divides_cons_divides_tail with i;
 [ elim Def_p'; elim (inv_Implicant p' (Fun (Node i l r)) H1p');
    trivial with v62
 | exact (Soundness_left_smallest_order tl Def_tl)
 | elim Def_p'; elim Def_p; assumption ].
Qed.


Lemma Soundness_left_smallest_out :
 Monotonic (Fun (Node i l r)) ->
 Correct l pl ->
 Correct r pr ->
 W_correct pl r w ->
 forall tl : Path,
 Solution tl w ->
 forall p : Path,
 p = Cons i tl ->
 forall p' : Path,
 Implicant p' (Fun (Node i l r)) -> Divides p' p -> ~ Of i p' -> Divides p p'.
Proof.
intros Hmon HCpl HCpr HCw tl Def_tl p Def_p.
elim HCpl; intros HCSpl HCCpl.
elim HCpr; intros HCSpr HCCpr.
elim HCw; intros HCSw HCCw.
intros p' H1p' H2p' Hi.
absurd (Implicant tl (Fun r)).
unfold W_sound in HCSw.
elim (HCSw tl Def_tl); trivial with v62.
apply (L9 p');
 [ apply (L8 p' tl i); [ elim Def_p; assumption | assumption ]
 | idtac
 | exact (Solution_OBDT_ordered w tl Def_tl HOw)
 | exact (L5 i l r p' H1p' Hi) ].
elim (LC2_S_fac1 pl l HCSpl r w HCSw tl Def_tl); intros H1tl H2tl.
apply H2tl;
 [ idtac | apply (L8 p' tl i); [ elim Def_p; assumption | assumption ] ].
apply (L15 i l r HO Hmon); [ idtac | exact (L5 i l r p' H1p' Hi) ].
apply (Pth_ord9 i tl);
 [ exact (Soundness_left_smallest_order tl Def_tl)
 | elim (inv_Implicant p' (Fun (Node i l r)) H1p'); trivial with v62
 | apply (L8 p' tl i); [ elim Def_p; assumption | assumption ] ].
Qed.


Lemma Soundness_left :
 Monotonic (Fun (Node i l r)) ->
 Correct l pl ->
 Correct r pr ->
 W_correct pl r w ->
 forall tl : Path,
 Solution tl w ->
 forall p : Path, p = Cons i tl -> Prime p (Fun (Node i l r)).
Proof.
intros Hmon HCpl HCpr HCw tl Def_tl p Def_p.
elim HCpl; intros HCSpl HCCpl.
elim HCpr; intros HCSpr HCCpr.
elim HCw; intros HCSw HCCw.
unfold Sound in HCSpr.
unfold Prime in |- *; split.
(*----- Implicant -----*)
exact (Soundness_left_impl HCSpl HCSw tl Def_tl p Def_p).
(*----- Smallest  -----*)
intros p' H1p' H2p'.
elim (Of_path_dec p' i); intro Hi.
          (*   i in p'   *)
exact
 (Soundness_left_smallest_in HCpl HCpr HCw tl Def_tl p Def_p p' H1p' H2p' Hi).
          (*  i out of p'  *)
exact
 (Soundness_left_smallest_out Hmon HCpl HCpr HCw tl Def_tl p Def_p p' H1p'
    H2p' Hi).
Qed.


Lemma Soundness :
 Monotonic (Fun (Node i l r)) ->
 Correct l pl ->
 Correct r pr -> W_correct pl r w -> Sound (Node i l r) (Node i w pr).
Proof.
intros Hmon HCpl HCpr HCw.
elim HCpl; intros HCSpl HCCpl.
elim HCpr; intros HCSpr HCCpr.
elim HCw; intros HCSw HCCw.
unfold Sound in |- *.
intros p Def_p.
elim (p_inv_Solution p (Node i w pr) Def_p).
(*  Case right (Solution p pr) *)
intro Cas_def_p.
exact (Soundness_right HCSpl HCSpr HCSw p Cas_def_p).
(*  Case left p=(Cons i tl) /\ (Solution tl w) *)
simple induction 1; intro tl; simple induction 1; intros H1tl H2tl; clear H0.
exact (Soundness_left Hmon HCpl HCpr HCw tl H1tl p H2tl).
Qed.


Lemma Completness :
 Correct l pl ->
 Correct r pr -> W_correct pl r w -> Complete (Node i l r) (Node i w pr).
Proof.
intros HCpl HCpr HCw.
elim HCpl; intros HCSpl HCCpl.
elim HCpr; intros HCSpr HCCpr.
elim HCw; intros HCSw HCCw.
unfold Complete in |- *.
intros p Def_p.
elim (Of_path_dec p i); intro Hi.
(*----- Case  (Of i p) -----*)
elim (L4bis i l r HO p Def_p Hi); intro tl; simple induction 1;
 intros H1tl H2tl; clear H.
rewrite H1tl; apply Sol_Left.
elim (LC2_C_fac1 pl l HCCpl r w HCCw tl H2tl);
 [ intro tl'; simple induction 1; intros H1tl' H2tl'; clear H
 | apply (L12 i l r); elim H1tl; exact Def_p ].
elim (Ordered_paths_eq tl' (Solution_OBDT_ordered w tl' H1tl' HOw) tl);
 [ exact H1tl'
 | elim (inv_Implicant tl (Fun l) (Prime_implicant tl (Fun l) H2tl));
    trivial with v62
 | exact H2tl'
 | idtac ]. 
elim H2tl; intros H2tl_impl H2tl_smallest; clear H2tl.
apply H2tl_smallest;
 [ exact
    (Prime_implicant tl' (Fun l) (LC2_S_fac1 pl l HCSpl r w HCSw tl' H1tl'))
 | exact H2tl' ].
(*---- Case ~(Of i p) ------*)
apply Sol_Right.
unfold Complete in HCCpr; apply HCCpr.
exact (L5bis i l r p Def_p Hi).
Qed.


Lemma Correctness :
 Monotonic (Fun (Node i l r)) ->
 Correct l pl ->
 Correct r pr -> W_correct pl r w -> Correct (Node i l r) (Node i w pr).
Proof.
intros Hmon HCpl HCpr HCw.
unfold Correct in |- *; split.
exact (Soundness Hmon HCpl HCpr HCw).
exact (Completness HCpl HCpr HCw).
Qed.

End Case_recursion.


(*--------------------------------------------------------------------------*)
(*             Proof-programming of the algorithm computing a BDT           *)
(*        coding the primes of a boolean function defined by its BDT        *)
(*--------------------------------------------------------------------------*)

 
Theorem Existence_BDT2 :
 forall b1 : BDT,
 OBDT b1 ->
 Monotonic (Fun b1) ->
 {b2 : BDT | OBDT b2 /\ Dim b2 <= Dim b1 /\ Correct b1 b2}.
Proof.
(*----- Structural recursion on b1  ----*)
simple induction b1; clear b1.
intros.
(*---- if b1 = Zero  then b2 = Zero ----*)
exists Zero.
split;
 [ trivial with v62 | split; [ trivial with v62 | exact BDT2_of_Zero ] ].
intros.
(*---- if b1 = One  then b2 = One  ----*)
exists One.
split; [ trivial with v62 | split; [ trivial with v62 | exact BDT2_of_One ] ].
(*---- if b1 = (Node i1 h1 l1) then  .... *)
intros i1 l1 Hrec_l1 r1 Hrec_r1 Node_orded Node_monotonic.
elim Hrec_l1;
 [ intros Prm_l1 Def_Prm_l1; clear Hrec_l1
 | elim (ordered_node_ordered_sons i1 l1 r1 Node_orded); trivial with v62
 | elim (Mon_node_Mon_sons i1 l1 r1 Node_orded Node_monotonic);
    trivial with v62 ].
elim Def_Prm_l1; intro HO_Prm_l1.
simple induction 1; intros HD_Prm_l1 HCorr_Prm_l1; clear H.
elim Hrec_r1;
 [ intros Prm_r1 Def_Prm_r1; clear Hrec_r1
 | elim (ordered_node_ordered_sons i1 l1 r1 Node_orded); trivial with v62
 | elim (Mon_node_Mon_sons i1 l1 r1 Node_orded Node_monotonic);
    trivial with v62 ].
elim Def_Prm_r1; intro HO_Prm_r1.
simple induction 1; intros HD_Prm_r1 HCorr_Prm_r1; clear H.
clear Def_Prm_r1; clear Def_Prm_l1.
elim (Existence_Op_W Prm_l1 r1);
 [ intros Prm_l1_W_r1 Correctness_W
 | assumption
 | elim (ordered_node_ordered_sons i1 l1 r1 Node_orded); trivial with v62
 | elim (Mon_node_Mon_sons i1 l1 r1 Node_orded Node_monotonic);
    trivial with v62 ].
elim Correctness_W; intro HO_Prm_l1_W_r1.
simple induction 1; intros HD_Prm_l1_W_r1 HCorr_Prm_l1_W_r1; clear H.
clear Correctness_W.
   (*   ..... b2 = (Node i1 Prm_l1_W_r1 Prm_r1)  ... *) 
exists (Node i1 Prm_l1_W_r1 Prm_r1); split.
exact
 (Result_Ordered i1 l1 r1 Node_orded Prm_l1 Prm_r1 HO_Prm_l1 HO_Prm_r1
    HD_Prm_l1 HD_Prm_r1 Prm_l1_W_r1 HO_Prm_l1_W_r1 HD_Prm_l1_W_r1
    HCorr_Prm_l1 HCorr_Prm_r1 HCorr_Prm_l1_W_r1).
split;
 [ auto with v62
 | exact
    (Correctness i1 l1 r1 Node_orded Prm_l1 Prm_r1 HO_Prm_l1 HO_Prm_r1
       HD_Prm_l1 HD_Prm_r1 Prm_l1_W_r1 HO_Prm_l1_W_r1 HD_Prm_l1_W_r1
       Node_monotonic HCorr_Prm_l1 HCorr_Prm_r1 HCorr_Prm_l1_W_r1) ].
Qed.
