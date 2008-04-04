(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                        Induction Principles used                         *)
(*                    for the development of two algorithms:                *)
(*   - Computation of the BDT of a boolean formula (Induction1)             *)
(*   - Computation of the Without operator for prime implicants (Induction2)*)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                               Inductions.v                               *)
(****************************************************************************)


Require Import Prelude_BDT.
Require Import bdd.rauzy.algorithme1.BDTs.


(*-----------   Measure on couples of BDTs  for termination    -------------*)

Definition R (b1 b2 c1 c2 : BDT) := Maxdim b1 b2 > Maxdim c1 c2.
Definition f (p : BDT * BDT) := Maxdim (fst p) (snd p).
Definition Rp (b c : BDT * BDT) := f b < f c.
Definition Lower := Rp.
Definition Pr1 (c : BDT * BDT) := fst c.
Definition Pr2 (c : BDT * BDT) := snd c.
Definition Cpl (b1 b2 : BDT) := pair b1 b2.

Lemma Lower_well_founded : well_founded Lower.
Proof.
change (well_founded (ltof (BDT * BDT) f)) in |- *.
exact (well_founded_ltof (BDT * BDT) f).
Qed.


(*--------------           Pattern Matchings         --------------------*)

Lemma BDT_matching1 :
 forall P : BDT -> BDT -> Set,
 (forall b2 : BDT, P Zero b2) ->
 (forall b2 : BDT, P One b2) ->
 (forall b1 : BDT, P b1 Zero) ->
 (forall b1 : BDT, P b1 One) ->
 (forall (i1 i2 : nat) (h1 h2 l1 l2 : BDT), P (Node i1 h1 l1) (Node i2 h2 l2)) ->
 forall b1 b2 : BDT, P b1 b2.
Proof.
intros P H1 H2 H3 H4 H5.
simple induction b1; try assumption.
intros i1 h1 H6 l1 H7.
simple induction b2; auto with v62.
Qed.

Lemma BDT_matching2 :
 forall P : BDT -> BDT -> Set,
 (forall b1 : BDT, P b1 Zero) ->
 (forall b1 : BDT, P b1 One) ->
 (forall (i2 : nat) (h2 l2 : BDT), P Zero (Node i2 h2 l2)) ->
 (forall (i2 : nat) (h2 l2 : BDT), P One (Node i2 h2 l2)) ->
 (forall (i1 i2 : nat) (h1 h2 l1 l2 : BDT), P (Node i1 h1 l1) (Node i2 h2 l2)) ->
 forall b1 b2 : BDT, P b1 b2.
Proof.
intros P H1 H2 H3 H4 H5.
simple induction b2; auto with v62.
intros i2 h2 H6 l2 H7.
elim b1; auto with v62.
Qed.


(*---------     Well founded induction on couples of BDTs       ------------*)

Lemma Wf_ind1 :
 forall P : BDT -> BDT -> Set,
 (forall b1 b2 : BDT,
  (forall c1 c2 : BDT, R b1 b2 c1 c2 -> P c1 c2) -> P b1 b2) ->
 forall b1 b2 : BDT, P b1 b2.
Proof.
intros P H b1 b2.
change ((fun c : BDT * BDT => P (fst c) (snd c)) (b1, b2)) in |- *.
apply
 well_founded_induction
  with
    (A := (BDT * BDT)%type)
    (R := Rp)
    (P := fun c : BDT * BDT => P (fst c) (snd c))
    (a := (b1, b2)).
change (well_founded (ltof (BDT * BDT) f)) in |- *. 
exact (well_founded_ltof (BDT * BDT) f).
clear b1 b2.
intros x Hx.
apply H.
intros c1 c2 Hc.
apply Hx with (y := (c1, c2)).
unfold Rp, f in |- *; simpl in |- *; unfold R in Hc; assumption.
Qed.


(*---------      Induction Principle for Algorithm1:Bexp->BDT  -----------*)
(*     First formulation hiding in Choice the 3 cases Node Node           *)


Lemma ind1_ind2 :
 forall (P : BDT -> BDT -> Set) (b1 : BDT),
 OBDT b1 ->
 Dim b1 > 0 ->
 forall b2 : BDT,
 OBDT b2 ->
 Dim b2 > 0 ->
 (forall c1 c2 : BDT, R b1 b2 c1 c2 -> OBDT c1 -> OBDT c2 -> P c1 c2) ->
 forall b : bool, P (Choice b1 (Maxdim b1 b2) b) (Choice b2 (Maxdim b1 b2) b).
Proof.
intros P b1 HOb1 HDb1 b2 HOb2 HDb2 H_ind1 b.
apply H_ind1;
 [ unfold R in |- *; apply Measure_decrease; trivial with v62
 | apply Ordered_node_ordered_restr; try assumption;
    elim (Max_le (Dim b1) (Dim b2)); unfold Maxdim in |- *; 
    auto with v62
 | apply Ordered_node_ordered_restr; try assumption;
    elim (Max_le (Dim b1) (Dim b2)); unfold Maxdim in |- *; 
    auto with v62 ].
Qed.
 

Lemma Induction1 :
 forall P : BDT -> BDT -> Set,
 (forall b2 : BDT, OBDT b2 -> P Zero b2) ->
 (forall b2 : BDT, OBDT b2 -> P One b2) ->
 (forall b1 : BDT, OBDT b1 -> P b1 Zero) ->
 (forall b1 : BDT, OBDT b1 -> P b1 One) ->
 (forall b1 b2 : BDT,
  OBDT b1 ->
  Dim b1 > 0 ->
  OBDT b2 ->
  Dim b2 > 0 ->
  forall i : nat,
  i = Maxdim b1 b2 ->
  P (Choice b1 i true) (Choice b2 i true) ->
  P (Choice b1 i false) (Choice b2 i false) -> P b1 b2) ->
 forall b1 b2 : BDT, OBDT b1 -> OBDT b2 -> P b1 b2.
Proof.
intros P H1 H2 H3 H4 H5 b1 b2.
pattern b1, b2 in |- *.
apply Wf_ind1.
clear b1 b2.
intros b1 b2.
pattern b1, b2 in |- *.
apply BDT_matching1; auto with v62.
clear b1 b2.
intros i1 i2 h1 h2 l1 l2 Hn1n2 n1_ordered n2_ordered.
apply H5 with (i := Max i1 i2); try assumption; try apply Dim_node_gt_O;
 try trivial with v62.
(* P(n1\i=true,n2\i=true) *)
change
  (P (Choice (Node i1 h1 l1) (Maxdim (Node i1 h1 l1) (Node i2 h2 l2)) true)
     (Choice (Node i2 h2 l2) (Maxdim (Node i1 h1 l1) (Node i2 h2 l2)) true))
 in |- *.
apply ind1_ind2; try assumption; apply Dim_node_gt_O; auto with v62.
(* P(n1\i=false,n2\i=false) *)
change
  (P (Choice (Node i1 h1 l1) (Maxdim (Node i1 h1 l1) (Node i2 h2 l2)) false)
     (Choice (Node i2 h2 l2) (Maxdim (Node i1 h1 l1) (Node i2 h2 l2)) false))
 in |- *.
apply ind1_ind2; try assumption; apply Dim_node_gt_O; auto with v62.
Qed.

(*---------------        Second formulation       ----------------------*)
(*             The three cases Node Node are apparent                   *)

Lemma Induction1' :
 forall P : BDT -> BDT -> Set,
 (forall b2 : BDT, OBDT b2 -> P Zero b2) ->
 (forall b2 : BDT, OBDT b2 -> P One b2) ->
 (forall b1 : BDT, OBDT b1 -> P b1 Zero) ->
 (forall b1 : BDT, OBDT b1 -> P b1 One) ->
 (forall i1 i2 : nat,
  i1 > i2 ->
  forall h1 l1 : BDT,
  OBDT (Node i1 h1 l1) ->
  forall h2 l2 : BDT,
  OBDT (Node i2 h2 l2) ->
  P h1 (Node i2 h2 l2) ->
  P l1 (Node i2 h2 l2) -> P (Node i1 h1 l1) (Node i2 h2 l2)) ->
 (forall i1 i2 : nat,
  i1 = i2 ->
  forall h1 l1 : BDT,
  OBDT (Node i1 h1 l1) ->
  forall h2 l2 : BDT,
  OBDT (Node i2 h2 l2) ->
  P h1 h2 -> P l1 l2 -> P (Node i1 h1 l1) (Node i2 h2 l2)) ->
 (forall i1 i2 : nat,
  i2 > i1 ->
  forall h1 l1 : BDT,
  OBDT (Node i1 h1 l1) ->
  forall h2 l2 : BDT,
  OBDT (Node i2 h2 l2) ->
  P (Node i1 h1 l1) h2 ->
  P (Node i1 h1 l1) l2 -> P (Node i1 h1 l1) (Node i2 h2 l2)) ->
 forall b1 b2 : BDT, OBDT b1 -> OBDT b2 -> P b1 b2.
Proof.
intros P H1 H2 H3 H4 H5 H6 H7 b1 b2.
pattern b1, b2 in |- *.
apply Wf_ind1.
clear b1 b2; intros b1 b2; pattern b1, b2 in |- *.
apply BDT_matching1; auto with v62.
intros i1 i2 h1 h2 l1 l2 Hn1n2 Hn1 Hn2.
elim (Compar i1 i2); intro Hi.
(* case i1 > i2 *)
apply H5; auto with v62.
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_h1n2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | elim (ordered_node_ordered_sons i1 h1 l1 Hn1); auto with v62
 | assumption ].
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_l1n2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | elim (ordered_node_ordered_sons i1 h1 l1 Hn1); auto with v62
 | assumption ].
(* case i1 = i2 *)
apply H6; auto with v62.
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_h1h2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | elim (ordered_node_ordered_sons i1 h1 l1 Hn1); auto with v62
 | elim (ordered_node_ordered_sons i2 h2 l2 Hn2); auto with v62 ].
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_l1l2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | elim (ordered_node_ordered_sons i1 h1 l1 Hn1); auto with v62
 | elim (ordered_node_ordered_sons i2 h2 l2 Hn2); auto with v62 ].
(* case i2 > i1 *)
apply H7; auto with v62.
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_n1h2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | assumption
 | elim (ordered_node_ordered_sons i2 h2 l2 Hn2); auto with v62 ].
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_n1l2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | assumption
 | elim (ordered_node_ordered_sons i2 h2 l2 Hn2); auto with v62 ].
Qed.


Axiom
  Induction1_prop :
    forall P : BDT -> BDT -> Prop,
    (forall b2 : BDT, OBDT b2 -> P Zero b2) ->
    (forall b2 : BDT, OBDT b2 -> P One b2) ->
    (forall b1 : BDT, OBDT b1 -> P b1 Zero) ->
    (forall b1 : BDT, OBDT b1 -> P b1 One) ->
    (forall b1 b2 : BDT,
     OBDT b1 ->
     Dim b1 > 0 ->
     OBDT b2 ->
     Dim b2 > 0 ->
     forall i : nat,
     i = Maxdim b1 b2 ->
     P (Choice b1 i true) (Choice b2 i true) ->
     P (Choice b1 i false) (Choice b2 i false) -> P b1 b2) ->
    forall b1 b2 : BDT, OBDT b1 -> OBDT b2 -> P b1 b2.


(*----------  Induction Principle for Algorithm2:BDT->BDT->BDT     --------*)
(*                           (Operator Without)                            *)

Lemma Induction2 :
 forall P : BDT -> BDT -> Set,
 (forall b1 : BDT, OBDT b1 -> P b1 Zero) ->
 (forall b1 : BDT, OBDT b1 -> P b1 One) ->
 (forall (i2 : nat) (h2 l2 : BDT),
  OBDT (Node i2 h2 l2) -> P Zero (Node i2 h2 l2)) ->
 (forall (i2 : nat) (h2 l2 : BDT),
  OBDT (Node i2 h2 l2) -> P One (Node i2 h2 l2)) ->
 (forall i1 i2 : nat,
  i1 > i2 ->
  forall h1 l1 : BDT,
  OBDT (Node i1 h1 l1) ->
  forall h2 l2 : BDT,
  OBDT (Node i2 h2 l2) ->
  P h1 (Node i2 h2 l2) ->
  P l1 (Node i2 h2 l2) -> P (Node i1 h1 l1) (Node i2 h2 l2)) ->
 (forall i1 i2 : nat,
  i1 = i2 ->
  forall h1 l1 : BDT,
  OBDT (Node i1 h1 l1) ->
  forall h2 l2 : BDT,
  OBDT (Node i2 h2 l2) ->
  P h1 h2 -> P l1 l2 -> P (Node i1 h1 l1) (Node i2 h2 l2)) ->
 (forall i1 i2 : nat,
  i2 > i1 ->
  forall h1 l1 : BDT,
  OBDT (Node i1 h1 l1) ->
  forall h2 l2 : BDT,
  OBDT (Node i2 h2 l2) ->
  P (Node i1 h1 l1) l2 -> P (Node i1 h1 l1) (Node i2 h2 l2)) ->
 forall b1 b2 : BDT, OBDT b1 -> OBDT b2 -> P b1 b2.
Proof.
intros P H1 H2 H3 H4 H5 H6 H7 b1 b2.
pattern b1, b2 in |- *.
apply Wf_ind1.
clear b1 b2; intros b1 b2; pattern b1, b2 in |- *.
apply BDT_matching2; auto with v62.
intros i1 i2 h1 h2 l1 l2 Hn1n2 Hn1 Hn2.
elim (Compar i1 i2); intro Hi.
(* case i1 > i2 *)
apply H5; auto with v62.
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_h1n2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | elim (ordered_node_ordered_sons i1 h1 l1 Hn1); auto with v62
 | assumption ].
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_l1n2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | elim (ordered_node_ordered_sons i1 h1 l1 Hn1); auto with v62
 | assumption ].
(* case i1 = i2 *)
apply H6; auto with v62.
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_h1h2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | elim (ordered_node_ordered_sons i1 h1 l1 Hn1); auto with v62
 | elim (ordered_node_ordered_sons i2 h2 l2 Hn2); auto with v62 ].
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_l1l2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | elim (ordered_node_ordered_sons i1 h1 l1 Hn1); auto with v62
 | elim (ordered_node_ordered_sons i2 h2 l2 Hn2); auto with v62 ].
(* case i2 > i1 *)
apply H7; auto with v62.
apply Hn1n2;
 [ unfold R, Maxdim in |- *; simpl in |- *;
    exact (Decrease_n1n2_n1l2 i1 i2 h1 l1 Hn1 h2 l2 Hn2 Hi)
 | assumption
 | elim (ordered_node_ordered_sons i2 h2 l2 Hn2); auto with v62 ].
Qed.
