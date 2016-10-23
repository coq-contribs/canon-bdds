(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*             Definition and properties of reduced Shannon trees           *)
(*                also called Ordered Binary Decision Trees                 *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                  BDTs.v                                  *)
(****************************************************************************)

Require Import Prelude_BDT.
Require Import CanonBDDs.rauzy.algorithme1.Boolean_functions.


Inductive BDT : Set :=
  | Zero : BDT
  | One : BDT
  | Node : nat -> BDT -> BDT -> BDT.


(*-------------        Properties of equality on BDTs        ----------------*)

Lemma neq_Zero_One : Zero <> One.
Proof.
intros; discriminate.
Qed.
Hint Resolve neq_Zero_One.

Lemma neq_One_Zero : One <> Zero.
Proof.
intros; discriminate.
Qed.
Hint Resolve neq_One_Zero.

Lemma neq_Node_One : forall (i : nat) (h l : BDT), Node i h l <> One. 
Proof.
intros; discriminate.
Qed.
Hint Resolve neq_Node_One.

Lemma neq_Node_Zero : forall (i : nat) (h l : BDT), Node i h l <> Zero. 
Proof.
intros; discriminate.
Qed.
Hint Resolve neq_Node_Zero.

Lemma neq_vars_neq_BDTs :
 forall i1 i2 : nat,
 i1 <> i2 -> forall h1 h2 l1 l2 : BDT, Node i1 h1 l1 <> Node i2 h2 l2.
Proof.
unfold not in |- *.
intros i1 i2 Di1i2 h1 h2 l1 l2 H_absurde.
apply Di1i2; injection H_absurde; trivial with arith.
Qed.
Hint Resolve neq_vars_neq_BDTs.

Lemma neq_left_neq_BDTs :
 forall h1 h2 : BDT,
 h1 <> h2 ->
 forall (i1 i2 : nat) (l1 l2 : BDT), Node i1 h1 l1 <> Node i2 h2 l2.
Proof.
unfold not in |- *.
intros i1 i2 Di1i2 h1 h2 l1 l2 H_absurde.
apply Di1i2; injection H_absurde; trivial with arith.
Qed.
Hint Resolve neq_left_neq_BDTs.

Lemma neq_right_neq_BDTs :
 forall l1 l2 : BDT,
 l1 <> l2 ->
 forall (i1 i2 : nat) (h1 h2 : BDT), Node i1 h1 l1 <> Node i2 h2 l2.
Proof.
unfold not in |- *.
intros i1 i2 Di1i2 h1 h2 l1 l2 H_absurde.
apply Di1i2; injection H_absurde; trivial with arith.
Qed.
Hint Resolve neq_right_neq_BDTs.

Lemma eq_BDT_decidable : forall t1 t2 : BDT, {t1 = t2} + {t1 <> t2}.
Proof.
simple induction t1; simple induction t2; auto with arith.
intros n' y' H1 y0' H2.
elim (eq_nat_dec n n'); intro H_var; elim (H y'); intro H_left; elim (H0 y0');
 intro H_right; auto with arith.
(* case equal *)
elim H_right; elim H_left; elim H_var; left; trivial with arith.
Qed.

Lemma Components_eq_nodes_eq :
 forall i1 i2 : nat,
 i1 = i2 ->
 forall h1 h2 l1 l2 : BDT,
 h1 = h2 -> l1 = l2 -> Node i1 h1 l1 = Node i2 h2 l2.
Proof.
intros i1 i2 Hi h1 h2 l1 l2 Hh Hl.
elim Hi; elim Hh; elim Hl; trivial with arith.
Qed.


(*------------   Dimension of a tree = Root variable  ---------------*)

Definition Dim (bdt : BDT) : nat :=
  match bdt return nat with
  | Zero =>
      (* Zero  *)  0
      (* One   *) 
  | One => 0
      (* (Node i bh bl) *) 
  | Node i bh bl => i
  end.


Inductive dim : BDT -> nat -> Prop :=
  | dim_zero : dim Zero 0
  | dim_one : dim One 0
  | dim_node : forall (i : nat) (bh bl : BDT), dim (Node i bh bl) i.
Hint Resolve dim_zero dim_one dim_node.


Lemma dim_Dim : forall (d : nat) (bdt : BDT), dim bdt d -> d = Dim bdt.
Proof.
simple induction 1; simpl in |- *; auto with arith.
Qed.
Hint Resolve dim_Dim.


(*------         Choosing sons of a BDT         ------*)
(*     with respect to a variable and a boolean value *)

Definition Choice (B : BDT) (i : nat) (b : bool) : BDT :=
  match B return BDT with
  | Zero =>
      (* Zero *)  Zero
      (* One  *) 
  | One => One
      (* (Node d bh bl) *) 
  | Node d bh bl =>
      match Compar i d return BDT with
      | case_left pleft => Node d bh bl
      | case_middle pmid =>
          match b return BDT with
          | true =>
              (* true  *)  bh
              (* false *) 
          | false => bl
          end
      | case_right pright => Zero
      end
  end. 

Lemma Choice_invariant :
 forall (t : BDT) (i : nat), i > Dim t -> forall b : bool, t = Choice t i b.
Proof.
simple induction t; try trivial with arith.
intros d bh Hh bl Hl i Hi.
unfold Choice in |- *; elim (Compar i d); trivial with arith.
intro H_absurde.
absurd (i > Dim (Node d bh bl)); trivial with arith.
simpl in |- *; rewrite H_absurde; trivial with arith.
intro H_absurde.
absurd (i > Dim (Node d bh bl)); trivial with arith.
simpl in |- *; auto with arith.
Qed.


Lemma Choice_left :
 forall (i : nat) (bh bl : BDT), bh = Choice (Node i bh bl) i true.
Proof.
intros i bh bl.
unfold Choice in |- *; elim (Compar i i);
 [ intro; absurd (i > i); trivial with arith
 | trivial with arith
 | intro; absurd (i > i); trivial with arith ].  
Qed.


(* Bdt_choice3 *)
Lemma Choice_right :
 forall (i : nat) (bh bl : BDT), bl = Choice (Node i bh bl) i false.
Proof.
intros i bh bl.
unfold Choice in |- *; elim (Compar i i);
 [ intro; absurd (i > i); trivial with arith
 | trivial with arith
 | intro; absurd (i > i); trivial with arith ]. 
Qed.



(*-----------   Ordering of variables of Binary Trees    -----------*)

Inductive OBDT : BDT -> Prop :=
  | order_0 : OBDT Zero
  | order_1 : OBDT One
  | order_node :
      forall bh bl : BDT,
      OBDT bh ->
      OBDT bl ->
      forall i : nat,
      i > Dim bh -> i > Dim bl -> bh <> bl -> OBDT (Node i bh bl).
Hint Resolve order_0 order_1 order_node.


Definition inv_OBDT_dim (bdt : BDT) : Prop :=
  match bdt return Prop with
  | Zero =>
      (* Zero *)  True
      (* One  *) 
  | One => True
      (* Node i bh bl *) 
  | Node i bh bl => i > Dim bh /\ i > Dim bl
  end.


Lemma p_inv_OBDT_dim : forall bdt : BDT, OBDT bdt -> inv_OBDT_dim bdt.
Proof.
simple induction 1; simpl in |- *; auto with arith.
Qed.
Hint Resolve p_inv_OBDT_dim.

Lemma dim_node_dim_sons :
 forall (i : nat) (bh bl : BDT),
 OBDT (Node i bh bl) -> i > Dim bh /\ i > Dim bl.
Proof.
intros i bh bl Node_ordered.
change (inv_OBDT_dim (Node i bh bl)) in |- *; auto with arith.
Qed.


Lemma Dim_node_gt_O :
 forall (i : nat) (bh bl : BDT),
 OBDT (Node i bh bl) -> Dim (Node i bh bl) > 0.
Proof.
intros i bh bl H.
simpl in |- *.
elim (dim_node_dim_sons i bh bl H); intros Hh Hl.
apply gt_le_trans with (m := Dim bh); auto with arith.
Qed.


Inductive node_decomposition (b : BDT) : Prop :=
    node_exist :
      forall (i : nat) (bl bh : BDT),
      Node i bh bl = b -> node_decomposition b.


Lemma Dim_gt_O_node_decomposition :
 forall b : BDT, OBDT b -> Dim b > 0 -> node_decomposition b.
Proof.
simple induction b;
 [ simpl in |- *; intros; absurd (0 > 0); auto with arith
 | simpl in |- *; intros; absurd (0 > 0); auto with arith
 | intros i h Hh l Hl HO Hd; apply node_exist with i l h; trivial with arith ].
Qed.


Definition inv_OBDT_order (bdt : BDT) : Prop :=
  match bdt return Prop with
  | Zero =>
      (* Zero *)  True
      (* One  *) 
  | One => True
      (* Node i bh bl *) 
  | Node i bh bl => OBDT bh /\ OBDT bl
  end.


Lemma p_inv_OBDT_order : forall bdt : BDT, OBDT bdt -> inv_OBDT_order bdt.
Proof.
simple induction 1; simpl in |- *; auto with arith.
Qed.
Hint Resolve p_inv_OBDT_order.


Definition inv_OBDT_neq (bdt : BDT) : Prop :=
  match bdt return Prop with
  | Zero =>
      (* Zero *)  True
      (* One  *) 
  | One => True
      (* Node i bh bl *) 
  | Node i bh bl => bh <> bl
  end.


Lemma p_inv_OBDT_neq : forall bdt : BDT, OBDT bdt -> inv_OBDT_neq bdt.
Proof.
simple induction 1; simpl in |- *; auto with arith.
Qed.
Hint Resolve p_inv_OBDT_neq.


Lemma ordered_node_neq_sons :
 forall (i : nat) (bh bl : BDT), OBDT (Node i bh bl) -> bh <> bl.
Proof.
intros i bh bl Node_ordered.
change (inv_OBDT_neq (Node i bh bl)) in |- *; auto with arith.
Qed.


Lemma ordered_node_a_son_neq_zero :
 forall (i : nat) (bh bl : BDT),
 OBDT (Node i bh bl) -> bh <> Zero \/ bl <> Zero.
Proof.
intros i bh bl HO.
apply deMorgan_or_not.
unfold not in |- *; simple induction 1; intros H1 H2; clear H.  
absurd (bh = bl :>BDT);
 [ exact (ordered_node_neq_sons i bh bl HO)
 | rewrite H1; rewrite H2; trivial with arith ].
Qed.

Lemma ordered_node_ordered_sons :
 forall (i : nat) (bh bl : BDT), OBDT (Node i bh bl) -> OBDT bh /\ OBDT bl.
Proof.
intros i bh bl Node_ordered.
change (inv_OBDT_order (Node i bh bl)) in |- *; auto with arith.
Qed.

Lemma Ordered_node_ordered_restr :
 forall t : BDT,
 OBDT t -> forall i : nat, Dim t <= i -> forall b : bool, OBDT (Choice t i b).
Proof.
simple induction 1; [ auto with arith | auto with arith | idtac ].
clear H t.
intros bl bh H1l H2l H1h H2h i H1i H2i bl_neq_bh j Hj.
unfold Choice in |- *; elim (Compar j i);
 [ auto with arith
 |  (* Case j > i *)
    intro; simple induction b0; trivial with arith
 |  (* Case j = i *)
    intro H_absurd;  (* Case i > j *)
    absurd (Dim (Node i bl bh) > j); auto with arith ].
Qed.

Lemma Choice_dim_decrease :
 forall t : BDT,
 OBDT t -> Dim t > 0 -> forall b : bool, Dim t > Dim (Choice t (Dim t) b).
Proof.
simple induction 1;
 [ simpl in |- *; intro H_abs; absurd (0 > 0); auto with arith
 | simpl in |- *; intro H_abs; absurd (0 > 0); auto with arith
 | idtac ].
clear H t.
intros bl bh HOl Hrecl HOh Hrech i Hi1 Hi2 bh_neq_bl H.
simpl in |- *.
elim (Compar i i);
 [ intro H_abs; absurd (i > i); auto with arith
 | intro Htriv; simple induction b; assumption
 | intro H_abs; absurd (i > i); auto with arith ].
Qed.


Definition Maxdim (b1 b2 : BDT) := Max (Dim b1) (Dim b2).


Lemma Measure_decrease :
 forall t1 : BDT,
 OBDT t1 ->
 Dim t1 > 0 ->
 forall t2 : BDT,
 OBDT t2 ->
 Dim t2 > 0 ->
 forall i : nat,
 i = Maxdim t1 t2 ->
 forall b : bool, i > Maxdim (Choice t1 i b) (Choice t2 i b).
Proof.
intros t1 HO1 Hd1 t2 HO2 Hd2 i Def_i.
elim (Compar (Dim t1) (Dim t2)).
(*------ Case Dim(t1) > Dim(t2) ------*)
intros D1_gt_D2 b.
rewrite Def_i.
unfold Maxdim at 1 2 in |- *.
elim (Choice_invariant t2 (Maxdim t1 t2));
 [ idtac
 | unfold Maxdim in |- *; elim (gt_Max (Dim t1) (Dim t2)); try assumption ].
apply Max_mon_left; try assumption.
unfold Maxdim in |- *; elim (gt_Max (Dim t1) (Dim t2)); try assumption.
apply Choice_dim_decrease; trivial with arith.
(*-----  Case  Dim(t1) = Dim(t2) -----*)
intros D1_eq_D2 b.
rewrite Def_i.
unfold Maxdim at 1 2 in |- *.
apply Max_mon_middle.
unfold Maxdim in |- *; elim (eq_Max (Dim t1) (Dim t2)); trivial with arith.
apply Choice_dim_decrease; trivial with arith.
unfold Maxdim in |- *; elim (Max_sym (Dim t2) (Dim t1)).
elim (eq_Max (Dim t2) (Dim t1));
 [ apply Choice_dim_decrease; trivial with arith
 | symmetry  in |- *; trivial with arith ].
(*-----  Case Dim(t1) < Dim(t2) ------*)
intros D2_gt_D1 b.
rewrite Def_i.
unfold Maxdim at 3 in |- *.
rewrite (Max_sym (Dim t1) (Dim t2)).
elim (gt_Max (Dim t2) (Dim t1)); try assumption.
elim (Choice_invariant t1 (Dim t2)); try assumption.
unfold Maxdim at 3 in |- *.
rewrite (Max_sym (Dim t1) (Dim t2)).
elim (gt_Max (Dim t2) (Dim t1)); try assumption.
unfold Maxdim in |- *.
apply Max_mon_right; try assumption.
apply Choice_dim_decrease; trivial with arith.
Qed.


Section Decrease_induction1.

Variable i1 i2 : nat.
Variable h1 l1 : BDT.
Hypothesis HO1 : OBDT (Node i1 h1 l1).
Variable h2 l2 : BDT.
Hypothesis HO2 : OBDT (Node i2 h2 l2).
Hint Resolve HO1 HO2.


Lemma Decrease_n1n2_h1n2 : i1 > i2 -> Max i1 i2 > Max (Dim h1) i2.
Proof.
intro Hi.
change (Max i1 i2 > Maxdim h1 (Node i2 h2 l2)) in |- *.
rewrite (Choice_left i1 h1 l1).
rewrite (Choice_invariant (Node i2 h2 l2) i1 Hi true).
pattern i1 at 3 4 in |- *; rewrite (gt_Max i1 i2 Hi).
apply Measure_decrease;
 [ trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | trivial with arith ].
Qed.


(* Bdt_order11 *)
Lemma Decrease_n1n2_l1n2 : i1 > i2 -> Max i1 i2 > Max (Dim l1) i2.
Proof.
intro Hi.
change (Max i1 i2 > Maxdim l1 (Node i2 h2 l2)) in |- *.
rewrite (Choice_right i1 h1 l1).
rewrite (Choice_invariant (Node i2 h2 l2) i1 Hi false).
pattern i1 at 3 4 in |- *; rewrite (gt_Max i1 i2 Hi).
apply Measure_decrease;
 [ trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | trivial with arith ].
Qed.

Lemma Decrease_n1n2_h1h2 : i1 = i2 -> Max i1 i2 > Max (Dim h1) (Dim h2).
Proof.
intro Hi.
change (Max i1 i2 > Maxdim h1 h2) in |- *.
rewrite (Choice_left i1 h1 l1).
rewrite (Choice_left i2 h2 l2).
pattern i1 at 3 in |- *; rewrite Hi; pattern i2 at 2 4 in |- *;
 rewrite (le_Max i1 i2).
apply Measure_decrease;
 [ trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | trivial with arith ].
elim Hi; trivial with arith.
Qed.

Lemma Decrease_n1n2_l1l2 : i1 = i2 -> Max i1 i2 > Max (Dim l1) (Dim l2).
Proof.
intro Hi.
change (Max i1 i2 > Maxdim l1 l2) in |- *.
rewrite (Choice_right i1 h1 l1).
rewrite (Choice_right i2 h2 l2).
pattern i1 at 3 in |- *; rewrite Hi; pattern i2 at 2 4 in |- *;
 rewrite (le_Max i1 i2).
apply Measure_decrease;
 [ trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | trivial with arith ].
elim Hi; trivial with arith.
Qed.

Lemma Decrease_n1n2_n1h2 : i2 > i1 -> Max i1 i2 > Max i1 (Dim h2).
Proof.
intro Hi.
change (Max i1 i2 > Maxdim (Node i1 h1 l1) h2) in |- *.
rewrite (Choice_left i2 h2 l2).
rewrite (Choice_invariant (Node i1 h1 l1) i2 Hi true).
pattern i2 at 2 4 in |- *; rewrite (gt_Max i2 i1 Hi).
elim (Max_sym i2 i1); apply Measure_decrease;
 [ trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | rewrite (Max_sym i2 i1); auto with arith ].
Qed.

Lemma Decrease_n1n2_n1l2 : i2 > i1 -> Max i1 i2 > Max i1 (Dim l2).
Proof.
intro Hi.
change (Max i1 i2 > Maxdim (Node i1 h1 l1) l2) in |- *.
rewrite (Choice_right i2 h2 l2).
rewrite (Choice_invariant (Node i1 h1 l1) i2 Hi false).
pattern i2 at 2 4 in |- *; rewrite (gt_Max i2 i1 Hi).
elim (Max_sym i2 i1); apply Measure_decrease;
 [ trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | trivial with arith
 | apply Dim_node_gt_O; trivial with arith
 | rewrite (Max_sym i2 i1); auto with arith ].
Qed.

End Decrease_induction1.



(*----------  Boolean function defined by a Binary Decision Tree  -----------*)

Definition Fun (bdt : BDT) : BF :=
  (fix F (b : BDT) : BF :=
     match b with
     | Zero => FALSE
     | One => TRUE
     | Node n b0 b1 => IF Boolean_functions.F n then F b0 else F b1
     end) bdt.
(* Zero  *) 
(* One   *) 
(* Node(i,bl,bh) *) 


Lemma Fun_node_case_left :
 forall (i : nat) (h l : BDT) (A : Assign),
 true = A i -> Fun (Node i h l) A = Fun h A.
Proof.
intros i h l A.
simpl in |- *; unfold IF_, F in |- *; simple induction 1; trivial with arith.
Qed.


Lemma Fun_node_case_right :
 forall (i : nat) (h l : BDT) (A : Assign),
 false = A i -> Fun (Node i h l) A = Fun l A.
Proof.
intros i h l A.
simpl in |- *; unfold IF_, F in |- *; simple induction 1; trivial with arith.
Qed.


Lemma Sh_exp_dim :
 forall (t : BDT) (i : nat),
 Dim t = i ->
 BF_eq (IF F i then Fun (Choice t i true) else Fun (Choice t i false))
   (Fun t).
Proof.
simple induction t. 
simpl in |- *; intros; apply BF_eq_sym; apply eq_f_iff.
simpl in |- *; intros; apply BF_eq_sym; apply eq_f_iff.
intros j bh H_bh bl H_bl i; simpl in |- *; intro Def_i.
rewrite <- Def_i.
elim (Compar j j); intro.
absurd (j > j); auto with arith. 
apply BF_eq_refl.
absurd (j > j); auto with arith.
Qed.


Lemma Shannon_expansion :
 forall (t : BDT) (i : nat),
 Dim t <= i ->
 BF_eq (IF F i then Fun (Choice t i true) else Fun (Choice t i false))
   (Fun t).
Proof.
intros t i Hi.
elim (le_lt_or_eq (Dim t) i); try assumption.
(* Case i > Dim(t) *)
clear Hi; intro Hi.
elim (Choice_invariant t i); [ idtac | apply lt_gt; assumption ].
elim (Choice_invariant t i); [ idtac | apply lt_gt; assumption ].
apply BF_eq_sym; apply eq_f_iff.
(* Case i = Dim(t) *)
exact (Sh_exp_dim t i).
Qed.


Lemma Dim_is_depvar_max :
 forall t : BDT, OBDT t -> forall i : nat, i > Dim t -> ~ Dep_Var (Fun t) i.
Proof.
simple induction 1.
(*  Case t=Zero  *)
intros.
apply L_Dep_Var2; simpl in |- *.
intro b.
replace FALSE with (Fcst false); auto with arith.
(*  Case t=One  *)
intros.
apply L_Dep_Var2; simpl in |- *.
intro b.
replace TRUE with (Fcst true); auto with arith.
(*  Case t=Node(i,th,tl)  *)
intros th tl HOh Hrec_h HOl Hrec_l i Hil Hih Hneq j Hj.
apply L_Dep_Var2.
intro b.
change
  (BF_eq (Fun (Node i th tl)) (Frestr (IF F i then Fun th else Fun tl) j b))
 in |- *.
apply
 BF_eq_trans
  with
    (f2 := IF Frestr (F i) j b then Frestr (Fun th) j b
           else Frestr (Fun tl) j b);
 [ idtac | apply BF_eq_sym; apply Commute_Frestr_IF ].
apply BF_eq_trans with (f2 := IF F i then Fun th else Fun tl);
 [ auto with arith | apply BF_eq_congruence_op3 ].
   (*   (BF_eq (F i) (Frestr (F i) j b)) *)
pattern (F i) at 1 in |- *.
elim (Frestr_Fi_j i j) with b; [ trivial with arith | idtac ].
unfold not in |- *; intro H_absurde.
simpl in Hj.
absurd (i > i);
 [ trivial with arith | pattern i at 1 in |- *; rewrite H_absurde; assumption ].
   (*   (BF_eq (Fun th) (Frestr (Fun th) j b))  *)
apply L_Dep_Var1.
apply Hrec_h.
simpl in Hj.
apply gt_trans with i; trivial with arith.
   (*   (BF_eq (Fun tl) (Frestr (Fun tl) j b))  *)
apply L_Dep_Var1.
apply Hrec_l.
simpl in Hj.
apply gt_trans with i; trivial with arith.  
Qed.

Remark Fun_sons_dim_nondep :
 forall (i : nat) (h l : BDT),
 OBDT (Node i h l) -> ~ Dep_Var (Fun h) i /\ ~ Dep_Var (Fun l) i.
Proof.
intros i h l HO.
split;
 (apply Dim_is_depvar_max;
   [ elim (ordered_node_ordered_sons i h l HO); trivial with arith
   | elim (dim_node_dim_sons i h l HO); trivial with arith ]).
Qed.

Lemma Choice_Fun_eq_Fun_Choice :
 forall t : BDT,
 OBDT t ->
 forall i : nat,
 Dim t <= i ->
 forall b : bool, BF_eq (Frestr (Fun t) i b) (Fun (Choice t i b)).
Proof.
simple induction t.
(*  t = Zero  *)
simpl in |- *; intros HO i Hi b.
replace FALSE with (Fcst false); auto with arith.
(*  t = One  *)
simpl in |- *; intros HO i Hi b.
replace TRUE with (Fcst true); auto with arith.
(*  t = Node(i,h,l)  *)
intros i h Hrec_h l Hrec_l HO j Hj b.
simpl in Hj.
unfold Choice in |- *; elim (Compar j i).
   (* case j > i *)
intro Hsup.
apply BF_eq_sym; apply L_Dep_Var1; apply Dim_is_depvar_max; auto with arith.
   (* case j = i *)
intro Heq; rewrite Heq; simpl in |- *.
apply
 BF_eq_trans
  with (IF Frestr (F i) i b then Frestr (Fun h) i b else Frestr (Fun l) i b).
apply Commute_Frestr_IF.
elim (Fun_sons_dim_nondep i h l HO); intros.
rewrite Frestr_Fi_i_b.
elim b; unfold Fcst in |- *; simpl in |- *.
apply BF_eq_trans with (Frestr (Fun h) i true);
 [ apply BF_eq_sym; apply eq_if_true_f
 | apply BF_eq_sym; apply L_Dep_Var1; trivial with arith ].
apply BF_eq_trans with (Frestr (Fun l) i false);
 [ apply BF_eq_sym; apply eq_if_false_g
 | apply BF_eq_sym; apply L_Dep_Var1; trivial with arith ].
   (* case j < i *)
intro Habsurde.
absurd (i > j); auto with arith.
Qed.

Lemma Fun_eq_Fun_choice_eq :
 forall t1 : BDT,
 OBDT t1 ->
 forall t2 : BDT,
 OBDT t2 ->
 forall m : nat,
 m = Maxdim t1 t2 ->
 BF_eq (Fun t1) (Fun t2) ->
 forall b : bool, BF_eq (Fun (Choice t1 m b)) (Fun (Choice t2 m b)).
Proof.
intros t1 HO1 t2 HO2 m Def_m Heq b.
apply BF_eq_trans with (Frestr (Fun t1) m b).
apply BF_eq_sym; apply Choice_Fun_eq_Fun_Choice;
 [ assumption
 | rewrite Def_m; unfold Maxdim in |- *; elim (Max_le (Dim t1) (Dim t2));
    trivial with arith ].
apply BF_eq_trans with (Frestr (Fun t2) m b).
apply F_eq_Frestr_eq; trivial with arith.
apply Choice_Fun_eq_Fun_Choice;
 [ assumption
 | rewrite Def_m; unfold Maxdim in |- *; elim (Max_le (Dim t1) (Dim t2));
    trivial with arith ].
Qed.

Lemma Corr_hl_Corr_node :
 forall Op : BF -> BF -> BF,
 Boolean Op ->
 forall b1 b2 : BDT,
 OBDT b1 ->
 OBDT b2 ->
 forall (bh bl : BDT) (i : nat),
 i = Maxdim b1 b2 ->
 BF_eq (Fun bl) (Op (Fun (Choice b1 i false)) (Fun (Choice b2 i false))) ->
 BF_eq (Fun bh) (Op (Fun (Choice b1 i true)) (Fun (Choice b2 i true))) ->
 BF_eq (IF F i then Fun bh else Fun bl) (Op (Fun b1) (Fun b2)).
Proof.
intros Op H_Op b1 b2 H1 H2 bh bl i Def_i Hbl Hbh.
apply
 BF_eq_trans
  with
    (f2 := IF F i then Op (Fun (Choice b1 i true)) (Fun (Choice b2 i true))
           else Op (Fun (Choice b1 i false)) (Fun (Choice b2 i false))).
apply BF_eq_congruence_op3; auto with arith.
apply
 BF_eq_trans
  with
    (f2 := Op
             (IF F i then Fun (Choice b1 i true) else Fun (Choice b1 i false))
             (IF F i then Fun (Choice b2 i true) else Fun (Choice b2 i false))).
apply Commute_if_bool_op2; assumption.
apply BF_eq_congruence_op2; try assumption; apply Shannon_expansion;
 try assumption; rewrite Def_i; unfold Maxdim in |- *;
 elim (Max_le (Dim b1) (Dim b2)); auto with arith.
Qed.



