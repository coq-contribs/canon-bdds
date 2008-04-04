(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                  Binary Decision Trees (BDTs)                            *)
(*               MacMillan's "Proof" of canonicity of BDDs                  *)
(*                                                                          *)
(****************************************************************************)
(*                                  BDTs.v                                  *)
(****************************************************************************)

Require Import bdd.canonicite.Boolean_functions.
Require Import Vars.

Inductive BDT (n : nat) : Set :=
  | zero : BDT n
  | one : BDT n
  | node : Var n -> BDT n -> BDT n -> BDT n.

Definition Dimension (n : nat) (bdt : BDT n) : nat :=
  match bdt return nat with
  | zero =>
      (* zero  *)  0
      (* one   *) 
  | one => 0
      (* (node i bl bh) *) 
  | node xi bl bh => Order n xi
  end.

Inductive dimension (n : nat) : BDT n -> nat -> Prop :=
  | dim_zero : dimension n (zero n) 0
  | dim_one : dimension n (one n) 0
  | dim_node :
      forall (xi : Var n) (bl bh : BDT n),
      dimension n (node n xi bl bh) (Order n xi).
Hint Resolve dim_zero dim_one dim_node.


Lemma dim_functional :
 forall (n d : nat) (bdt : BDT n), dimension n bdt d -> d = Dimension n bdt.
Proof.
simple induction 1; simpl in |- *; auto with arith bdd.
Qed.
Hint Resolve dim_functional.


Inductive node_decomposition (n : nat) (bdt : BDT n) (d : nat) : Prop :=
    node_exist :
      forall (x : Var n) (bl bh : BDT n),
      Order n x = d -> node n x bl bh = bdt -> node_decomposition n bdt d.

Let dim_inv (n : nat) (bdt : BDT n) (d : nat) : Prop :=
  match d return Prop with
  | O =>
      (* O *)  zero n = bdt \/ one n = bdt
      (* S k *) 
  | S k => node_decomposition n bdt d
  end.

Lemma p_dim_inv :
 forall (n d : nat) (bdt : BDT n), dimension n bdt d -> dim_inv n bdt d.
Proof.
simple induction 1; simpl in |- *; auto with arith bdd.
intros.
elim (Order_S n xi).
intros x E; rewrite E; simpl in |- *.
apply node_exist with xi bl bh; auto with arith bdd.
Qed.
Hint Resolve p_dim_inv.

Lemma dim_Dim :
 forall (n : nat) (bdt : BDT n), dimension n bdt (Dimension n bdt).
Proof.
intro n.
simple induction bdt; simpl in |- *; auto with arith bdd.
Qed.
Hint Resolve dim_Dim.

Lemma Exist_dim :
 forall (n : nat) (bdt : BDT n), exists d : nat, dimension n bdt d.
Proof.
intros n bdt.
exists (Dimension n bdt); auto with arith bdd.
Qed.

Lemma Dim_le_n : forall (n d : nat) (bdt : BDT n), Dimension n bdt <= n.
Proof.
simple induction bdt; simpl in |- *; auto with arith bdd.
Qed.
Hint Resolve Dim_le_n.


Inductive BDT_eq (n : nat) : BDT n -> BDT n -> Prop :=
  | BDT_eq_0 : BDT_eq n (zero n) (zero n)
  | BDT_eq_1 : BDT_eq n (one n) (one n)
  | BDT_eq_node :
      forall (bl1 bl2 bh1 bh2 : BDT n) (xi1 xi2 : Var n),
      BDT_eq n bl1 bl2 ->
      BDT_eq n bh1 bh2 ->
      eq_Var n xi1 xi2 -> BDT_eq n (node n xi1 bl1 bh1) (node n xi2 bl2 bh2).
Hint Resolve BDT_eq_0 BDT_eq_1 BDT_eq_node.

Definition inv_BDT_eq (n : nat) (bdt1 : BDT n) : BDT n -> Prop :=
  match bdt1 return (BDT n -> Prop) with
  | zero =>
      (* zero *) 
      fun bdt2 : BDT n =>
      match bdt2 return Prop with
      | zero =>
          (* zero *)  True
          (* one  *) 
      | one => False
          (* node *) 
      | node x2 b2l b2h => False
      end
      (* one  *) 
  | one =>
      fun bdt2 : BDT n =>
      match bdt2 return Prop with
      | zero =>
          (* zero *)  False
          (* one  *) 
      | one => True
          (* node *) 
      | node x2 b2l b2h => False
      end
      (* node *) 
  | node x1 b1l b1h =>
      fun bdt2 : BDT n =>
      match bdt2 return Prop with
      | zero =>
          (* zero *)  False
          (* one  *) 
      | one => False
          (* node *) 
      | node x2 b2l b2h =>
          (BDT_eq n b1l b2l /\ BDT_eq n b1h b2h) /\ eq_Var n x1 x2
      end
  end.

Lemma p_inv_BDT_eq :
 forall (n : nat) (bdt1 bdt2 : BDT n),
 BDT_eq n bdt1 bdt2 -> inv_BDT_eq n bdt1 bdt2. 
Proof.
simple induction 1; simpl in |- *; auto with arith bdd.
Qed.
Hint Resolve p_inv_BDT_eq.

Lemma ne_zero_one : forall n : nat, ~ BDT_eq n (zero n) (one n).
Proof.
unfold not in |- *.
intros n H_absurde.
change (inv_BDT_eq n (zero n) (one n)) in |- *; auto with arith bdd.
Qed.
Hint Resolve ne_zero_one.

Lemma ne_zero_node :
 forall (n : nat) (x2 : Var n) (b2l b2h : BDT n),
 ~ BDT_eq n (zero n) (node n x2 b2l b2h).
Proof.
unfold not in |- *.
intros n x2 b2l b2h H_absurde.
change (inv_BDT_eq n (zero n) (node n x2 b2l b2h)) in |- *;
 auto with arith bdd.
Qed.
Hint Resolve ne_zero_node.

Lemma ne_one_zero : forall n : nat, ~ BDT_eq n (one n) (zero n).
Proof.
unfold not in |- *.
intros n H_absurde.
change (inv_BDT_eq n (one n) (zero n)) in |- *; auto with arith bdd.
Qed.
Hint Resolve ne_one_zero.

Lemma ne_one_node :
 forall (n : nat) (x2 : Var n) (b2l b2h : BDT n),
 ~ BDT_eq n (one n) (node n x2 b2l b2h).
Proof.
unfold not in |- *.
intros n x2 b2l b2h H_absurde.
change (inv_BDT_eq n (one n) (node n x2 b2l b2h)) in |- *;
 auto with arith bdd.
Qed.
Hint Resolve ne_one_node.

Lemma inv_BDT_eq_node :
 forall (n : nat) (x1 x2 : Var n) (b1l b1h b2l b2h : BDT n),
 BDT_eq n (node n x1 b1l b1h) (node n x2 b2l b2h) ->
 (BDT_eq n b1l b2l /\ BDT_eq n b1h b2h) /\ eq_Var n x1 x2.
Proof.
intros n x1 x2 b1l b1h b2l b2h node1_eq_node2.
change (inv_BDT_eq n (node n x1 b1l b1h) (node n x2 b2l b2h)) in |- *;
 auto with arith bdd.
Qed.

Lemma ne_node_zero :
 forall (n : nat) (x1 : Var n) (b1l b1h : BDT n),
 ~ BDT_eq n (node n x1 b1l b1h) (zero n).
Proof.
unfold not in |- *.
intros n x1 b1l b1h H_absurde.
change (inv_BDT_eq n (node n x1 b1l b1h) (zero n)) in |- *;
 auto with arith bdd.
Qed.
Hint Resolve ne_node_zero.

Lemma ne_node_one :
 forall (n : nat) (x1 : Var n) (b1l b1h : BDT n),
 ~ BDT_eq n (node n x1 b1l b1h) (one n).
Proof.
unfold not in |- *.
intros n x1 b1l b1h H_absurde.
change (inv_BDT_eq n (node n x1 b1l b1h) (one n)) in |- *;
 auto with arith bdd.
Qed.
Hint Resolve ne_node_one.

Inductive OBDT (n : nat) : BDT n -> Prop :=
  | order_0 : OBDT n (zero n)
  | order_1 : OBDT n (one n)
  | order_node :
      forall (xi : Var n) (bl bh : BDT n),
      OBDT n bl ->
      OBDT n bh ->
      Order n xi > Dimension n bl ->
      Order n xi > Dimension n bh ->
      ~ BDT_eq n bl bh -> OBDT n (node n xi bl bh).

Hint Resolve order_0 order_1 order_node.

Definition inv_OBDT_Order (n : nat) (bdt : BDT n) : Prop :=
  match bdt return Prop with
  | zero =>
      (* zero *)  True
      (* one  *) 
  | one => True
      (* node xi bl bh *) 
  | node xi bl bh =>
      Order n xi > Dimension n bl /\ Order n xi > Dimension n bh
  end.

Lemma p_inv_OBDT_order :
 forall (n : nat) (bdt : BDT n), OBDT n bdt -> inv_OBDT_Order n bdt.
Proof.
simple induction 1; simpl in |- *; auto with arith bdd.
Qed.
Hint Resolve p_inv_OBDT_order.

Definition inv_OBDT_eq (n : nat) (bdt : BDT n) : Prop :=
  match bdt return Prop with
  | zero =>
      (* zero *)  True
      (* one  *) 
  | one => True
      (* node xi bl bh *) 
  | node xi bl bh => ~ BDT_eq n bl bh
  end.

Lemma p_inv_OBDT_eq :
 forall (n : nat) (bdt : BDT n), OBDT n bdt -> inv_OBDT_eq n bdt.
Proof.
simple induction 1; simpl in |- *; auto with arith bdd.
Qed.
Hint Resolve p_inv_OBDT_eq.

Definition inv_OBDT_bl (n : nat) (bdt : BDT n) : Prop :=
  match bdt return Prop with
  | zero =>
      (* zero *)  True
      (* one  *) 
  | one => True
      (* node xi bl bh *) 
  | node xi bl bh => OBDT n bl
  end.

Lemma p_inv_OBDT_bl :
 forall (n : nat) (bdt : BDT n), OBDT n bdt -> inv_OBDT_bl n bdt.
Proof.
simple induction 1; simpl in |- *; auto with arith bdd.
Qed.
Hint Resolve p_inv_OBDT_bl.


Definition inv_OBDT_bh (n : nat) (bdt : BDT n) : Prop :=
  match bdt return Prop with
  | zero =>
      (* zero *)  True
      (* one  *) 
  | one => True
      (* node xi bl bh *) 
  | node xi bl bh => OBDT n bh
  end.

Lemma p_inv_OBDT_bh :
 forall (n : nat) (bdt : BDT n), OBDT n bdt -> inv_OBDT_bh n bdt.
Proof.
simple induction 1; simpl in |- *; auto with arith bdd.
Qed.
Hint Resolve p_inv_OBDT_bh.

Lemma Dim_node_Dim_bh :
 forall (n : nat) (bl bh : BDT n) (xi : Var n),
 OBDT n (node n xi bl bh) ->
 forall dn dh : nat,
 dimension n (node n xi bl bh) dn -> dimension n bh dh -> dn > dh.
Proof.
intros n bl bh xi H_OBDT dn dh Def_dn Def_dh.
replace dn with (Dimension n (node n xi bl bh)); try symmetry  in |- *;
 auto with arith bdd.
replace dh with (Dimension n bh); try symmetry  in |- *; auto with arith bdd.
simpl in |- *.
cut (inv_OBDT_Order n (node n xi bl bh)); auto with arith bdd.
simpl in |- *; simple induction 1; auto with arith bdd.
Qed.

Lemma Dim_node_Dim_bl :
 forall (n : nat) (bl bh : BDT n) (xi : Var n),
 OBDT n (node n xi bl bh) ->
 forall dn dl : nat,
 dimension n (node n xi bl bh) dn -> dimension n bl dl -> dn > dl.
Proof.
intros n bl bh xi H_OBDT dn dl Def_dn Def_dl.
replace dn with (Dimension n (node n xi bl bh)); try symmetry  in |- *;
 auto with arith bdd.
replace dl with (Dimension n bl); try symmetry  in |- *; auto with arith bdd.
simpl in |- *.
cut (inv_OBDT_Order n (node n xi bl bh)); auto with arith bdd.
simpl in |- *; simple induction 1; auto with arith bdd.
Qed.


(********************         From BDT to BF             *******************)

Definition Fun (n : nat) (bdt : BDT n) : BF n :=
  (fix F (b : BDT n) : BF n :=
     match b with
     | zero => fun _ : Assign n => false
     | one => fun _ : Assign n => true
     | node v b0 b1 => fun A : Assign n => if A v then F b1 A else F b0 A
     end) bdt.
(* zero  *) 
(* one   *) 
(* node xi bl bh *) 
(* true *) 
(* false *) 

Lemma ne_Fzero_Fone :
 forall n : nat, ~ BF_eq n (Fun n (zero n)) (Fun n (one n)).
Proof.
intro n.
simpl in |- *.
unfold not, BF_eq in |- *.
intro H_absurd.
absurd (false = true); auto with bool.
apply H_absurd; exact (fun x : Var n => true).
Qed.
Hint Resolve ne_Fzero_Fone.
 
Lemma ne_Fone_Fzero :
 forall n : nat, ~ BF_eq n (Fun n (one n)) (Fun n (zero n)).
Proof.
intro n.
unfold not in |- *; intro H1.
cut (~ BF_eq n (Fun n (zero n)) (Fun n (one n))); auto with arith bdd.
Qed.
Hint Resolve ne_Fone_Fzero.

Lemma Restr_node_Restr_low :
 forall (n : nat) (x : Var n) (bl bh : BDT n),
 BF_eq n (Restr n (Fun n (node n x bl bh)) x false)
   (Restr n (Fun n bl) x false).
Proof.
intros n x bl bh.
unfold BF_eq in |- *.
intro A.
unfold Restr at 1 in |- *; simpl in |- *.
unfold Upd at 1 in |- *; simpl in |- *.
elim (eq_Var_dec n x x).
intro x_eq_x.
change (Restr n (Fun n bl) x false A = Restr n (Fun n bl) x false A) in |- *;
 auto with arith bdd.
intro H_absurde.
absurd (eq_Var n x x); auto with arith bdd.
Qed.
Hint Resolve Restr_node_Restr_low.

Lemma Restr_node_Restr_high :
 forall (n : nat) (x : Var n) (bl bh : BDT n),
 BF_eq n (Restr n (Fun n (node n x bl bh)) x true)
   (Restr n (Fun n bh) x true).
Proof.
intros n x bl bh.
unfold BF_eq in |- *.
intro A.
unfold Restr at 1 in |- *; simpl in |- *.
unfold Upd at 1 in |- *; simpl in |- *.
elim (eq_Var_dec n x x).
intro x_eq_x.
change (Restr n (Fun n bh) x true A = Restr n (Fun n bh) x true A) in |- *;
 auto with arith bdd.
intro H_absurde.
absurd (eq_Var n x x); auto with arith bdd.
Qed.
Hint Resolve Restr_node_Restr_high.

(*---------------------------------------------------------------------------*)
Lemma vars_sup_dim_non_dep :
 forall (n : nat) (bdt : BDT n),
 OBDT n bdt ->
 forall x : Var n,
 Order n x > Dimension n bdt ->
 forall b : bool, BF_eq n (Restr n (Fun n bdt) x b) (Fun n bdt).
(*---------------------------------------------------------------------------*)
Proof.
cut
 (forall (n k : nat) (bdt : BDT n),
  OBDT n bdt ->
  Dimension n bdt <= k ->
  forall x : Var n,
  Order n x > Dimension n bdt ->
  forall b : bool, BF_eq n (Restr n (Fun n bdt) x b) (Fun n bdt)).
intros Coupure n bdt bdt_OBDT x x_gt_Dim_bdt b.
apply Coupure with (k := n); auto with arith bdd.
simple induction k.
       (* k = O *)
intros bdt bdt_OBDT Dim_O x gt_Orderx_Dim b.
cut (dim_inv n bdt 0).
unfold dim_inv in |- *.
do 2 simple induction 1; simpl in |- *; unfold BF_eq in |- *;
 auto with arith bdd.
apply p_dim_inv.
elimtype (Dimension n bdt = 0); try apply sym_equal; auto with arith bdd.
     (* k -> (S k) *)
intros l Hl bdt H_OBDT H_dim x H_order_x b.
elim (le_nSm_le_nm_or_eq l (Dimension n bdt)); try assumption;
 intro H_dim_bdt; auto with arith bool bdd.
cut (node_decomposition n bdt (S l)).
simple induction 1.
intros xi bl bh Order_xi decomp_bdt.
unfold BF_eq in |- *.
intro A.
elim decomp_bdt; simpl in |- *.
unfold Restr in |- *; simpl in |- *.
elimtype (A xi = Upd n A x b xi).
elim (A xi).
(*---- (Fun n bh (Upd n A x b))=(Fun n bh A) ---*)
change (Restr n (Fun n bh) x b A = Fun n bh A) in |- *.
cut (forall A : Assign n, Restr n (Fun n bh) x b A = Fun n bh A);
 auto with arith bool bdd.
change (BF_eq n (Restr n (Fun n bh) x b) (Fun n bh)) in |- *.
apply Hl.
change (inv_OBDT_bh n (node n xi bl bh)) in |- *; rewrite decomp_bdt;
 auto with arith bool bdd.
apply gt_S_le.
replace (S l) with (Dimension n bdt).
apply Dim_node_Dim_bh with n bl bh xi; try rewrite decomp_bdt;
 auto with arith bool bdd.
apply gt_trans with (m := Dimension n bdt); auto with arith bool bdd.
apply Dim_node_Dim_bh with n bl bh xi; try rewrite decomp_bdt;
 auto with arith bool bdd.
(*---- (Fun n bl (Upd n A x b))=(Fun n bl A) ----*)
change (Restr n (Fun n bl) x b A = Fun n bl A) in |- *.
cut (forall A : Assign n, Restr n (Fun n bl) x b A = Fun n bl A);
 auto with arith bool bdd.
change (BF_eq n (Restr n (Fun n bl) x b) (Fun n bl)) in |- *.
apply Hl.
change (inv_OBDT_bl n (node n xi bl bh)) in |- *; rewrite decomp_bdt;
 auto with arith bool bdd.
apply gt_S_le.
replace (S l) with (Dimension n bdt).
apply Dim_node_Dim_bl with n bl bh xi; try rewrite decomp_bdt;
 auto with arith bool bdd.
apply gt_trans with (m := Dimension n bdt); auto with arith bool bdd.
apply Dim_node_Dim_bl with n bl bh xi; try rewrite decomp_bdt;
 auto with arith bool bdd.
(*---- (A xi)=(Upd n A x b xi) -----*)
symmetry  in |- *; apply Upd_xi_xj.
unfold eq_Var, not in |- *; intro E.
generalize H_order_x; rewrite H_dim_bdt; elim E; rewrite Order_xi.
intro; apply (gt_irrefl (S l)); trivial.
(*---- (node_decomposition n bdt (S l)) -----*)
change (dim_inv n bdt (S l)) in |- *.
rewrite <- H_dim_bdt; auto with arith bool bdd.
Qed.

Lemma vars_sup_dim_non_dep2 :
 forall (n : nat) (bdt : BDT n),
 OBDT n bdt ->
 forall x : Var n, Order n x > Dimension n bdt -> ~ Dep_Var n (Fun n bdt) x.
Proof.
intros n bdt On x H_Order_x.
unfold not in |- *.
intro H_absurde.
cut (~ BF_eq n (Restr n (Fun n bdt) x true) (Restr n (Fun n bdt) x false));
 auto with arith bool bdd.
unfold not in |- *.
intro H; apply H.
apply BF_eq_trans with (f2 := Fun n bdt).
apply vars_sup_dim_non_dep; auto with arith bool bdd.
apply BF_eq_sym; apply vars_sup_dim_non_dep; auto with arith bool bdd.
Qed.

(*--------------------------------------------------------------------------*)
  Lemma BDT_iso_BDF_eq :
   forall (n : nat) (bdt1 bdt2 : BDT n),
   BDT_eq n bdt1 bdt2 -> BF_eq n (Fun n bdt1) (Fun n bdt2).
(*--------------------------------------------------------------------------*)
Proof.
simple induction 1; auto with arith bool bdd.
intros bl1 bl2 bh1 bh2 xi1 xi2 bl1_iso_bl2 Fbl1_eq_Fbl2 bh1_iso_bh2
 Fbh1_eq_Fbh2 xi1_eq_xi2.
unfold BF_eq in |- *; intro A; simpl in |- *.
elimtype (A xi1 = A xi2).
unfold BF_eq in Fbh1_eq_Fbh2.
unfold BF_eq in Fbl1_eq_Fbl2.
elim (A xi1); auto with arith bool bdd.
pattern xi2 in |- *; apply Proof_irrelevance with n xi1;
 auto with arith bool bdd.
Qed.
Hint Resolve BDT_iso_BDF_eq.

(*--------------------------------------------------------------------------*)
  Lemma Fun_eq_OBDT_eq :
   forall (n : nat) (bdt1 bdt2 : BDT n),
   OBDT n bdt1 ->
   OBDT n bdt2 -> BF_eq n (Fun n bdt1) (Fun n bdt2) -> BDT_eq n bdt1 bdt2.
(*--------------------------------------------------------------------------*)
Proof.
intros n bdt1 bdt2 H H0 H1.
cut
 (forall (n k : nat) (bdt1 bdt2 : BDT n),
  Dimension n bdt1 <= k ->
  Dimension n bdt2 <= k ->
  OBDT n bdt1 ->
  OBDT n bdt2 -> BF_eq n (Fun n bdt1) (Fun n bdt2) -> BDT_eq n bdt1 bdt2).
intro Fun_eq_OBDT_eq_dimk.
apply Fun_eq_OBDT_eq_dimk with (k := n); auto with arith bool bdd.
(* Cut *)
clear H1 H0 H bdt2 bdt1 n.
intro n.
simple induction k.
(*------ k= O ------*)
intros bdt1 bdt2 H_dim1 H_dim2 H_OBDT1 H_OBDT2.
cut (dim_inv n bdt1 0).
cut (dim_inv n bdt2 0).
unfold dim_inv in |- *.
do 4 simple induction 1; auto with arith bool bdd.
intro Fone_eq_Fzero.
unfold BF_eq, Fun in Fone_eq_Fzero.
absurd (true = false); auto with arith bool bdd.
apply Fone_eq_Fzero; exact (fun x : Var n => true).
intro Fzero_eq_Fone.
unfold BF_eq, Fun in Fzero_eq_Fone.
absurd (false = true); auto with arith bool bdd.
apply Fzero_eq_Fone; exact (fun x : Var n => true).
(* (dim_inv n bdt2 O) *)
cut (0 = Dimension n bdt2); try apply le_n_O_eq; try assumption.
intro Dim_bdt2.
apply p_dim_inv; rewrite Dim_bdt2; auto with arith bool bdd.
(* (dim_inv n bdt1 O) *)
cut (0 = Dimension n bdt1); try apply le_n_O_eq; try assumption.
intro Dim_bdt1.
apply p_dim_inv; rewrite Dim_bdt1; auto with arith bool bdd.
(*------  k -> (S k) -------*)
intros l Hl.
intros bdt1 bdt2 Dim_bdt1 Dim_bdt2 OBDT1 OBDT2 Fun1_eq_Fun2.
elim (le_nSm_le_nm_or_eq l (Dimension n bdt1)); try assumption;
 elim (le_nSm_le_nm_or_eq l (Dimension n bdt2)); try assumption;
 auto with arith bool bdd.
(*--- Case Dim(bdt1)<=l Dim(bdt2)=(S l) ---*)
intros Dim2_eq_Sl Dim1_le_l.
cut (node_decomposition n bdt2 (S l)).
simple induction 1.
intros x b2l b2h Order_x decomp_bdt2.
absurd (BDT_eq n b2l b2h). 
    (* ~(BDT_eq n b2l b2h) *)
change (inv_OBDT_eq n (node n x b2l b2h)) in |- *.
replace (node n x b2l b2h) with bdt2; auto with arith bool bdd.
    (* (BDT_eq n b2l b2h) *)
cut (OBDT n bdt2); try assumption.
rewrite <- decomp_bdt2.
intro OBDT_node_b2.
cut (OBDT n b2l).
intro OBDT_b2l.
cut (OBDT n b2h).
intro OBDT_b2h.
apply Hl; auto with arith bool bdd.
      (* (le (Dimension n b2l) l) *)
apply gt_S_le.
replace (S l) with (Dimension n bdt2).
apply Dim_node_Dim_bl with n b2l b2h x; auto with arith bool bdd.
rewrite decomp_bdt2; auto with arith bool bdd.
      (* (le (Dimension n b2h) l) *)
apply gt_S_le.
replace (S l) with (Dimension n bdt2).
apply Dim_node_Dim_bh with n b2l b2h x; auto with arith bool bdd.
rewrite decomp_bdt2; auto with arith bool bdd.
      (* (BF_eq n (Fun n b2l) (Fun n b2h)) *)
apply BF_eq_trans with (Fun n bdt1).
apply BF_eq_trans with (Restr n (Fun n bdt1) x false).
apply BF_eq_trans with (Restr n (Fun n bdt2) x false);
 auto with arith bool bdd.
apply BF_eq_trans with (Restr n (Fun n (node n x b2l b2h)) x false).
  (* (BF_eq n (Fun n b2l) (Restr n (Fun n (node n x b2l b2h)) x false)) *)
apply BF_eq_trans with (Restr n (Fun n b2l) x false);
 auto with arith bool bdd.
(* Use: Restr_node_Restr_low *)
apply BF_eq_sym.
apply vars_sup_dim_non_dep; auto with arith bool bdd.
  (* (gt (Order n x) (Dimension n b2l)) *)
rewrite Order_x.
rewrite <- Dim2_eq_Sl.
rewrite <- decomp_bdt2.
apply Dim_node_Dim_bl with (n := n) (bl := b2l) (bh := b2h) (xi := x);
 auto with arith bool bdd. 
rewrite decomp_bdt2; auto with arith bool bdd.
  (*  (BF_eq n (Restr n (Fun n bdt1) x false) (Fun n bdt1)) *)
apply vars_sup_dim_non_dep; auto with arith bool bdd.
rewrite Order_x.
apply gt_le_trans with (n := S l) (m := l) (p := Dimension n bdt1);
 auto with arith bool bdd.
  (*  (BF_eq n (Fun n bdt1) (Fun n b2h)) *)
apply BF_eq_trans with (Restr n (Fun n bdt1) x true).
apply BF_eq_sym; apply vars_sup_dim_non_dep; auto with arith bool bdd.
rewrite Order_x.
apply gt_le_trans with (n := S l) (m := l) (p := Dimension n bdt1);
 auto with arith bool bdd.
  (* (BF_eq n (Restr n (Fun n bdt1) x true) (Fun n b2h)) *)
apply BF_eq_trans with (Restr n (Fun n bdt2) x true);
 auto with arith bool bdd.
apply BF_eq_trans with (Restr n (Fun n (node n x b2l b2h)) x true). 
rewrite decomp_bdt2; auto with arith bool bdd.
  (*  (BF_eq n (Restr n (Fun n (node n x b2l b2h)) x true) (Fun n b2h)) *)
apply BF_eq_trans with (Restr n (Fun n b2h) x true); auto with arith bool bdd.
(* Use: Restr_node_Restr_high *)
apply vars_sup_dim_non_dep; auto with arith bool bdd.
  (* (gt (Order n x) (Dimension n b2h)) *)
rewrite Order_x.
rewrite <- Dim2_eq_Sl.
rewrite <- decomp_bdt2.
apply Dim_node_Dim_bh with (n := n) (bl := b2l) (bh := b2h) (xi := x);
 auto with arith bool bdd. 
      (* (OBDT n b2h) *)
change (inv_OBDT_bh n (node n x b2l b2h)) in |- *; auto with arith bool bdd.
      (* (OBDT n b2l) *)
change (inv_OBDT_bl n (node n x b2l b2h)) in |- *; auto with arith bool bdd.
    (* (node_decomposition n bdt2 (S l)) *)
change (dim_inv n bdt2 (S l)) in |- *; rewrite <- Dim2_eq_Sl;
 auto with arith bool bdd.
(*--- Case Dim(bdt1)=Sl Dim(bdt2)<=l ---*) 
intros Dim2_le_l Dim1_eq_Sl.
cut (node_decomposition n bdt1 (S l)).
simple induction 1.
intros x b1l b1h Order_x decomp_bdt1.
absurd (BDT_eq n b1l b1h).
    (* ~(BDT_eq n b1l b1h) *)
change (inv_OBDT_eq n (node n x b1l b1h)) in |- *.
replace (node n x b1l b1h) with bdt1; auto with arith bool bdd.
    (* (BDT_eq n b1l b1h) *)
cut (OBDT n bdt1); try assumption.
rewrite <- decomp_bdt1.
intro OBDT_node_b1.
cut (OBDT n b1l).
intro OBDT_b1l.
cut (OBDT n b1h).
intro OBDT_b1h.
apply Hl; auto with arith bool bdd.
      (* (le (Dimension n b1l) l) *)
apply gt_S_le.
replace (S l) with (Dimension n bdt1).
apply Dim_node_Dim_bl with n b1l b1h x; auto with arith bool bdd.
rewrite decomp_bdt1; auto with arith bool bdd.
      (* (le (Dimension n b1h) l) *)
apply gt_S_le.
replace (S l) with (Dimension n bdt1).
apply Dim_node_Dim_bh with n b1l b1h x; auto with arith bool bdd.
rewrite decomp_bdt1; auto with arith bool bdd.
      (* (BF_eq n (Fun n b1l) (Fun n b1h)) *)
apply BF_eq_trans with (Fun n bdt2).
apply BF_eq_trans with (Restr n (Fun n bdt2) x false).
apply BF_eq_trans with (Restr n (Fun n bdt1) x false);
 auto with arith bool bdd.
apply BF_eq_trans with (Restr n (Fun n (node n x b1l b1h)) x false).
  (* (BF_eq n (Fun n b1l) (Restr n (Fun n (node n x b1l b1h)) x false)) *)
apply BF_eq_trans with (Restr n (Fun n b1l) x false);
 auto with arith bool bdd.
(* Use: Restr_node_Restr_low *)
apply BF_eq_sym.
apply vars_sup_dim_non_dep; auto with arith bool bdd.
  (* (gt (Order n x) (Dimension n b1l)) *)
rewrite Order_x.
rewrite <- Dim1_eq_Sl.
rewrite <- decomp_bdt1.
apply Dim_node_Dim_bl with (n := n) (bl := b1l) (bh := b1h) (xi := x);
 auto with arith bool bdd. 
rewrite decomp_bdt1; auto with arith bool bdd.
  (* (BF_eq n (Restr n (Fun n bdt2) x false) (Fun n bdt2)) *)
apply vars_sup_dim_non_dep; auto with arith bool bdd.
rewrite Order_x.
apply gt_le_trans with (n := S l) (m := l) (p := Dimension n bdt2);
 auto with arith bool bdd.
  (* (BF_eq n (Fun n bdt2) (Fun n b1h)) *)
apply BF_eq_trans with (Restr n (Fun n bdt2) x true).
apply BF_eq_sym; apply vars_sup_dim_non_dep; auto with arith bool bdd.
rewrite Order_x.
apply gt_le_trans with (n := S l) (m := l) (p := Dimension n bdt2);
 auto with arith bool bdd.
  (* (BF_eq n (Restr n (Fun n bdt2) x true) (Fun n b1h)) *)
apply BF_eq_trans with (Restr n (Fun n bdt1) x true);
 auto with arith bool bdd.
apply BF_eq_trans with (Restr n (Fun n (node n x b1l b1h)) x true). 
rewrite decomp_bdt1; auto with arith bool bdd.
  (*  (BF_eq n (Restr n (Fun n (node n x b1l b1h)) x true) (Fun n b1h)) *)
apply BF_eq_trans with (Restr n (Fun n b1h) x true); auto with arith bool bdd.
(* Use: Restr_node_Restr_high *)
apply vars_sup_dim_non_dep; auto with arith bool bdd.
  (* (gt (Order n x) (Dimension n b1h)) *)
rewrite Order_x.
rewrite <- Dim1_eq_Sl.
rewrite <- decomp_bdt1.
apply Dim_node_Dim_bh with (n := n) (bl := b1l) (bh := b1h) (xi := x);
 auto with arith bool bdd. 
      (* (OBDT n b1h) *)
change (inv_OBDT_bh n (node n x b1l b1h)) in |- *; auto with arith bool bdd.
      (* (OBDT n b1l) *)
change (inv_OBDT_bl n (node n x b1l b1h)) in |- *; auto with arith bool bdd.
    (* (node_decomposition n bdt1 (S l)) *)
change (dim_inv n bdt1 (S l)) in |- *; rewrite <- Dim1_eq_Sl;
 auto with arith bool bdd.
(*-----    Case Dim(bdt1)=Sl Dim(bdt2)=Sl    ------*) 
intros Dim2_eq_Sl Dim1_eq_Sl.
cut (node_decomposition n bdt1 (S l)).
simple induction 1.
intros x1 b1l b1h Order_x1 decomp_bdt1.
cut (node_decomposition n bdt2 (S l)).
simple induction 1.
intros x2 b2l b2h Order_x2 decomp_bdt2.
cut (OBDT n bdt1); try assumption.
rewrite <- decomp_bdt1.
intro OBDT_node_b1.
cut (OBDT n bdt2); try assumption.
rewrite <- decomp_bdt2.
intro OBDT_node_b2.
cut (eq_Var n x1 x2).
intro x1_eq_x2.
apply BDT_eq_node; auto with arith bool bdd.
   (* (BDT_eq n b1l b2l) *)
cut (OBDT n b1l).
intro OBDT_b1l.
cut (OBDT n b2l).
intro OBDT_b2l.
apply Hl; auto with arith bool bdd. 
       (* (le (Dimension n b1l) l) *)
apply gt_S_le.
replace (S l) with (Dimension n bdt1).
apply Dim_node_Dim_bl with n b1l b1h x1; auto with arith bool bdd.
rewrite decomp_bdt1; auto with arith bool bdd.
       (* (le (Dimension n b2l) l) *)
apply gt_S_le.
replace (S l) with (Dimension n bdt2).
apply Dim_node_Dim_bl with n b2l b2h x2; auto with arith bool bdd.
rewrite decomp_bdt2; auto with arith bool bdd.
       (* (BF_eq n (Fun n b1l) (Fun n b2l)) *)
apply BF_eq_trans with (Restr n (Fun n (node n x1 b1l b1h)) x1 false).
apply BF_eq_sym.
apply BF_eq_trans with (Restr n (Fun n b1l) x1 false);
 auto with arith bool bdd.
apply vars_sup_dim_non_dep; auto with arith bool bdd.
  (* (gt (Order n x1) (Dimension n b1l)) *)
rewrite Order_x1.
rewrite <- Dim1_eq_Sl.
rewrite <- decomp_bdt1.
apply Dim_node_Dim_bl with (n := n) (bl := b1l) (bh := b1h) (xi := x1);
 auto with arith bool bdd.
  (*  (BF_eq n (Restr n (Fun n (node n x1 b1l b1h)) x1 false) (Fun n b2l)) *)
apply BF_eq_trans with (Restr n (Fun n (node n x2 b2l b2h)) x2 false).
rewrite decomp_bdt1; rewrite decomp_bdt2.
pattern x2 in |- *.
apply Proof_irrelevance with (n := n) (x := x1); auto with arith bool bdd.
apply BF_eq_trans with (Restr n (Fun n b2l) x2 false);
 auto with arith bool bdd.
apply vars_sup_dim_non_dep; auto with arith bool bdd.
  (* (gt (Order n x2) (Dimension n b2l)) *)
rewrite Order_x2.
rewrite <- Dim2_eq_Sl.
rewrite <- decomp_bdt2.
apply Dim_node_Dim_bl with (n := n) (bl := b2l) (bh := b2h) (xi := x2);
 auto with arith bool bdd.
       (*  (OBDT n b2l) *)
change (inv_OBDT_bl n (node n x2 b2l b2h)) in |- *; auto with arith bool bdd.
       (*  (OBDT n b1l) *)
change (inv_OBDT_bl n (node n x1 b1l b1h)) in |- *; auto with arith bool bdd.
  (* (BDT_eq n b1h b2h) *)
cut (OBDT n b1h).
intro OBDT_b1h.
cut (OBDT n b2h).
intro OBDT_b2h.
apply Hl; auto with arith bool bdd.
       (* (le (Dimension n b1h) l) *)
apply gt_S_le.
replace (S l) with (Dimension n bdt1).
apply Dim_node_Dim_bh with n b1l b1h x1; auto with arith bool bdd.
rewrite decomp_bdt1; auto with arith bool bdd.
       (* (le (Dimension n b2h) l) *)
apply gt_S_le.
replace (S l) with (Dimension n bdt2).
apply Dim_node_Dim_bh with n b2l b2h x2; auto with arith bool bdd.
rewrite decomp_bdt2; auto with arith bool bdd.
       (* (BF_eq n (Fun n b1h) (Fun n b2h)) *)
apply BF_eq_trans with (Restr n (Fun n (node n x1 b1l b1h)) x1 true).
apply BF_eq_sym.
apply BF_eq_trans with (Restr n (Fun n b1h) x1 true);
 auto with arith bool bdd.
apply vars_sup_dim_non_dep; auto with arith bool bdd.
  (* (gt (Order n x1) (Dimension n b1h)) *)
rewrite Order_x1.
rewrite <- Dim1_eq_Sl.
rewrite <- decomp_bdt1.
apply Dim_node_Dim_bh with (n := n) (bl := b1l) (bh := b1h) (xi := x1);
 auto with arith bool bdd.
  (*  (BF_eq n (Restr n (Fun n (node n x1 b1l b1h)) x1 true) (Fun n b2h)) *)
apply BF_eq_trans with (Restr n (Fun n (node n x2 b2l b2h)) x2 true).
rewrite decomp_bdt1; rewrite decomp_bdt2.
pattern x2 in |- *.
apply Proof_irrelevance with (n := n) (x := x1); auto with arith bool bdd.
apply BF_eq_trans with (Restr n (Fun n b2h) x2 true);
 auto with arith bool bdd.
apply vars_sup_dim_non_dep; auto with arith bool bdd.
  (* (gt (Order n x2) (Dimension n b2h)) *)
rewrite Order_x2.
rewrite <- Dim2_eq_Sl.
rewrite <- decomp_bdt2.
apply Dim_node_Dim_bh with (n := n) (bl := b2l) (bh := b2h) (xi := x2);
 auto with arith bool bdd.
       (*  (OBDT n b2h) *)
change (inv_OBDT_bh n (node n x2 b2l b2h)) in |- *; auto with arith bool bdd.
       (*  (OBDT n b1h) *)
change (inv_OBDT_bh n (node n x1 b1l b1h)) in |- *; auto with arith bool bdd.
      (* (eq_Var n x1 x2) *)
apply same_order_eq_Var with (k := S l); auto with arith bool bdd.
    (* (node_decomposition n bdt2 (S l)) *)
change (dim_inv n bdt2 (S l)) in |- *; rewrite <- Dim2_eq_Sl;
 auto with arith bool bdd.
    (* (node_decomposition n bdt1 (S l)) *)
change (dim_inv n bdt1 (S l)) in |- *; rewrite <- Dim1_eq_Sl;
 auto with arith bool bdd.
Qed.

(*---------------------------------------------------------------------------*)
  Lemma Dim_is_Greatest_Dep_Var :
   forall (n : nat) (bdt : BDT n),
   OBDT n bdt ->
   Dimension n bdt > 0 ->
   exists x : Var n,
     Order n x = Dimension n bdt /\ Greatest_Dep_Var n (Fun n bdt) x.
(*---------------------------------------------------------------------------*)
Proof.
intros n bdt On Dim.
cut (node_decomposition n bdt (Dimension n bdt)).
simple induction 1.
intros x bl bh Order_x decomp_bdt.
exists x; split; auto with arith bool bdd.
apply Def_GreatestDV.
(*-----  (Dep_Var n (Fun n bdt) x)----- *)
unfold Dep_Var in |- *.
cut (~ BF_eq n (Fun n bl) (Fun n bh)).
intro H1.
unfold not in H1.
unfold not in |- *.
intro H_absurde.
apply H1.
    (* (BF_eq n (Fun n bl) (Fun n bh)) *)
apply BF_eq_trans with (n := n) (f2 := Restr n (Fun n bh) x true).
apply
 BF_eq_trans with (n := n) (f2 := Restr n (Fun n (node n x bl bh)) x true);
 auto with arith bool bdd. 
apply
 BF_eq_trans with (n := n) (f2 := Restr n (Fun n (node n x bl bh)) x false);
 [ idtac | apply BF_eq_sym; rewrite decomp_bdt; auto ].
apply BF_eq_trans with (n := n) (f2 := Restr n (Fun n bl) x false);
 [ idtac | apply BF_eq_sym; auto ].
apply BF_eq_sym.
 (*  (BF_eq n (Restr n (Fun n bl) x false) (Fun n bl)) *)
apply vars_sup_dim_non_dep.
change (inv_OBDT_bl n (node n x bl bh)) in |- *.
rewrite decomp_bdt; auto with arith bool bdd.
rewrite Order_x.
apply Dim_node_Dim_bl with (n := n) (bl := bl) (bh := bh) (xi := x);
 try rewrite decomp_bdt; auto with arith bool bdd.
 (*  (BF_eq n (Restr n (Fun n bh) x true) (Fun n bh))  *)
apply vars_sup_dim_non_dep.
change (inv_OBDT_bh n (node n x bl bh)) in |- *.
rewrite decomp_bdt; auto with arith bool bdd.
rewrite Order_x.
apply Dim_node_Dim_bh with (n := n) (bl := bl) (bh := bh) (xi := x);
 try rewrite decomp_bdt; auto with arith bool bdd.
 (* ~(BF_eq n (Fun n bl) (Fun n bh)) *)
apply Contra with (Q := BDT_eq n bl bh).
intro Fbl_eq_Fbh; apply Fun_eq_OBDT_eq.
change (inv_OBDT_bl n (node n x bl bh)) in |- *; rewrite decomp_bdt;
 auto with arith bool bdd.
change (inv_OBDT_bh n (node n x bl bh)) in |- *; rewrite decomp_bdt;
 auto with arith bool bdd.
auto with arith bool bdd.
change (inv_OBDT_eq n (node n x bl bh)) in |- *; rewrite decomp_bdt;
 auto with arith bool bdd.
 (*----- (xj:(Var n))(Dep_Var n (Fun n bdt) xj)->(le_Var n xj x) ----- *)
intros xj xj_Dep.
elim (le_or_gt_Var n xj x); auto with arith bool bdd.
intro H_absurde.
absurd (Dep_Var n (Fun n bdt) xj); auto with arith bool bdd.
apply vars_sup_dim_non_dep2; auto with arith bool bdd.
elim Order_x.
change (gt_Var n xj x) in |- *; assumption.
 (*  (node_decomposition n bdt (Dimension n bdt)) *)
cut (dim_inv n bdt (Dimension n bdt)); auto with arith bool bdd.
generalize Dim; elim (Dimension n bdt); trivial.
intros; absurd (0 > 0); auto with arith bool bdd.
Qed.

(*****************    Denotation of a function by a BDT   ******************)

Definition Denote (n : nat) (f : BF n) (bdt : BDT n) :=
  OBDT n bdt /\ BF_eq n f (Fun n bdt).

Lemma Denote_inv_eq :
 forall (n : nat) (f : BF n) (bdt : BDT n),
 Denote n f bdt -> BF_eq n f (Fun n bdt).
Proof.
intros n f bdt.
unfold Denote in |- *.
simple induction 1; auto with arith bool bdd.
Qed.
Hint Resolve Denote_inv_eq.

Lemma Denote_inv_OBDT :
 forall (n : nat) (f : BF n) (bdt : BDT n), Denote n f bdt -> OBDT n bdt.
Proof.
intros n f bdt.
unfold Denote in |- *.
simple induction 1; auto with arith bool bdd.
Qed.
