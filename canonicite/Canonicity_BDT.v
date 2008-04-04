(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                         Canonicity of BDTs                               *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                             Canonicity_BDT.v                             *)
(****************************************************************************)

Require Import bdd.canonicite.Boolean_functions.
Require Import bdd.canonicite.BDTs.
Require Import Complete_induction.

Parameter n : nat.

(****************     Existence of BDT Canonical form    ******************)

Lemma Cst_fct_Fzero_Fone :
 forall f : BF n,
 Constant_fct n f -> BF_eq n f (Fun n (zero n)) \/ BF_eq n f (Fun n (one n)).
Proof.
intros f H_f_Cst.
cut (exists b : bool, (forall A : Assign n, b = f A)); auto.
simple induction 1.
simple induction x.
intro f_Cst_true.
right; simpl in |- *.
unfold BF_eq in |- *; auto.
intro f_Cst_false.
left; simpl in |- *.
unfold BF_eq in |- *; auto.
Qed.

Lemma Exist_DepO :
 forall f : BF n, Constant_fct n f -> exists bdt : BDT n, Denote n f bdt.
Proof.
intros f f_Cst.
cut (BF_eq n f (Fun n (zero n)) \/ BF_eq n f (Fun n (one n)));
 try apply Cst_fct_Fzero_Fone; auto.
simple induction 1.
      (*  f cst false *)
intro f_eq_Fzero.
exists (zero n).
unfold Denote in |- *; auto.
      (*  f cst true *)
intro f_eq_Fone.
exists (one n).
unfold Denote in |- *; auto.
Qed.

Lemma Denote_true_false :
 forall (f : BF n) (xi : Var n),
 Greatest_Dep_Var n f xi ->
 forall bl bh : BDT n,
 Denote n (Restr n f xi false) bl ->
 Denote n (Restr n f xi true) bh -> Denote n f (node n xi bl bh).
Proof.
intros f xi Def_xi bl bh Def_bl Def_bh.
unfold Denote in |- *.
split.
(*--- (OBDT n (node n xi bl bh)) ----*)
apply order_node.
apply Denote_inv_OBDT with (Restr n f xi false); assumption.
apply Denote_inv_OBDT with (Restr n f xi true); assumption.
     (* (gt (Order n xi) (Dimension n bl)) *)
elim (gt_O_eq (Dimension n bl)).
2: simple induction 1; auto.
intro Dim_low_gt_O.
cut
 (exists x : Var n,
    Order n x = Dimension n bl /\ Greatest_Dep_Var n (Fun n bl) x).
simple induction 1.
intro xl.
simple induction 1.
intros Order_xl Def_xl.
elim Order_xl.
apply le_ne_gt.
change (le_Var n xl xi) in |- *.
apply Gst_Dep_Var_inv_Greatest with (f := f); auto.
  (* (Dep_Var n f xl) *)
apply Dep_Restr_f_Dep_f with (xi := xi) (b := false).
apply BF_eq_same_dep_var with (f1 := Fun n bl);
 [ apply BF_eq_sym; auto | apply Gst_Dep_Var_inv_Dep; auto ].
  (*  ~(Order n xl)=(Order n xi) *)
unfold not in |- *.
intro H_absurde.
absurd (Dep_Var n (Fun n bl) xi).
             (*  ~(Dep_Var n (Fun n bl) xi) *)
apply Contra with (Q := Dep_Var n (Restr n f xi false) xi); auto.
intro Flow_dep_xi.
apply BF_eq_same_dep_var with (f1 := Fun n bl); try apply BF_eq_sym; auto.
             (* (Dep_Var n (Fun n bl) xi) *)
apply (Proof_irrelevance n xl (fun a : Var n => Dep_Var n (Fun n bl) a));
 auto.
   (*    (Ex [x:(Var n)](Order n x)=(Dimension n bl)
                     /\ (Greatest_Dep_Var n (Fun n bl) x))   *)
apply Dim_is_Greatest_Dep_Var; auto. 
apply Denote_inv_OBDT with (f := Restr n f xi false); trivial.
    (*  (gt (Order n xi) (Dimension n bh)) *)
elim (gt_O_eq (Dimension n bh)).
2: simple induction 1; auto.
intro Dim_high_gt_O.
cut
 (exists x : Var n,
    Order n x = Dimension n bh /\ Greatest_Dep_Var n (Fun n bh) x).
simple induction 1.
intro x_high.
simple induction 1.
intros Order_x_high Def_x_high.
elim Order_x_high.
apply le_ne_gt.
change (le_Var n x_high xi) in |- *.
apply Gst_Dep_Var_inv_Greatest with (f := f); auto.
  (* (Dep_Var n f x_high) *)
apply Dep_Restr_f_Dep_f with (xi := xi) (b := true).
apply BF_eq_same_dep_var with (f1 := Fun n bh);
 [ apply BF_eq_sym; auto | apply Gst_Dep_Var_inv_Dep; auto ].
  (*  ~(Order n x_high)=(Order n xi) *)
unfold not in |- *.
intro H_absurde.
absurd (Dep_Var n (Fun n bh) xi).
             (*  ~(Dep_Var n (Fun n bh) xi) *)
apply Contra with (Q := Dep_Var n (Restr n f xi true) xi); auto.
intro Fhigh_dep_xi.
apply BF_eq_same_dep_var with (f1 := Fun n bh); try apply BF_eq_sym; auto.
             (* (Dep_Var n (Fun n bh) xi) *)
apply (Proof_irrelevance n x_high (fun a : Var n => Dep_Var n (Fun n bh) a));
 auto.
   (*    (Ex [x:(Var n)](Order n x)=(Dimension n bh)
                     /\ (Greatest_Dep_Var n (Fun n bh) x))       *)
apply Dim_is_Greatest_Dep_Var; auto. 
apply Denote_inv_OBDT with (f := Restr n f xi true); trivial.
   (*  ~(BDT_eq n bl bh)  *)
unfold not in |- *.
intro H_absurde.
absurd (BF_eq n (Restr n f xi true) (Restr n f xi false)).
    (*  ~(BF_eq n (Restr n f xi true) (Restr n f xi false)) *)
change (Dep_Var n f xi) in |- *; auto.
    (*   (BF_eq n (Restr n f xi true) (Restr n f xi false)) *)
apply BF_eq_trans with (f2 := Fun n bh); auto.
apply BF_eq_trans with (f2 := Fun n bl); apply BF_eq_sym; auto.
      (* (BF_eq n f (Fun n (node n xi bl bh))) *)
unfold BF_eq in |- *.
intro A; simpl in |- *.
elimtype (true = A xi \/ false = A xi); try simple induction 1.
      (*  (f A)=(Fun n bh A) *)
elim (f_Restr_f n A f xi true); auto.
cut (BF_eq n (Restr n f xi true) (Fun n bh)); auto. 
unfold BF_eq in |- *; auto.
      (*  (f A)=(Fun n bl A)  *)
elim (f_Restr_f n A f xi false); auto.
cut (BF_eq n (Restr n f xi false) (Fun n bl)); auto. 
unfold BF_eq in |- *; auto.
      (*   true=(A xi) \/ false=(A xi) *)
elim (A xi); auto.
Qed.


(*--------------------------------------------------------------------------*)
   Theorem Existence : forall f : BF n, exists bdt : BDT n, Denote n f bdt.
(*--------------------------------------------------------------------------*)

Proof.
intro f.
elim (Dep_set_finite n f).
intros kf Def_kf.
cut
 (forall (k : nat) (f : BF n),
  cardinal (Var n) (Dep_set n f) k -> exists bdt : BDT n, Denote n f bdt).
intro H; apply H with (k := kf); trivial with arith.
intro k; pattern k in |- *; apply nat_wf_ind.
(****  |Dep(f)|=O     ****)
intros fO H_CardO.
apply Exist_DepO; apply CardO_cst_fct; assumption.
(****  |Dep(f)|=(S l) ****)
intros l H_Exist_Dep_l f_Sl H_CardSl.
elim (CardSk_Greatest n (S l) f_Sl); trivial with arith. 
intros xi Def_xi.
cut (exists bdt : BDT n, Denote n (Restr n f_Sl xi true) bdt).
intro H_rec_true; elim H_rec_true.
intros bh Def_bh.
cut (exists bdt : BDT n, Denote n (Restr n f_Sl xi false) bdt).
intro H_rec_false; elim H_rec_false.
intros bl Def_bl.
exists (node n xi bl bh).
apply Denote_true_false; trivial with arith.
      (*   Proof of Ex([bdt:(BDT n)](Denote n (Restr n f_Sl xi false) bdt))  *)
elim (Dep_set_finite n (Restr n f_Sl xi false)).
intros l_false Def_l_false.
apply H_Exist_Dep_l with (l0 := l_false); trivial with arith.
apply gt_S_le.
apply
 CardSk_Card_Restr
  with
    (n := n)
    (c := S l)
    (f := f_Sl)
    (xi := xi)
    (b := false)
    (cr := l_false); auto with arith bool bdd.
      (*   Proof of Ex([bdt:(BDT n)](Denote n (Restr n f_Sl xi true) bdt))  *)
elim (Dep_set_finite n (Restr n f_Sl xi true)).
intros l_true Def_l_true.
apply H_Exist_Dep_l with (l0 := l_true); trivial with arith.
apply gt_S_le.
apply
 CardSk_Card_Restr
  with (n := n) (c := S l) (f := f_Sl) (xi := xi) (b := true) (cr := l_true);
 auto with arith bool bdd.
Qed.





(****************               Uniqueness                   ******************)



(*----------------------------------------------------------------------------*)
   Theorem Uniqueness :
    forall (f : BF n) (bdt1 bdt2 : BDT n),
    Denote n f bdt1 -> Denote n f bdt2 -> BDT_eq n bdt1 bdt2.
(*----------------------------------------------------------------------------*)

Proof.
intros f bdt1 bdt2 Def_bdt1 Def_bdt2.
apply Fun_eq_OBDT_eq; try apply Denote_inv_OBDT with f;
 auto with arith bool bdd.
apply BF_eq_trans with f; auto with arith bool bdd.
apply BF_eq_sym; auto with arith bool bdd.
Qed.



(*----------------------------------------------------------------------------*)
  Remark Canonicity_BF_BDT :
   forall (f1 f2 : BF n) (bdt1 bdt2 : BDT n),
   Denote n f1 bdt1 ->
   Denote n f2 bdt2 -> BF_eq n f1 f2 -> BDT_eq n bdt1 bdt2.
(*----------------------------------------------------------------------------*)
Proof.
intros f1 f2 bdt1 bdt2 Def_bdt1 Def_bdt2 H_eq_f1_f2.
cut (Denote n f1 bdt2).
intro H.
apply Uniqueness with (f := f1); assumption.
unfold Denote in |- *.
split.
elim Def_bdt2; auto with arith bool bdd.
apply BF_eq_trans with (f2 := f2); try assumption.
elim Def_bdt2; auto with arith bool bdd.
Qed.

(*--------------------------------------------------------------------------*)
  Remark Canonicity_BDT_BF :
   forall (f1 f2 : BF n) (bdt1 bdt2 : BDT n),
   Denote n f1 bdt1 ->
   Denote n f2 bdt2 -> BDT_eq n bdt1 bdt2 -> BF_eq n f1 f2.                     
(*--------------------------------------------------------------------------*)
Proof.
intros f1 f2 bdt1 bdt2 Def_bdt1 Def_bdt2 bdt1_iso_bdt2.
apply BF_eq_trans with (f2 := Fun n bdt2).
apply BF_eq_trans with (f2 := Fun n bdt1); auto with arith bool bdd.
apply BF_eq_sym; auto with arith bool bdd.
Qed.
