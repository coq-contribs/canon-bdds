(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                          Boolean  Functions                              *)
(*           of arity n,  variables of which are named x1 ....xn            *)
(*                  and supposed ordered  x1 < x2 ....< xn                  *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                            Boolean_functions.v                           *)
(****************************************************************************)

Require Export Bool.
Require Export Peano_dec.
Require Export Compare_dec.
Require Export Compare.
Require Export Le.
Require Export Gt.
Require Export Prelude0.
Require Export Prelude1.
Require Export CanonBDDs.canonicite.Finite_sets.
Require Export Vars.


(*-------------------   Valuation of Boolean Variables    ------------------*)


Definition Assign (n : nat) := Var n -> bool.

Definition Cst_Ass (n : nat) (b : bool) (i : Var n) := b.


Lemma Assign_n_inhabited :
 forall n : nat, inhabited (Assign n) (all_ (Assign n)).
Proof.
intro n.
apply Def_inh with (v := Cst_Ass n true).
unfold In, all_ in |- *; auto.
Qed.
Hint Resolve Assign_n_inhabited.


Inductive Assign_eq (n : nat) : Assign n -> Assign n -> Prop :=
    Def_Assign_eq :
      forall A1 A2 : Assign n,
      (forall xi : Var n, A1 xi = A2 xi) -> Assign_eq n A1 A2.


Lemma Assign_eq_refl : forall (n : nat) (A : Assign n), Assign_eq n A A.
Proof.
intros n A.
apply Def_Assign_eq; auto.
Qed.


Lemma Assign_eq_sym :
 forall (n : nat) (A1 A2 : Assign n), Assign_eq n A1 A2 -> Assign_eq n A2 A1.
Proof.
intros n A1 A2 H_A1_eq_A2.
apply Def_Assign_eq.
intro xi.
elim H_A1_eq_A2; auto.
Qed.
Hint Immediate Assign_eq_sym: bdd.


Lemma Assign_eq_trans :
 forall (n : nat) (A1 A2 A3 : Assign n),
 Assign_eq n A1 A2 -> Assign_eq n A2 A3 -> Assign_eq n A2 A3.
Proof.
intros n A1 A2 A3 H_eq_A1A2 H_eq_A2A3.
apply Def_Assign_eq.
intro xi.
apply trans_equal with (y := A2 xi).
elim H_eq_A1A2; auto.
elim H_eq_A2A3; auto.
Qed.
 

(* Extensionality on Assignments *)
(*----------------------------------------------------------------------*)
Axiom
  Assign_subst :
    forall (n : nat) (X : Assign n) (P : Assign n -> Prop),
    P X -> forall A : Assign n, Assign_eq n X A -> P A.
(*----------------------------------------------------------------------*)


Definition Upd (n : nat) (A : Assign n) (xi : Var n) 
  (b : bool) : Assign n :=
  fun xk : Var n =>
  match eq_Var_dec n xi xk return bool with
  | left H => 
      (* Inl H *)  b
      (* Inr H *) 
  | right H => A xk
  end.


Definition Upd_le (n : nat) (A : Assign n) (k : nat) 
  (b : bool) : Assign n :=
  fun xi : Var n =>
  match le_gt_dec (Order n xi) k return bool with
  | left H => 
      (* Inl H *)  b
      (* Inr H *) 
  | right H => A xi
  end.


Lemma Upd_le_n_Cst :
 forall (n : nat) (b : bool) (A : Assign n),
 Assign_eq n (Upd_le n A n b) (Cst_Ass n b).
Proof.
intros n b A.
apply Def_Assign_eq.
simple induction xi.
intros i gi li.
unfold Upd_le, Cst_Ass in |- *; simpl in |- *; auto.
elim (le_gt_dec i n); auto.
intro H_i_gt_n; absurd (i <= n); auto with arith.
Qed.
Hint Resolve Upd_le_n_Cst.


Lemma Upd_le_O_Id :
 forall (n : nat) (b : bool) (A : Assign n), Assign_eq n (Upd_le n A 0 b) A.
Proof.
intros n b A.
apply Def_Assign_eq.
simple induction xi.
intros i gi li.
unfold Upd_le in |- *; simpl in |- *.
elim (le_gt_dec i 0); auto.
intro H_absurde.
absurd (i <= 0); auto with arith.
Qed.
Hint Resolve Upd_le_O_Id.


Lemma Upd_xi_xj :
 forall (n : nat) (xi xj : Var n),
 ~ eq_Var n xi xj -> forall (A : Assign n) (b : bool), Upd n A xj b xi = A xi.
Proof.
intros n xi xj xi_xj_distinct A b.
unfold Upd in |- *.
elim (eq_Var_dec n xj xi); auto.
intro H_absurde.
absurd (eq_Var n xi xj); auto; try apply eq_Var_sym; auto.
Qed.


Lemma eq_Var_eq_values :
 forall (n : nat) (xi xj : Var n) (A : Assign n),
 eq_Var n xi xj -> A xi = A xj.
Proof.
intros n xi xj A xi_eq_xj.
pattern xj in |- *; apply Proof_irrelevance with (n := n) (x := xi); auto.
Qed.


Definition Assign_gt (n k : nat) (A : Assign n) :=
  forall xi : Var n, Order n xi > k -> A xi = true.


Definition Upd' (n : nat) (xi : Var n) (b : bool) (A : Assign n) :
  Assign n := Upd n A xi b.


Lemma Assign_k_finite :
 forall n k : nat, k <= n -> finite (Assign n) (Assign_gt n k).
Proof.
intro n.
simple induction k.
(*  k = O  *)
intro H_triv.
apply
 (extensionality (Assign n)
    (add (Assign n) (empty (Assign n)) (Cst_Ass n true)) 
    (Assign_gt n 0)).
apply Def_set_eq; unfold incl, empty, add, In in |- *.
intro A.
simple induction 1; try contradiction.
unfold Assign_gt in |- *.
simple induction 1; unfold Cst_Ass in |- *; auto with arith bdd.
intro A.
right.
apply
 (Assign_subst n (Cst_Ass n true) (fun A : Assign n => Cst_Ass n true = A));
 auto with arith bdd.
apply Def_Assign_eq; unfold Cst_Ass in |- *.
unfold Assign_gt in H.
intro xi; symmetry  in |- *; auto with arith bdd.
apply finite_add; auto with arith bdd.
(* k -> (S k) *)
clear k.
intros k Hk Sk_le_n.
elimtype (exists x : Var n, S k = Order n x :>nat); auto with arith bdd.
intros x Order_x.
apply
 (extensionality (Assign n)
    (union (Assign n) (Im (Assign n) (Assign_gt n k) (Upd' n x true))
       (Im (Assign n) (Assign_gt n k) (Upd' n x false))) 
    (Assign_gt n (S k))).
(* (set_eq (union (Im (Assign_gt n k) (Upd' x true))
                  (Im (Assign_gt n k) (Upd' x false))) (Assign_gt n (S k))) *)
apply Def_set_eq; unfold incl, union, In in |- *.
intro A.
simple induction 1; unfold Im, Assign_gt in |- *; simple induction 1;
 intro A0; unfold In in |- *; simpl in |- *; simple induction 1;
 intros H_A0 Def_A; elim Def_A; intros xi Order_xi; 
 unfold Upd', Upd in |- *; elim (eq_Var_dec n x xi); 
 auto with arith bdd.
intro H_absurde.
absurd (Order n xi > S k); auto with arith bdd.
pattern xi in |- *.
apply Proof_irrelevance with (n := n) (x := x); auto with arith bdd.
elim Order_x; auto with arith bdd.
intros A Prop_A.
unfold Assign_gt in Prop_A.
elimtype (true = A x \/ false = A x);
 [ idtac | idtac | elim (A x); auto with arith bdd ].
(* true=(A x)->(Im (Assign n) (Assign_gt n k) (Upd' n x true) A) *)
left.
unfold Im, Assign_gt, In, Upd' in |- *.
exists A.
split.
intro xi.
elim (le_or_gt_Var n xi x).
unfold le_Var in |- *.
elim Order_x.
intros Oxi_le_Sk Oxi_gt_k.
pattern xi in |- *.
apply Proof_irrelevance with (n := n) (x := x); auto with arith bdd.
unfold eq_Var in |- *.
apply trans_equal with (y := S k); auto with arith bdd.
unfold gt_Var in |- *.
elim Order_x; auto with arith bdd.
pattern (Upd n A x true) in |- *.
apply Assign_subst with (n := n) (X := A); auto with arith bdd.
apply Def_Assign_eq.
unfold Upd in |- *.
intro xi; elim (eq_Var_dec n x xi); auto with arith bdd.
intro xi_eq_x. 
pattern xi in |- *.
apply Proof_irrelevance with (n := n) (x := x); auto with arith bdd.
(* false=(A x)->(Im (Assign n) (Assign_gt n k) (Upd' n x false) A) *)
right.
unfold Im, Assign_gt, In, Upd' in |- *.
exists (Upd n A x true).
split.
intro xi.
elim (le_or_gt_Var n xi x).
unfold le_Var in |- *.
elim Order_x.
intros Oxi_le_Sk Oxi_gt_k.
pattern xi in |- *.
apply Proof_irrelevance with (n := n) (x := x).
unfold Upd in |- *.
elim (eq_Var_dec n x x); auto with arith bdd.
unfold eq_Var in |- *.
apply trans_equal with (y := S k); auto with arith bdd.
unfold gt_Var in |- *.
elim Order_x.
intros H1 H2.
apply trans_equal with (y := A xi); auto with arith bdd.
unfold Upd in |- *.
elim (eq_Var_dec n x xi); auto with arith bdd.
intro H_abs.
absurd (Order n xi > S k); auto with arith bdd.
pattern xi in |- *.
apply Proof_irrelevance with (n := n) (x := x); auto with arith bdd.
elim Order_x; auto with arith bdd.
pattern (Upd n (Upd n A x true) x false) in |- *.
apply Assign_subst with (n := n) (X := A); auto with arith bdd.
apply Def_Assign_eq.
unfold Upd in |- *.
intro xi; elim (eq_Var_dec n x xi); auto with arith bdd.
intro xi_eq_x. 
pattern xi in |- *.
apply Proof_irrelevance with (n := n) (x := x); auto with arith bdd.
(*  (finite (Assign n) (union (Im (Assign_gt n k) (Upd' n x true)) 
                              (Im (Assign_gt n k) (Upd' n x false))))  *)
apply finite_union; apply finite_image; auto with arith bdd.
Qed.

Lemma Assign_n_finite : forall n : nat, finite (Assign n) (all_ (Assign n)).
Proof.
intro n.
apply (extensionality (Assign n) (Assign_gt n n) (all_ (Assign n))).
apply Def_set_eq; unfold incl, Assign_gt, all_, In in |- *;
 auto with arith bdd.
intros A Triv xi H_abs.
absurd (Order n xi <= n); auto with arith bdd.
apply Assign_k_finite; auto with arith bdd.
Qed.
Hint Resolve Assign_n_finite.


(*--------------------      Boolean Functions      -------------------------*)


Definition BF (n : nat) := Assign n -> bool.


(*------------------     Equality of functions      ------------------------*)


Definition BF_eq (n : nat) (f1 f2 : BF n) : Prop :=
  forall A : Assign n, f1 A = f2 A :>bool.


Lemma BF_eq_refl : forall (n : nat) (f : BF n), BF_eq n f f.
Proof.
intros n f.
unfold BF_eq in |- *; auto with arith bdd.
Qed.
Hint Resolve BF_eq_refl.


Lemma BF_eq_sym :
 forall (n : nat) (f1 f2 : BF n), BF_eq n f1 f2 -> BF_eq n f2 f1.
Proof.
intros n f1 f2.
unfold BF_eq in |- *; auto with arith bdd.
Qed.
Hint Immediate BF_eq_sym: bdd.


Lemma BF_eq_trans :
 forall (n : nat) (f1 f2 f3 : BF n),
 BF_eq n f1 f2 -> BF_eq n f2 f3 -> BF_eq n f1 f3.
Proof.
intros n f1 f2 f3. 
unfold BF_eq in |- *.
intros H12 H23 A.
apply trans_equal with (y := f2 A); auto with arith bdd.
Qed.


Lemma BF_eq_congr :
 forall (n : nat) (f1 f'1 f2 f'2 : BF n),
 BF_eq n f1 f'1 ->
 BF_eq n f2 f'2 -> forall A : Assign n, f1 A = f2 A -> f'1 A = f'2 A.
Proof.
intros n f1 f'1 f2 f'2 eq1 eq2 A H.
unfold BF_eq in eq1.
unfold BF_eq in eq2.
apply trans_equal with (y := f2 A); auto with arith bdd.
apply trans_equal with (y := f1 A); auto with arith bdd.
Qed.


(*------------------    Restriction on a variable   ------------------------*)


Definition Restr (n : nat) (f : BF n) (xi : Var n) 
  (b : bool) : BF n := fun A : Assign n => f (Upd n A xi b).


Lemma f_Restr_f :
 forall (n : nat) (A : Assign n) (f : BF n) (xi : Var n) (b : bool),
 b = A xi -> Restr n f xi b A = f A.
Proof.
intros n A f xi b Def_b.
unfold Restr in |- *.
pattern (Upd n A xi b) in |- *.
apply Assign_subst with (n := n) (X := A); auto with arith bdd.
apply Def_Assign_eq.
intro xj.
unfold Upd in |- *.
elim (eq_Var_dec n xi xj); auto with arith bdd.
intro xi_eq_xj.
apply Proof_irrelevance with (n := n) (x := xi) (a := xj);
 auto with arith bdd; elim Def_b; trivial.
Qed.


Lemma BF_eq_Restr :
 forall (n : nat) (f1 f2 : BF n),
 BF_eq n f1 f2 ->
 forall (x : Var n) (b : bool), BF_eq n (Restr n f1 x b) (Restr n f2 x b).
Proof.
intros n f1 f2 f1_eq_f2 x b.
unfold BF_eq in f1_eq_f2.
unfold BF_eq, Restr in |- *; auto with arith bdd.
Qed.
Hint Resolve BF_eq_Restr.


Lemma Restr_xi_Restr_xi :
 forall (n : nat) (f : BF n) (xi : Var n) (b1 b2 : bool),
 BF_eq n (Restr n (Restr n f xi b1) xi b2) (Restr n f xi b1).
Proof.
intros n f xi b1 b2.
unfold BF_eq in |- *.
intro A.
unfold Restr in |- *.
pattern (Upd n (Upd n A xi b2) xi b1) in |- *.
apply Assign_subst with (n := n) (X := Upd n A xi b1); auto with arith bdd.
apply Def_Assign_eq.
intro x.
unfold Upd in |- *.
elim (eq_Var_dec n xi x); auto with arith bdd.
Qed.
Hint Resolve Restr_xi_Restr_xi.


Lemma Restr_xi_Restr_xj :
 forall (n : nat) (f : BF n) (xi xj : Var n) (bi bj : bool),
 ~ eq_Var n xi xj ->
 BF_eq n (Restr n (Restr n f xi bi) xj bj) (Restr n (Restr n f xj bj) xi bi).
Proof.
intros n f xi xj bi bj xi_diff_xj.
unfold BF_eq in |- *.
intro A.
unfold Restr in |- *.
pattern (Upd n (Upd n A xj bj) xi bi) in |- *.
apply Assign_subst with (n := n) (X := Upd n (Upd n A xi bi) xj bj);
 auto with arith bdd.
apply Def_Assign_eq.
intro x.
unfold Upd in |- *.
elim (eq_Var_dec n xi x); elim (eq_Var_dec n xj x); auto with arith bdd.
intros H1 H2.
absurd (eq_Var n xi xj); auto with arith bdd.
apply eq_Var_trans with (x2 := x); try assumption; apply eq_Var_sym;
 assumption.
Qed.
Hint Resolve Restr_xi_Restr_xj.


(*--------------          Dependent variables         ----------------------*)

Definition Dep_Var (n : nat) (f : BF n) (xi : Var n) : Prop :=
  ~ BF_eq n (Restr n f xi true) (Restr n f xi false).


Lemma xi_non_dep_Restr_xi_Id :
 forall (n : nat) (f : BF n) (xi : Var n),
 ~ Dep_Var n f xi -> forall b : bool, BF_eq n f (Restr n f xi b).
Proof.
intros n f xi xi_non_dep b.
unfold BF_eq, Restr in |- *.
intro A.
elim (eq_bool_dec (f A) (f (Upd n A xi b))); auto with arith bdd.
intro Def_A.
absurd (Dep_Var n f xi); auto with arith bdd.
(* (Dep_Var n f xi) *)
unfold Dep_Var, BF_eq, not in |- *.
intro H_absurde.
cut (Assign_eq n A (Upd n A xi (negb b))).
intro Axi_eq_negb.
unfold not in Def_A.
apply Def_A.
pattern A at 1 in |- *.
apply Assign_subst with (n := n) (X := Upd n A xi (negb b));
 auto with arith bdd.
change (Restr n f xi (negb b) A = Restr n f xi b A) in |- *.
elim b; simpl in |- *; auto with arith bdd.
(* (Assign_eq n A (Upd n A xi (negb b))) *)
apply Def_Assign_eq.
intro x.
unfold Upd in |- *.
elim (eq_Var_dec n xi x); auto with arith bdd.
intro x_eq_xi.
cut (A x = negb b \/ A x = b).
simple induction 1; auto with arith bdd.
intro Cas_absurde_Ax.
absurd (f A = f (Upd n A xi b)); auto with arith bdd.
pattern A at 1 in |- *.
apply Assign_subst with (n := n) (X := Upd n A xi b); auto with arith bdd.
apply Def_Assign_eq.
intro y.
unfold Upd in |- *.
elim (eq_Var_dec n xi y); auto with arith bdd.
intro xi_eq_y.
pattern y in |- *.
apply Proof_irrelevance with (n := n) (x := x); auto with arith bdd.
apply eq_Var_trans with (x2 := xi); auto with arith bdd.
(* (A x)=(negb b) \/ (A x)=b *)
elim (A x); elim b; auto with arith bdd.
Qed.
                          

Lemma xi_non_dep_Restr_xi :
 forall (n : nat) (f : BF n) (xi : Var n) (b : bool),
 ~ Dep_Var n (Restr n f xi b) xi.
Proof.
intros n f xi b.
unfold not in |- *.
intro H_absurde.
unfold Dep_Var in H_absurde.
absurd
 (BF_eq n (Restr n (Restr n f xi b) xi true)
    (Restr n (Restr n f xi b) xi false)); auto with arith bdd.
apply BF_eq_trans with (f2 := Restr n f xi b); auto with arith bdd.
Qed.
Hint Resolve xi_non_dep_Restr_xi.


Lemma BF_eq_same_dep_var :
 forall (n : nat) (f1 f2 : BF n) (xi : Var n),
 BF_eq n f1 f2 -> Dep_Var n f1 xi -> Dep_Var n f2 xi.
Proof.
intros n f1 f2 xi f1_eq_f2 f1_dep_xi.
unfold Dep_Var in |- *.
unfold Dep_Var in f1_dep_xi.
apply Contra with (Q := BF_eq n (Restr n f1 xi true) (Restr n f1 xi false));
 auto with arith bdd.
intro H2.
apply BF_eq_trans with (f2 := Restr n f2 xi true); auto with arith bdd.
apply BF_eq_trans with (f2 := Restr n f2 xi false); auto with arith bdd.
Qed.


Lemma Dep_Restr_f_Dep_f :
 forall (n : nat) (f : BF n) (xi x : Var n) (b : bool),
 Dep_Var n (Restr n f xi b) x -> Dep_Var n f x.
Proof.
intros n f xi x b.
elim (eq_Var_dec n xi x).
(* Case xi = x *)
intro xi_eq_x. 
pattern x in |- *.
apply Proof_irrelevance with (n := n) (x := xi); auto with arith bdd.
intro H_absure.
absurd (Dep_Var n (Restr n f xi b) xi); auto with arith bdd.
(* Case xi diff x *)
intro xi_diff_x.
intro H_dep.
unfold Dep_Var in H_dep.
unfold Dep_Var in |- *.
apply
 Contra
  with
    (Q := BF_eq n (Restr n (Restr n f xi b) x true)
            (Restr n (Restr n f xi b) x false)); auto with arith bdd.
intro H'.
apply BF_eq_trans with (n := n) (f2 := Restr n (Restr n f x true) xi b);
 auto with arith bdd.
apply BF_eq_trans with (n := n) (f2 := Restr n (Restr n f x false) xi b);
 auto with arith bdd.
Qed.


Definition Dep_set (n : nat) (f : BF n) : Varset n :=
  fun xi : Var n => Dep_Var n f xi.


Lemma A_Dep_xi_dec :
 forall (n : nat) (f : BF n) (xi : Var n),
 decidable (Assign n)
   (fun A : Assign n => Restr n f xi true A = Restr n f xi false A :>bool).
Proof.
intros n f xi.
apply Def_dec.
intro A.
elim (eq_bool_dec (Restr n f xi true A) (Restr n f xi false A));
 unfold In in |- *; auto with arith bdd.
Qed.
Hint Resolve A_Dep_xi_dec.


Lemma Dep_set_decidable :
 forall (n : nat) (f : BF n), decidable (Var n) (Dep_set n f).
Proof.
intros n f.
apply Def_dec.
unfold In, Dep_set in |- *.
intro xi.
cut
 ((forall A : Assign n,
   (fun X : Assign n => Restr n f xi true X = Restr n f xi false X) A) \/
  ~
  (forall A : Assign n,
   (fun X : Assign n => Restr n f xi true X = Restr n f xi false X) A)).
simple induction 1; intro H1.
right.
unfold Dep_Var, not in |- *; auto with arith bdd.
left.
unfold Dep_Var in |- *; auto with arith bdd.
apply
 P_dec_AllP_dec
  with
    (V := Assign n)
    (P := fun A : Assign n => Restr n f xi true A = Restr n f xi false A);
 auto with arith bdd.
Qed.


Lemma Dep_set_finite :
 forall (n : nat) (f : BF n),
 exists c : nat, cardinal (Var n) (Dep_set n f) c.
Proof.
intros n f.
apply finite_cardinal.
apply decidable_finite.
apply Var_n_finite.
apply Dep_set_decidable.
Qed.


(*--------      Existence of a greatest dependent variable       ----------*)


Inductive Greatest_Dep_Var (n : nat) (f : BF n) (xi : Var n) : Prop :=
    Def_GreatestDV :
      Dep_Var n f xi ->
      (forall xj : Var n, Dep_Var n f xj -> le_Var n xj xi) ->
      Greatest_Dep_Var n f xi.


Lemma Gst_Dep_Var_inv_Dep :
 forall (n : nat) (f : BF n) (xi : Var n),
 Greatest_Dep_Var n f xi -> Dep_Var n f xi.
Proof.
simple induction 1; auto with arith bdd.
Qed.
Hint Resolve Gst_Dep_Var_inv_Dep.


Lemma Gst_Dep_Var_inv_Greatest :
 forall (n : nat) (f : BF n) (xi : Var n),
 Greatest_Dep_Var n f xi ->
 forall xj : Var n, Dep_Var n f xj -> le_Var n xj xi.
Proof.
simple induction 1; auto with arith bdd.
Qed.

Lemma CardSk_Greatest :
 forall (n c : nat) (f : BF n),
 cardinal (Var n) (Dep_set n f) c ->
 c > 0 -> exists xi : Var n, Greatest_Dep_Var n f xi.
Proof.
intros n c f Def_c c_gt_O.
cut (exists xi : Var n, greatest (Var n) (le_Var n) (Dep_set n f) xi).
2: apply Card_gtO_exist_greatest with (V_eq := eq_Var n) (c := c);
    auto with arith bdd.
simple induction 1.
intros xi Def_xi.
exists xi.
apply Def_GreatestDV; elim Def_xi; auto with arith bdd. 
Qed.

Lemma Dep_Restrf_incl_Depf :
 forall (n : nat) (f : BF n) (xi : Var n) (b : bool),
 Dep_Var n f xi -> incl_st (Var n) (Dep_set n (Restr n f xi b)) (Dep_set n f).
Proof.
intros n f xi b H.
unfold incl_st in |- *.
split. 
unfold incl, Dep_set in |- *.
intro x; unfold In in |- *.
intro H1.
apply Dep_Restr_f_Dep_f with (xi := xi) (b := b); trivial.
exists xi.
split; unfold In, Dep_set in |- *; auto with arith bdd.
Qed.
Hint Resolve Dep_Restrf_incl_Depf.


Lemma CardSk_Card_Restr :
 forall (n c : nat) (f : BF n),
 cardinal (Var n) (Dep_set n f) c ->
 forall xi : Var n,
 Dep_Var n f xi ->
 forall (b : bool) (cr : nat),
 cardinal (Var n) (Dep_set n (Restr n f xi b)) cr -> c > cr.
Proof.
intros n c f Def_c xi f_dep_xi b cr Def_cr.
apply
 incl_st_card_lt
  with (V := Var n) (E1 := Dep_set n (Restr n f xi b)) (E2 := Dep_set n f);
 auto with arith bdd.
Qed.


(*---------------          Constant functions          ---------------------*)


Inductive Constant_fct (n : nat) (f : BF n) : Prop :=
    Def_cst_fct :
      forall b : bool,
      (forall A : Assign n, b = f A :>bool) -> Constant_fct n f.


Definition Fcst (n : nat) (f : BF n) (b : bool) : BF n :=
  fun A : Assign n => f (Cst_Ass n b).


Definition Restr_le (n : nat) (f : BF n) (k : nat) 
  (b : bool) : BF n := fun A : Assign n => f (Upd_le n A k b).


Lemma Constant_fct_inv :
 forall (n : nat) (f : BF n),
 Constant_fct n f -> exists b : bool, (forall A : Assign n, b = f A :>bool).
Proof.
simple induction 1.
intros b H_f.
exists b; auto with arith bdd.
Qed.
Hint Resolve Constant_fct_inv.


Lemma CardO_no_Dep_Var :
 forall (n : nat) (f : BF n),
 cardinal (Var n) (Dep_set n f) 0 -> forall xi : Var n, ~ Dep_Var n f xi.
Proof.
intros n f H_cardO xi.
cut (set_eq (Var n) (Dep_set n f) (empty (Var n))).
2: apply cardinalO_empty; trivial.
intro H_Dep_set.
cut
 (incl (Var n) (Dep_set n f) (empty (Var n)) /\
  incl (Var n) (empty (Var n)) (Dep_set n f)).
2: apply set_eq_inv; trivial.
simple induction 1.
unfold not in |- *; intros H1 H2 H3.
apply H1 with (x := xi); trivial.
Qed.


Lemma Restr_le_k_Restr_le_Sk :
 forall (n k : nat) (f : BF n) (x : Var n),
 Order n x = S k ->
 ~ Dep_Var n f x ->
 forall b : bool,
 BF_eq n f (Restr_le n f k b) -> BF_eq n f (Restr_le n f (S k) b).
Proof.
intros n k f x Order_x x_non_dep b f_eq_Rk_f.
apply BF_eq_trans with (n := n) (f2 := Restr n (Restr_le n f k b) x b).
apply BF_eq_trans with (f2 := Restr n f x b).
apply xi_non_dep_Restr_xi_Id; trivial.
apply BF_eq_Restr; trivial.
unfold BF_eq in |- *.
intro A.
unfold Restr_le, Restr in |- *.
pattern (Upd_le n (Upd n A x b) k b) in |- *.
apply Assign_subst with (n := n) (X := Upd_le n A (S k) b);
 auto with arith bdd.
apply Def_Assign_eq.
intro xi.
unfold Upd_le, Upd in |- *.
elim (le_gt_dec (Order n xi) (S k)); elim (le_gt_dec (Order n xi) k);
 elim (eq_Var_dec n x xi); auto with arith bdd.
(* (gt (Order n xi) k) (le (Order n xi) (S k)) ~(eq_Var n x xi) *)
intros H1 H2 H_absurde.
absurd (eq_Var n x xi); auto with arith bdd.
apply same_order_eq_Var with (k := S k); auto with arith bdd.
(* (gt (Order n xi) (S k)) (le (Order n xi) k) (eq_Var n x xi) *)
intros H1 H2 H3.
absurd (k > S k); auto with arith bdd.
apply le_gt_trans with (m := Order n xi); auto with arith bdd.
(* (gt (Order n xi) (S k)) (le (Order n xi) k) ~(eq_Var n x xi) *)
intros H1 H2 H3.
absurd (k > S k); auto with arith bdd.
apply le_gt_trans with (m := Order n xi); auto with arith bdd.
(* (gt (Order n xi) k) (gt (Order n xi) (S k)) (eq_Var n x xi) *)
intros H1 Order_xi H_absurde. 
cut (Order n x = Order n xi);
   auto with arith bdd.
intro H_absurde2.
absurd (Order n xi > S k); auto with arith bdd.
elim H_absurde2; elim Order_x; auto with arith bdd.
Qed.


Lemma no_Dep_Var_Cstk :
 forall (n : nat) (f : BF n),
 (forall xi : Var n, ~ Dep_Var n f xi) ->
 forall k : nat, k <= n -> forall b : bool, BF_eq n f (Restr_le n f k b).
Proof.
intros n f no_dep_var.
simple induction k.
(* k = O *)
unfold BF_eq, Restr_le in |- *.
intros H_triv b A.
pattern (Upd_le n A 0 b) in |- *.
apply Assign_subst with (n := n) (X := A); auto with arith bdd.
(* k -> (S k) *)
clear k.
intros k Hk Sk_le_n b.
elimtype (exists x : Var n, S k = Order n x); auto with arith bdd.
intros x Order_x.
apply Restr_le_k_Restr_le_Sk with (x := x); auto with arith bdd.
Qed.


Lemma Restr_le_n_Fcst :
 forall (n : nat) (f : BF n) (b : bool),
 BF_eq n (Restr_le n f n b) (Fcst n f b).
Proof.
intros n f b.
unfold BF_eq, Restr_le in |- *.
intro A.
pattern (Upd_le n A n b) in |- *.
apply Assign_subst with (n := n) (X := Cst_Ass n b); auto with arith bdd.
Qed.
Hint Resolve Restr_le_n_Fcst.


Lemma CardO_cst_fct :
 forall (n : nat) (f : BF n),
 cardinal (Var n) (Dep_set n f) 0 -> Constant_fct n f.
Proof.
intros n f H_card.
apply Def_cst_fct with (b := f (Cst_Ass n true)).
change (BF_eq n (Fcst n f true) f) in |- *.
apply BF_eq_sym.
apply BF_eq_trans with (f2 := Restr_le n f n true); auto with arith bdd.
apply no_Dep_Var_Cstk with (k := n); auto with arith bdd.
intro xi.
apply CardO_no_Dep_Var; auto with arith bdd.
Qed.
