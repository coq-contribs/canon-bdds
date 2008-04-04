(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                       Prelude on Boolean functions                       *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                            Boolean_functions.v                           *)
(****************************************************************************)

Require Import Prelude_BDT.
Require Export Peano_dec.

(*------------------             Assignments            --------------------*)


Definition Assign := nat -> bool.


Definition Ass_eq (A1 A2 : Assign) : Prop := forall i : nat, A1 i = A2 i.

Lemma Ass_eq_refl : forall A : Assign, Ass_eq A A.
Proof.
intro A; unfold Ass_eq in |- *; auto with v62.
Qed.
Hint Resolve Ass_eq_refl.

Lemma Ass_eq_sym : forall A1 A2 : Assign, Ass_eq A1 A2 -> Ass_eq A2 A1.
Proof.
intros A1 A2.
unfold Ass_eq in |- *; auto with v62.
Qed.
Hint Immediate Ass_eq_sym.

Lemma Ass_eq_trans :
 forall A1 A2 A3 : Assign, Ass_eq A1 A2 -> Ass_eq A2 A3 -> Ass_eq A2 A3.
Proof.
intros A1 A2 A3.
unfold Ass_eq in |- *; intros H1 H2 i.
apply trans_equal with (y := A2 i); auto with v62.
Qed.
 
(*-----------------------------------------------*)
  Axiom
    Extensionality_Assignments :
      forall A1 A2 : Assign, Ass_eq A1 A2 -> A1 = A2.
(*-----------------------------------------------*)

Lemma Cases_Assign_i :
 forall (A : Assign) (i : nat), true = A i \/ false = A i.
Proof.
intros A i.
elim (A i); auto with v62.
Qed.


Definition Upd (A : Assign) (i : nat) (b : bool) : Assign :=
  fun x : nat =>
  match eq_nat_dec i x return bool with
  | left H =>
      (* Inl H *)  b
      (* Inr H *) 
  | right H => A x
  end.


Lemma L_Assign1 :
 forall (A : Assign) (i : nat) (b : bool), b = A i -> A = Upd A i b.
Proof.
intros A i b H.
apply Extensionality_Assignments.
unfold Ass_eq, Upd in |- *.
intro j; elim (eq_nat_dec i j); auto with v62.
simple induction 1; elim H; trivial with v62.
Qed.


Lemma L_Assign2 : forall (A : Assign) (i : nat) (b : bool), Upd A i b i = b.
Proof.
intros A i b.
unfold Upd in |- *; elim (eq_nat_dec i i);
 [ trivial with v62 | intro Habs; absurd (i = i); trivial with v62 ].
Qed.


Lemma L_Assign3 :
 forall (A : Assign) (j i : nat),
 j <> i -> forall b : bool, Upd A j b i = A i.
Proof.
intros A j i Hneq b.
unfold Upd in |- *; elim (eq_nat_dec j i);
 [ intro Habs; absurd (j = i); assumption | trivial with v62 ].
Qed.



(*--------------------       Boolean Functions         ---------------------*)


Definition BF := Assign -> bool.
Definition BF_eq (f1 f2 : BF) : Prop := forall A : Assign, f1 A = f2 A.


Lemma BF_eq_refl : forall f : BF, BF_eq f f.
Proof.
intro f.
unfold BF_eq in |- *; auto with v62.
Qed.
Hint Resolve BF_eq_refl.


Lemma BF_eq_sym : forall f1 f2 : BF, BF_eq f1 f2 -> BF_eq f2 f1.
Proof.
intros f1 f2.
unfold BF_eq in |- *; auto with v62.
Qed.
Hint Immediate BF_eq_sym.


Lemma BF_eq_trans :
 forall f1 f2 f3 : BF, BF_eq f1 f2 -> BF_eq f2 f3 -> BF_eq f1 f3.
Proof.
intros f1 f2 f3. 
unfold BF_eq in |- *.
intros H12 H23 A.
apply trans_equal with (y := f2 A); auto with v62.
Qed.


   (*------ Operations  on boolean functions ------*)

Definition Fcst (b : bool) (A : Assign) := b.
Definition TRUE (A : Assign) := true.              Hint Unfold TRUE.
Definition FALSE (A : Assign) := false.            Hint Unfold FALSE.
Definition F (i : nat) : BF := fun A : Assign => A i.
Definition OR (f1 f2 : BF) : BF := fun A : Assign => f1 A || f2 A. 
Definition AND (f1 f2 : BF) : BF := fun A : Assign => f1 A && f2 A.
Definition NOT (f : BF) : BF := fun A : Assign => negb (f A).
Definition IF_ (f1 f2 f3 : BF) : BF :=
  fun A : Assign =>
  match f1 A return bool with
  | true => f2 A
  | false => f3 A
  end.

(* Redefine syntax for this new IF *)

Notation "'IF' c1 'then' c2 'else' c3" := (IF_ c1 c2 c3).

Lemma eq_Fi_if_i : forall i : nat, BF_eq (F i) (IF F i then TRUE else FALSE).
Proof.
intro i.
unfold BF_eq in |- *.
intro A.
unfold IF_, F, TRUE, FALSE in |- *; simpl in |- *.
elim (A i); auto with v62.
Qed.
Hint Resolve eq_Fi_if_i.


Lemma eq_f_iff : forall (i : nat) (f : BF), BF_eq f (IF F i then f else f).
Proof.
intros i f.
unfold BF_eq, IF_ in |- *; intro A.
elim (F i A); trivial with v62.
Qed.


Lemma eq_if_true_f : forall f g : BF, BF_eq f (IF TRUE then f else g).
Proof.
unfold BF_eq in |- *; auto with v62.
Qed.


Lemma eq_if_false_g : forall f g : BF, BF_eq g (IF FALSE then f else g).
Proof.
unfold BF_eq in |- *; auto with v62.
Qed.


Lemma TRUE_neutral_AND : forall f : BF, BF_eq (AND TRUE f) f.
Proof.
intro f.
unfold BF_eq, AND in |- *; auto with v62.
Qed.
Hint Resolve TRUE_neutral_AND.


Lemma FALSE_absorb_AND : forall f : BF, BF_eq (AND FALSE f) FALSE.
Proof.
intro f.
unfold BF_eq, AND in |- *; auto with v62.
Qed.
Hint Resolve FALSE_absorb_AND.


Lemma Commutative_AND : forall f1 f2 : BF, BF_eq (AND f1 f2) (AND f2 f1).
Proof.
unfold BF_eq, AND in |- *.
intros; apply Commutative_andb.
Qed.


Lemma TRUE_absorb_OR : forall f : BF, BF_eq (OR TRUE f) TRUE.
Proof.
intro f.
unfold BF_eq, OR in |- *; auto with v62.
Qed.
Hint Resolve TRUE_absorb_OR.


Lemma FALSE_neutral_OR : forall f : BF, BF_eq (OR FALSE f) f.
Proof.
intro f.
unfold BF_eq, OR in |- *; auto with v62.
Qed.
Hint Resolve FALSE_neutral_OR.


Lemma Commutative_OR : forall f1 f2 : BF, BF_eq (OR f1 f2) (OR f2 f1).
Proof.
unfold BF_eq, OR in |- *.
intros; apply Commutative_orb.
Qed.


Lemma TRUE_neq_FALSE : ~ BF_eq TRUE FALSE.
Proof.
unfold BF_eq, TRUE, FALSE, not in |- *.
intro H; absurd (true = false).
exact diff_true_false.
exact (H (fun i : nat => true)).
Qed.


(*----- Congruence properties   ------*)

Definition Boolean (Op : BF -> BF -> BF) :=
  exists op : bool -> bool -> bool,
    (forall (f1 f2 : BF) (A : Assign), Op f1 f2 A = op (f1 A) (f2 A)).


Lemma Boolean_AND : Boolean AND.
Proof.
unfold Boolean in |- *.
exists andb.
unfold AND in |- *; auto with v62.
Qed.
Hint Resolve Boolean_AND.


Lemma Boolean_OR : Boolean OR.
Proof.
unfold Boolean in |- *.
exists orb.
unfold OR in |- *; auto with v62.
Qed.
Hint Resolve Boolean_OR.


Lemma BF_eq_congruence_op2 :
 forall Op : BF -> BF -> BF,
 Boolean Op ->
 forall f1 f'1 : BF,
 BF_eq f1 f'1 ->
 forall f2 f'2 : BF, BF_eq f2 f'2 -> BF_eq (Op f1 f2) (Op f'1 f'2).
Proof.
intros Op HOp f1 f'1 H1 f2 f'2 H2.
unfold BF_eq in |- *.
intro A.
unfold Boolean in HOp.
elim HOp.
intros op Def_op.
apply trans_equal with (y := op (f1 A) (f2 A)); auto with v62.
apply trans_equal with (y := op (f'1 A) (f'2 A)); auto with v62.
unfold BF_eq in H1.
unfold BF_eq in H2.
elim H1; elim H2; auto with v62.
Qed.


Lemma BF_eq_congruence_op1 :
 forall f f' : BF, BF_eq f f' -> BF_eq (NOT f) (NOT f').
Proof.
intros f f' H_f_eq_f'.
unfold BF_eq, NOT in |- *.
intro A.
unfold BF_eq in H_f_eq_f'.
elim (H_f_eq_f' A); auto with v62.
Qed.


Lemma BF_eq_congruence_op3 :
 forall f1 f'1 : BF,
 BF_eq f1 f'1 ->
 forall f2 f'2 : BF,
 BF_eq f2 f'2 ->
 forall f3 f'3 : BF,
 BF_eq f3 f'3 -> BF_eq (IF f1 then f2 else f3) (IF f'1 then f'2 else f'3).
Proof.
unfold BF_eq in |- *.
intros f1 f'1 H1 f2 f'2 H2 f3 f'3 H3 A.
unfold IF_ in |- *; elim (H1 A); elim (f1 A); auto with v62.
Qed.


(*----- Commutations properties   ------*)

Lemma Commute_if_not :
 forall (f g : BF) (i : nat),
 BF_eq (NOT (IF F i then f else g)) (IF F i then NOT f else NOT g).
Proof.
intros f g i.
unfold BF_eq in |- *; intro A.
unfold IF_, NOT in |- *; simpl in |- *; elim (F i A); auto with v62.
Qed.


Lemma Commute_if_bool_op2 :
 forall Op : BF -> BF -> BF,
 Boolean Op ->
 forall (f1 f2 g1 g2 : BF) (i : nat),
 BF_eq (IF F i then Op f1 g1 else Op f2 g2)
   (Op (IF F i then f1 else f2) (IF F i then g1 else g2)).
Proof.
intros Op HOp f1 f2 g1 g2 i.
unfold BF_eq, IF_ in |- *; intro A.
elim HOp.
intros op Def_op.
rewrite (Def_op f1 g1 A).
rewrite (Def_op f2 g2 A).
rewrite
 (Def_op
    (fun A : Assign =>
     match F i A return bool with
     | true => f1 A
     | false => f2 A
     end)
    (fun A : Assign =>
     match F i A return bool with
     | true => g1 A
     | false => g2 A
     end)).
elim (F i A); trivial with v62.
Qed.



(*----------------        Restriction  of functions       -------------------*)

Definition Frestr (f : BF) (i : nat) (b : bool) : BF :=
  fun A : Assign => f (Upd A i b).


Lemma FShannon_expansion :
 forall (f : BF) (i : nat),
 BF_eq f (IF F i then Frestr f i true else Frestr f i false).
Proof.
intros f i.
unfold BF_eq, Frestr, IF_, F in |- *; intro A; simpl in |- *.
elim (Cases_Assign_i A i); simple induction 1; elim L_Assign1;
 trivial with v62.
Qed.


Lemma Frestr_Fi_i_b : forall (i : nat) (b : bool), Frestr (F i) i b = Fcst b.
Proof.
intros i b.
unfold Frestr, Upd, F, Fcst in |- *.
elim (eq_nat_dec i i);
 [ trivial with v62 | intro H; absurd (i = i); trivial with v62 ].
Qed.


Lemma Frestr_Fi_true : forall i : nat, Frestr (F i) i true = TRUE.
Proof.
intro i.
unfold Frestr, Upd, F in |- *.
elim (eq_nat_dec i i);
 [ unfold TRUE in |- *; trivial with v62
 | intro H; absurd (i = i); trivial with v62 ].
Qed.


Lemma Frestr_Fi_false : forall i : nat, Frestr (F i) i false = FALSE.
Proof.
intro i.
unfold Frestr, Upd, F in |- *.
elim (eq_nat_dec i i);
 [ unfold FALSE in |- *; trivial with v62
 | intro H; absurd (i = i); trivial with v62 ].
Qed.


Lemma Frestr_Fi_j :
 forall i j : nat, i <> j -> forall b : bool, Frestr (F i) j b = F i.
Proof.
intros i j H b.
unfold Frestr, Upd, F in |- *.
elim (eq_nat_dec j i);
 [ intro Habs; absurd (i = j); auto with v62 | trivial with v62 ].
Qed.


Lemma Restr_Fcst :
 forall (i : nat) (b1 b2 : bool), Frestr (Fcst b1) i b2 = Fcst b1.
Proof.
unfold Frestr, Fcst, Upd in |- *; auto with v62.
Qed.


Lemma F_eq_Frestr_eq :
 forall f1 f2 : BF,
 BF_eq f1 f2 ->
 forall (i : nat) (b : bool), BF_eq (Frestr f1 i b) (Frestr f2 i b).
Proof.
intros f1 f2 H i b.
unfold BF_eq in H.
unfold BF_eq, Frestr in |- *; auto with v62.
Qed.
Hint Resolve F_eq_Frestr_eq.


Lemma Commute_Frestr_IF :
 forall (f1 f2 f3 : BF) (i : nat) (b : bool),
 BF_eq (Frestr (IF f1 then f2 else f3) i b)
   (IF Frestr f1 i b then Frestr f2 i b else Frestr f3 i b).
Proof.
intros f1 f2 f3 i b.
unfold BF_eq, IF_, Frestr in |- *; trivial with v62.
Qed.




(*----------------          Dependant variables           ------------------*)


Definition Dep_Var (f : BF) (i : nat) : Prop :=
  ~ BF_eq (Frestr f i true) (Frestr f i false).

Lemma L_Dep_Var1 :
 forall (f : BF) (i : nat),
 ~ Dep_Var f i -> forall b : bool, BF_eq f (Frestr f i b).
Proof.
intros f i.
unfold Dep_Var in |- *; intros H b.
apply
 BF_eq_trans with (f2 := IF F i then Frestr f i true else Frestr f i false);
 try apply FShannon_expansion.
elim b.
(*   Case b=true    *)
apply
 BF_eq_trans with (f2 := IF F i then Frestr f i true else Frestr f i true);
 [ apply BF_eq_congruence_op3; try trivial with v62
 | apply BF_eq_sym; apply eq_f_iff ].
apply BF_eq_sym; apply Classic; assumption.
(*   Case b=false   *)
apply
 BF_eq_trans with (f2 := IF F i then Frestr f i false else Frestr f i false);
 [ apply BF_eq_congruence_op3; try trivial with v62
 | apply BF_eq_sym; apply eq_f_iff ].
apply Classic; assumption.
Qed.

Lemma L_Dep_Var2 :
 forall (f : BF) (i : nat),
 (forall b : bool, BF_eq f (Frestr f i b)) -> ~ Dep_Var f i.
Proof.
intros f i H.
unfold Dep_Var in |- *.
apply P_notnotP.
apply BF_eq_trans with (f2 := f); auto with v62.
Qed.

Lemma Fcst_no_depvar : forall (i : nat) (b : bool), ~ Dep_Var (Fcst b) i.
Proof.
intros i b.
apply L_Dep_Var2.
intro b'.
rewrite (Restr_Fcst i b b'); trivial with v62.
Qed.

Lemma FB12 :
 forall (i : nat) (f1 : BF),
 ~ Dep_Var f1 i ->
 forall f2 : BF,
 ~ Dep_Var f2 i ->
 forall g1 : BF,
 ~ Dep_Var g1 i ->
 forall g2 : BF,
 ~ Dep_Var g2 i ->
 BF_eq (IF F i then f1 else f2) (IF F i then g1 else g2) ->
 BF_eq f1 g1 /\ BF_eq f2 g2.
Proof.
intros i f1 Hf1 f2 Hf2 g1 Hg1 g2 Hg2 H.
split.
(*    (BF_eq f1 g1)    *)
apply BF_eq_trans with (f2 := Frestr f1 i true);
 [ apply L_Dep_Var1; trivial with v62 | idtac ].      
apply BF_eq_trans with (f2 := Frestr g1 i true);
 [ idtac | apply BF_eq_sym; apply L_Dep_Var1; trivial with v62 ].
apply
 BF_eq_trans with (f2 := IF TRUE then Frestr f1 i true else Frestr f2 i true);
 [ apply eq_if_true_f | idtac ].
apply
 BF_eq_trans with (f2 := IF TRUE then Frestr g1 i true else Frestr g2 i true);
 [ idtac | apply BF_eq_sym; apply eq_if_true_f ].
elim (Frestr_Fi_true i).
apply BF_eq_trans with (f2 := Frestr (IF F i then f1 else f2) i true);
 [ apply BF_eq_sym; apply Commute_Frestr_IF | idtac ].
apply BF_eq_trans with (f2 := Frestr (IF F i then g1 else g2) i true);
 [ idtac | apply Commute_Frestr_IF ].
apply F_eq_Frestr_eq; trivial with v62.
(*    (BF_eq f2 g2)    *)
apply BF_eq_trans with (f2 := Frestr f2 i false);
 [ apply L_Dep_Var1; trivial with v62 | idtac ].
apply BF_eq_trans with (f2 := Frestr g2 i false);
 [ idtac | apply BF_eq_sym; apply L_Dep_Var1; trivial with v62 ]. 
apply
 BF_eq_trans
  with (f2 := IF FALSE then Frestr f1 i false else Frestr f2 i false);
 [ apply eq_if_false_g | idtac ].
apply
 BF_eq_trans
  with (f2 := IF FALSE then Frestr g1 i false else Frestr g2 i false);
 [ idtac | apply BF_eq_sym; apply eq_if_false_g ].
elim (Frestr_Fi_false i).
apply BF_eq_trans with (f2 := Frestr (IF F i then f1 else f2) i false);
 [ apply BF_eq_sym; apply Commute_Frestr_IF | idtac ].
apply BF_eq_trans with (f2 := Frestr (IF F i then g1 else g2) i false);
 [ idtac | apply Commute_Frestr_IF ].
apply F_eq_Frestr_eq; trivial with v62.
Qed. 

Remark FB12bis :
 forall (i : nat) (f1 : BF),
 ~ Dep_Var f1 i ->
 forall f2 : BF,
 ~ Dep_Var f2 i ->
 forall g : BF,
 ~ Dep_Var g i ->
 BF_eq (IF F i then f1 else f2) g -> BF_eq f1 g /\ BF_eq f2 g.
Proof.
intros i f1 Hf1 f2 Hf2 g Hg H.
apply FB12 with (i := i); try assumption.
apply BF_eq_trans with (f2 := g); [ assumption | apply eq_f_iff ].
Qed.
