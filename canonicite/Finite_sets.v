(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*            Lemmas on sets, finite sets, totally ordered sets             *)
(*                            Coq V5.10                                     *)
(*                                                                          *)
(*   Some definitions and lemmas are borrowed from Floyd.v and Dijkstra.v   *)
(*                        in $COQTH/PROGRAMS                                *)
(*                                                                          *)
(*       E. Ledinot                                                         *)
(*       Dassault-Aviation                                                  *)
(*       March 1993                                                         *)
(*                                                                          *)
(****************************************************************************)
(*                               Finite_sets.v                              *)
(****************************************************************************)

(* Warning : Two axioms are introduced:
    Axiom V_decidable : (x,y:V){x=y}+{~x=y}.
    Axiom extensionality: (V,W:set)(set_eq V W) -> (P:set->Prop)(P V) -> (P W).
*)

Require Import Prelude0.
Require Import Gt.
Require Import Lt.

Section sets.

Variable V : Set. (* The Universe of discourse *)

Axiom V_decidable : forall x y : V, {x = y} + {x <> y}.

Definition set := V -> Prop.

Definition In (P : set) (x : V) := P x.

Definition incl (P Q : set) := forall x : V, In P x -> In Q x.

Definition incl_st (P Q : set) :=
  incl P Q /\ (exists x : V, ~ In P x /\ In Q x).


Lemma incl_refl : forall U : set, incl U U.
Proof.
intro U; unfold incl, In in |- *; auto with arith.
Qed.
Hint Resolve incl_refl.


Lemma incl_trans : forall W X Y : set, incl W X -> incl X Y -> incl W Y.
Proof.
unfold incl in |- *; auto with arith.
Qed.


Inductive set_eq : set -> set -> Prop :=
    Def_set_eq : forall U W : set, incl U W -> incl W U -> set_eq U W.
Hint Resolve Def_set_eq.


Lemma set_eq_inv : forall U W : set, set_eq U W -> incl U W /\ incl W U.
Proof.
simple induction 1; auto with arith.
Qed.


Lemma set_eq_refl : forall U : set, set_eq U U.
Proof.
auto with arith.
Qed.
Hint Resolve set_eq_refl.


Lemma set_eq_sym : forall V1 V2 : set, set_eq V1 V2 -> set_eq V2 V1.
Proof.
simple induction 1; auto with arith.
Qed.
Hint Immediate set_eq_sym: bdd.


Lemma set_eq_trans :
 forall V1 V2 V3 : set, set_eq V1 V2 -> set_eq V2 V3 -> set_eq V1 V3.
Proof.
intros V1 V2 V3 V1_eq_V2 V2_eq_V3.
cut (incl V1 V2 /\ incl V2 V1); try (apply set_eq_inv; trivial with arith).
cut (incl V2 V3 /\ incl V3 V2); try (apply set_eq_inv; trivial with arith).
simple induction 1; intros H23 H32.
simple induction 1; intros H12 H21.
apply Def_set_eq; apply incl_trans with (X := V2); trivial with arith.
Qed.


Axiom
  extensionality :
    forall U W : set, set_eq U W -> forall P : set -> Prop, P U -> P W.

Inductive inhabited (S : set) : Prop :=
    Def_inh : forall v : V, In S v -> inhabited S.

Definition empty : set := fun x : V => False.

Definition all_ : set := fun x : V => True.


Section Add.

Variable Q : set.
Variable x : V.

Definition add : set := fun y : V => In Q y \/ x = y.

Variable y : V.

Lemma in_Q_add : In Q y -> In add y.
Proof.
intro.
unfold In, add in |- *.
auto with arith.
Qed.

Lemma eq_add : x = y -> In add y.
Proof.
intro.
unfold In, add in |- *.
auto with arith.
Qed.

End Add.
Hint Resolve in_Q_add eq_add.


Lemma singlx : forall x y : V, In (add empty x) y -> x = y.
Proof.
intros x y.
unfold add, empty, In in |- *.
simple induction 1; auto with arith.
simple induction 1; auto with arith.
Qed.



(****************************)
(* Lemmas about sets        *)
(****************************)


Lemma in_empty : forall x : V, ~ In empty x.
Proof.
unfold not, In, empty in |- *; trivial with arith.
Qed.
Hint Resolve in_empty.

Lemma in_allV : forall x : V, In all_ x.
Proof.
unfold In, all_ in |- *; trivial with arith.
Qed.
Hint Resolve in_allV.

Lemma incl_allV : forall W : set, incl W all_.
Proof.
red in |- *; auto with arith.
Qed.
Hint Resolve incl_allV.

Lemma incl_empty : forall W : set, incl empty W.
Proof.
red in |- *; intros W x H.
elim H.
Qed.
Hint Resolve incl_empty.

Lemma incl_Q_add : forall (Q : set) (x : V), incl Q (add Q x).
Proof.
exact in_Q_add.
Qed.
Hint Resolve incl_Q_add.

Lemma in_add_x : forall (Q : set) (x : V), In (add Q x) x.
Proof.
unfold In, add in |- *; auto with arith.
Qed.
Hint Resolve in_add_x.

Lemma add_in_or_eq :
 forall (Q : set) (x y : V), In (add Q x) y -> In Q y \/ x = y.
Proof.
auto with arith.
Qed.

Lemma incl_add :
 forall (Q Q' : set) (y : V), incl Q Q' -> incl (add Q y) (add Q' y).
Proof.
red in |- *; intros.
red in |- *; red in |- *.
elim H0; auto with arith.
Qed.
Hint Resolve incl_add.

Lemma In_not_In : forall (Q : set) (x y : V), In Q x -> ~ In Q y -> x <> y.
Proof.
red in |- *; intros.
apply H0; elim H1; auto with arith.
Qed.

Lemma In_not_In_sym :
 forall (Q : set) (x y : V), In Q x -> ~ In Q y -> y <> x.
Proof.
intros; apply sym_not_equal; apply (In_not_In Q); auto with arith.
Qed.

Lemma add_inh : forall (S : set) (x : V), inhabited (add S x).
Proof.
intros S x.
apply Def_inh with x; auto with arith.
Qed.
Hint Resolve add_inh.


Lemma incl_add_x :
 forall (S1 S2 : set) (x : V),
 ~ In S1 x -> incl (add S1 x) (add S2 x) -> incl S1 S2.
Proof.
intros S1 S2 x x_out_S1.
unfold incl, add, In in |- *.
intros H y y_in_S1.
elim (H y); auto with arith.
intro H_abs.
unfold In in x_out_S1.
absurd (S1 x); auto with arith.
rewrite H_abs; trivial with arith.
Qed.


Lemma incl_st_add_x :
 forall (S1 S2 : set) (x : V),
 ~ In S1 x -> incl_st (add S1 x) (add S2 x) -> incl_st S1 S2.
Proof.
intros S1 S2 x x_out_S1.
unfold incl_st in |- *.
simple induction 1.
intro H_incl.
simple induction 1.
intros y Def_y.
split.
apply incl_add_x with (x := x); trivial with arith.
exists y.
elim Def_y; intros H1 H2.
split.
apply Contra with (In (add S1 x) y); auto with arith.
unfold add, In at 1 in H2.
elim H2; auto with arith.
intro H_abs.
absurd (In (add S1 x) x); auto with arith.
Qed.


(********************************)
(*     Operations on sets       *)
(********************************)
    
Definition inter (P Q : set) (x : V) := In P x /\ In Q x.

Definition union (P Q : set) (x : V) := In P x \/ In Q x.

Definition soustr (Q : set) (x y : V) := In Q y /\ x <> y.


Lemma inter_incl_l : forall P Q : set, incl (inter P Q) P.
Proof.
red in |- *; intros P Q x H; elim H; auto with arith.
Qed.
Hint Resolve inter_incl_l.

Lemma inter_incl_r : forall P Q : set, incl (inter P Q) Q.
Proof.
red in |- *; intros P Q x H; elim H; auto with arith.
Qed.
Hint Resolve inter_incl_r.

Lemma inter_intro :
 forall (P Q : set) (x : V), In P x -> In Q x -> In (inter P Q) x.
Proof.
red in |- *; red in |- *; auto with arith.
Qed.
Hint Resolve inter_intro.

Lemma notP_notinterPQ :
 forall (P Q : set) (x : V), ~ In P x -> ~ In (inter P Q) x.
Proof.
intros P Q x.
unfold not, inter, In in |- *; auto with arith.
intros H1 H2; apply H1; elim H2; auto with arith.
Qed.
Hint Resolve notP_notinterPQ.

Lemma notQ_notinterPQ :
 forall (P Q : set) (x : V), ~ In Q x -> ~ In (inter P Q) x.
Proof.
intros P Q x.
unfold not, inter, In in |- *; auto with arith.
intros H1 H2; apply H1; elim H2; auto with arith.
Qed.
Hint Resolve notQ_notinterPQ.

Lemma union_sym : forall P Q : set, set_eq (union P Q) (union Q P).
Proof.
intros P Q.
apply Def_set_eq; unfold union, incl, In in |- *; simple induction 1;
 auto with arith.
Qed.
Hint Immediate union_sym: bdd.

Lemma P_union_empty : forall P : set, set_eq (union P empty) P.
Proof.
intro P.
apply Def_set_eq; unfold union, incl, In in |- *; try simple induction 1;
 auto with arith.
unfold empty in |- *; contradiction.
Qed.
Hint Resolve P_union_empty.

Lemma empty_union_P : forall P : set, set_eq (union empty P) P.
Proof.
intro P.
apply Def_set_eq; unfold union, incl, In in |- *; try simple induction 1;
 auto with arith.
unfold empty in |- *; contradiction.
Qed.
Hint Resolve empty_union_P.

Lemma union_add :
 forall (P Q : set) (x : V), set_eq (union (add P x) Q) (add (union P Q) x).
Proof.
intros P Q x.
apply Def_set_eq; unfold incl, union, add, In in |- *; simple induction 1;
 try simple induction 1; auto with arith.
Qed.

Lemma incl_soustr_in :
 forall (M : set) (y : V), In M y -> incl (soustr M y) M.
Proof.
red in |- *; intros.
elim H0; auto with arith.
Qed.
Hint Resolve incl_soustr_in.

Lemma incl_soustr :
 forall (M M' : set) (y : V), incl M M' -> incl (soustr M y) (soustr M' y).
Proof.
unfold soustr in |- *; red in |- *; red in |- *; intros.
elim H0; intros.
apply conj; auto with arith.
Qed.
Hint Resolve incl_soustr.

Lemma not_In_soustr :
 forall (M : set) (y z : V), ~ In M y -> ~ In (soustr M z) y.
Proof.
red in |- *; intros.
elim H0; intros; apply H; auto with arith.
Qed.
Hint Resolve not_In_soustr.

Lemma not_In_soustr_eq : forall (M : set) (y : V), ~ In (soustr M y) y.
Proof.
red in |- *; intros.
elim H; intros.
apply H1; auto with arith.
Qed.
Hint Resolve not_In_soustr_eq.

Lemma still_in_soustr :
 forall (M : set) (x : V),
 In M x -> forall y : V, x <> y -> In (soustr M y) x.
Proof.
intros M x x_in_M y x_ne_y.
unfold In, soustr in |- *; auto with arith.
Qed.

Lemma incl_soustr_add_l :
 forall (M : set) (y : V), incl (soustr (add M y) y) M.
Proof.
red in |- *; intros.
elim H; intros.
elim H0; intros; auto with arith.
absurd (y = x); auto with arith.
Qed.
Hint Resolve incl_soustr_add_l.

Lemma incl_soustr_add_r :
 forall (M : set) (y : V), ~ In M y -> incl M (soustr (add M y) y).
Proof.
red in |- *; intros.
red in |- *; red in |- *.
apply conj; auto with arith.
red in |- *; intro; absurd (In M x); auto with arith.
elim H1; auto with arith.
Qed.
Hint Resolve incl_soustr_add_r.

Lemma add_soustr_2 :
 forall (Q : set) (y : V), In Q y -> incl Q (add (soustr Q y) y).
Proof.
intros.
red in |- *; intros.
red in |- *; red in |- *.
unfold In, soustr in |- *.
elim (V_decidable y x); intro; auto with arith.
Qed.
Hint Resolve add_soustr_2.

Lemma add_soustr_1 :
 forall (Q : set) (y : V), In Q y -> incl (add (soustr Q y) y) Q.
Proof.
intros.
red in |- *; intros.
elim H0; intros.
elim H1; auto with arith.
elim H1; assumption.
Qed.
Hint Resolve add_soustr_1.

Lemma add_soustr_xy :
 forall (Q : set) (x y : V),
 x <> y -> set_eq (soustr (add Q x) y) (add (soustr Q y) x).
Proof.
intros Q x y x_diff_y.
apply Def_set_eq; unfold incl, soustr, add, In in |- *; intros z Def_z.
elim Def_z; intros H1 H2.
elim H1; auto with arith.
elim Def_z; try (simple induction 1; auto with arith).
Qed.
Hint Resolve add_soustr_xy.

Lemma incl_st_add_soustr :
 forall (E1 E2 : set) (x : V),
 ~ In E1 x -> incl_st (add E1 x) E2 -> incl_st E1 (soustr E2 x).
Proof.
intros E1 E2 x x_not_in_E1 H.
unfold incl_st in |- *.
unfold incl_st in H.
elim H; intros H_incl H_Ex.
split.
apply incl_trans with (soustr (add E1 x) x); auto with arith.
elim H_Ex; intros y Def_y.
exists y.
split; elim Def_y; intros H1 H2.
apply Contra with (In (add E1 x) y); auto with arith.
apply still_in_soustr; auto with arith.
Qed.

Lemma addQxinterS_addQinterSx :
 forall (Q S : set) (x : V),
 ~ In Q x -> In S x -> incl (inter (add Q x) S) (add (inter Q S) x).
Proof.
intros Q S x x_not_in_Q x_in_S.
unfold incl, inter, add, In in |- *.
intros y H_y.
elim H_y; intros Qy_or_xeqy y_in_S.
elim Qy_or_xeqy; auto with arith.
Qed.
Hint Resolve addQxinterS_addQinterSx.

Lemma addQinterSx_addQxinterS :
 forall (Q S : set) (x : V),
 ~ In Q x -> In S x -> incl (add (inter Q S) x) (inter (add Q x) S).
Proof.
intros Q S x x_not_in_Q x_in_S.
unfold incl, inter, add, In in |- *.
intros y H_y.
elim H_y.
intro Qy_and_Sy; split; elim Qy_and_Sy; auto with arith.
simple induction 1; auto with arith.
Qed.
Hint Resolve addQinterSx_addQxinterS.

Lemma addQxinterS_QinterS :
 forall (Q S : set) (x : V),
 ~ In Q x -> ~ In S x -> incl (inter (add Q x) S) (inter Q S).
Proof.
intros Q S x x_not_in_Q x_not_in_S.
unfold incl, inter, add, In in |- *.
intro y; simple induction 1.
simple induction 1; auto with arith.
intros Exy Sy; split; auto with arith.
absurd (S y); trivial with arith.
elim Exy; trivial with arith.
Qed.
Hint Resolve addQxinterS_QinterS.

Lemma QinterS_addQxinterS :
 forall (Q S : set) (x : V),
 ~ In Q x -> ~ In S x -> incl (inter Q S) (inter (add Q x) S).
Proof.
intros Q S x x_not_in_Q x_not_in_S.
unfold incl, inter, add, In in |- *.
intros y.
simple induction 1; intros.
split; auto with arith.
Qed.
Hint Resolve QinterS_addQxinterS.


(**************************)
(*   Image by functions   *)
(**************************)

Definition Im (Q : set) (f : V -> V) : set :=
  fun y : V => exists x : V, In Q x /\ f x = y.

Lemma Im_add :
 forall (Q : set) (y : V) (f : V -> V),
 set_eq (Im (add Q y) f) (add (Im Q f) (f y)).
Proof.
intros Q y f.
apply Def_set_eq; unfold incl, Im, add, In in |- *; intro fx.
simple induction 1; intro x.
do 2 simple induction 1; intros.
elim H1. (* H1 : (Q x)\/y=x *)
left.
exists x; auto with arith.
right.
rewrite H4; trivial with arith. (* H4 : y=x *)
right.
rewrite H2; trivial with arith. (* H2 : y=x *)
do 2 simple induction 1.
intro x.
simple induction 1.
intros.
exists x; auto with arith.
exists y; auto with arith.
Qed.


(*********************)
(*    Finite sets    *)
(*********************)

Inductive finite : set -> Prop :=
  | finite_empty : finite empty
  | finite_add :
      forall (y : V) (Q : set), ~ In Q y -> finite Q -> finite (add Q y).
Hint Resolve finite_empty finite_add.

Inductive cardinal : set -> nat -> Prop :=
  | card_empty : cardinal empty 0
  | card_add :
      forall (E : set) (k : nat) (x : V),
      cardinal E k -> ~ In E x -> cardinal (add E x) (S k).
Hint Resolve card_empty card_add.

Let inv_card (E : set) (k : nat) : Prop :=
  match k with
  | O => set_eq E empty
  | S _ => True
  end.
(* O  *) 
(* Sp *) 

Lemma cardinal_inv : forall (E : set) (n : nat), cardinal E n -> inv_card E n.
Proof.
simple induction 1; unfold inv_card in |- *; auto with arith.
Qed.

Lemma cardinalO_empty : forall E : set, cardinal E 0 -> set_eq E empty.
Proof.
intros E CardO.
change (inv_card E 0) in |- *.
apply cardinal_inv; trivial with arith.
Qed.

Lemma inh_card_gt_O :
 forall E : set, inhabited E -> forall c : nat, cardinal E c -> c > 0.
intros E HE.
elim HE.
intros e Def_e c Def_c.
elim (gt_O_eq c); auto with arith.
intro c_eq_O.
absurd (In E e); auto with arith.
pattern E in |- *.
apply extensionality with empty;
 try (unfold empty, In, not in |- *; contradiction).
apply set_eq_sym; apply cardinalO_empty.
rewrite c_eq_O; trivial with arith.
Qed.

Inductive decidable (S : set) : Prop :=
    Def_dec : (forall x : V, In S x \/ ~ In S x) -> decidable S.

Inductive decidable_on (Q S : set) : Prop :=
    Def_dec_on :
      (forall x : V, In Q x -> In S x \/ ~ In S x) -> decidable_on Q S.

Lemma inv_dec_on :
 forall Q S : set,
 decidable_on Q S -> forall x : V, In Q x -> In S x \/ ~ In S x.
Proof.
simple induction 1; auto with arith.
Qed.

Lemma dec_addQx_dec_Q :
 forall (Q : set) (P : V -> Prop) (x : V),
 decidable_on (add Q x) P -> decidable_on Q P.
Proof.
intros Q P x.
simple induction 1.
intro P_dec_on_addQx.
apply Def_dec_on; auto with arith.
Qed.

Lemma finite_cardinal :
 forall S : set, finite S -> exists k : nat, cardinal S k.
Proof.
intros E HE.
elim HE.
exists 0; trivial with arith.
intros y Q y_not_inQ Q_finite Ex_CardQ.
elim Ex_CardQ.
intros k Def_k.
exists (S k); auto with arith.
Qed.

Lemma cardinal_finite : forall (S : set) (c : nat), cardinal S c -> finite S.
Proof.
intros S c.
simple induction 1; auto with arith.
Qed.

Lemma decidable_finite :
 finite all_ -> forall S : set, decidable S -> finite S.
Proof.
intros V_finite S S_dec.
apply (extensionality (inter all_ S) S). 
apply Def_set_eq; auto with arith.
unfold incl, inter, In, all_ in |- *; simpl in |- *; auto with arith.
elim V_finite.
apply (extensionality empty (inter empty S)); auto with arith. 
intros x Q x_not_in_Q Q_finite Q_inter_S_finite.
elim S_dec.
intro Def_S_decidable.
elim (Def_S_decidable x).
(*   Case x in S  *)
intro x_in_S.
apply (extensionality (add (inter Q S) x) (inter (add Q x) S));
 auto with arith.
(*   Case x out of S *)
intro x_not_in_S.
apply (extensionality (inter Q S) (inter (add Q x) S)); auto with arith.
Qed.

Lemma finite_decidable : forall S : set, finite S -> decidable S.
Proof.
intro S.
simple induction 1.
apply Def_dec.
unfold empty in |- *; auto with arith.
intros y Q y_not_in_Q Q_finite Q_dec.
apply Def_dec.
unfold In, add in |- *.
elim Q_dec.
intros Def_Q_dec x.
elim (Def_Q_dec x); auto with arith.
intro not_in_Q_x.
elim (V_decidable x y); auto with arith.
intro x_ne_y.
right.
apply Morgan_or; auto with arith.
Qed.

Lemma card_soustr_1 :
 forall (Q : set) (n : nat),
 cardinal Q n -> forall y : V, In Q y -> cardinal (soustr Q y) (pred n).
Proof.
intros Q n.
simple induction 1.
intro y; unfold empty, In in |- *; contradiction.
clear H n Q.
intros Q n x Def_n H_n x_not_in_Q y y_in_addQx.
cut (In Q y \/ ~ In Q y).
simple induction 1.
(* subcase (In Q y) *)
intro H_in.
pattern (soustr (add Q x) y) in |- *.
apply (extensionality (add (soustr Q y) x) (soustr (add Q x) y)).
   (* Proof of set_eq *)
elim (V_decidable x y).
intro x_eq_y.
absurd (In Q y); auto with arith.
elim x_eq_y; auto with arith.
intro x_diff_y.
apply set_eq_sym; auto with arith.
cut (S (pred n) = pred (S n)).
intro H_pred.
elim H_pred.
apply card_add; auto with arith.
(* Use: H_n not_In_soustr *)
unfold pred at 2 in |- *; symmetry  in |- *.
apply S_pred with (m := 0).
change (n > 0) in |- *.
apply inh_card_gt_O with Q; auto with arith.
apply Def_inh with y; trivial with arith.
(* subcase ~(In Q y) *)
intro H_out.
elim (V_decidable x y).
intro x_eq_y.
elim x_eq_y.
pattern (soustr (add Q x) x) in |- *.
apply extensionality with Q; auto with arith.
intro x_diff_y.
absurd (In (add Q x) y); auto with arith.
unfold add, In at 1 in |- *.
apply Morgan_or; trivial with arith.
  (* (In Q y)\/(~(In Q y)) *)
cut (decidable Q).
simple induction 1; auto with arith.
apply finite_decidable.
apply cardinal_finite with n; trivial with arith.
Qed.

Lemma incl_st_card_lt :
 forall (E1 : set) (c1 : nat),
 cardinal E1 c1 ->
 forall (E2 : set) (c2 : nat), cardinal E2 c2 -> incl_st E1 E2 -> c2 > c1.
Proof.
simple induction 1.
(* E1 empty *)
simple induction 1.
   (* E2 empty *)
unfold incl_st in |- *.
simple induction 1.
intro empty_incl_empty.
simple induction 1.
intro e.
simple induction 1; intros; absurd (In empty e); auto with arith.
   (* E2 -> (add E2 x) *)
auto with arith.
(* E1 -> (add E1 x) *)
clear H E1 c1.
intros E1 c1 x1 Def_c1 H_E1 x1_not_in_E1 E2 c2 Def_c2.
elim Def_c2.
   (* E2 empty *)
unfold incl_st in |- *.
simple induction 1; intro H_abs1.
simple induction 1; intro e.
simple induction 1; intros; absurd (In empty e); auto with arith.
   (*  E2 -> (add E2 x) *)
clear Def_c2 c2 E2.
intros E2 c2 x2 Def_c2 H_E1x x2_not_in_E2 H.
elimtype (In E2 x1 \/ ~ In E2 x1); try intro Hx1.
(* subcase (In E2 x1) *)
apply gt_n_S.
apply H_E1 with (E2 := soustr (add E2 x2) x1);
 try (apply incl_st_add_soustr; auto with arith).
elimtype (pred (S c2) = c2); auto with arith.
apply card_soustr_1; auto with arith.
(* subcase ~(In E2 x1) *)
elim (V_decidable x1 x2); intro Hx1x2.
   (* x1 = x2 *)
apply gt_n_S.
apply H_E1 with (E2 := E2); try trivial with arith.
apply incl_st_add_x with (x := x1); auto with arith.
pattern x1 at 2 in |- *; rewrite Hx1x2; trivial with arith.
    (* x1 =/= x2 *)
absurd (In (add E2 x2) x1).
unfold add, In at 1 in |- *.
apply Morgan_or; auto with arith.
unfold incl_st in H.
elim H.
intros H_incl H_Ex.
unfold incl in H_incl; auto with arith.
(* Proof of Cut (In E2 x1) \/ ~(In E2 x1) *)
cut (decidable E2).
simple induction 1; auto with arith.
apply finite_decidable.
apply cardinal_finite with (c := c2); trivial with arith.
Qed.

Lemma finite_union :
 forall E1 E2 : set, finite E1 -> finite E2 -> finite (union E1 E2).
Proof.
intros E1 E2.
simple induction 1.
intro E2_finite.
apply (extensionality E2 (union empty E2)); auto with arith bdd.
intros y Q y_not_in_Q Q_finite HQ E2_finite.
apply (extensionality (add (union Q E2) y) (union (add Q y) E2));
 try (apply set_eq_sym; apply union_add; auto with arith).
elimtype (In E2 y \/ ~ In E2 y).
(* (In E2 y)->(finite (add (union Q E2) y)) *)
intro y_in_E2.
apply (extensionality (union Q E2) (add (union Q E2) y)); auto with arith.
apply Def_set_eq; unfold incl, union, add, In in |- *; auto with arith.
unfold In in y_in_E2.
do 3 (simple induction 1; auto with arith).
(*  (~(In E2 y))->(finite (add (union Q E2) y)) *)
intro y_notin_E2.
apply finite_add; auto with arith.
unfold union, In in |- *.
apply Morgan_or; auto with arith.
cut (decidable E2); try (apply finite_decidable; auto with arith).
simple induction 1; auto with arith.
Qed.

Lemma finite_image :
 forall (E : set) (f : V -> V), finite E -> finite (Im E f).
Proof.
intros E f.
simple induction 1.
(* (finite (Im empty f)) *)
apply (extensionality empty (Im empty f)); auto with arith.
apply Def_set_eq; unfold Im, empty, In in |- *; auto with arith.
unfold incl, In in |- *; do 2 simple induction 1; auto with arith.
(* (finite (Im Q f))->(finite (Im (add Q y) f)) *)
intros y Q y_notin_Q Q_finite ImQ_finite.
apply (extensionality (add (Im Q f) (f y)) (Im (add Q y) f));
 try (apply set_eq_sym; apply Im_add).
cut (decidable (Im Q f)); try (apply finite_decidable; auto with arith).
simple induction 1.
intro ImQ_dec.
elim (ImQ_dec (f y)); auto with arith.
intro fy_in_ImQ.
apply (extensionality (Im Q f) (add (Im Q f) (f y))); auto with arith.
apply Def_set_eq; unfold incl, add in |- *; auto with arith.
unfold In at 2 in |- *; auto with arith.
intro x.
unfold In at 1 in |- *; simple induction 1; auto with arith;
 simple induction 1; auto with arith.
Qed.

Lemma inv_inh_addQx :
 forall (Q : set) (x : V),
 finite Q -> inhabited (add Q x) -> inhabited Q \/ set_eq Q empty.
Proof.
intros Q' x'.
simple induction 1; auto with arith.
Qed.

Lemma notall_addQx_notall_Q :
 forall (Q : set) (P : V -> Prop) (x : V),
 P x ->
 ~ (forall y : V, In (add Q x) y -> P y) -> ~ (forall y : V, In Q y -> P y).
Proof.
intros Q P x H_Px.
unfold not in |- *.
intros H1 H2.
apply H1.
intros y; unfold In, add in |- *; simple induction 1; auto with arith.
simple induction 1; assumption.
Qed.

Lemma notall_existnot_singleton :
 forall (P : V -> Prop) (x : V),
 decidable_on (add empty x) P ->
 ~ (forall y : V, In (add empty x) y -> P y) -> ~ P x.
Proof.
intros P x singlx_dec singlx_notall.
cut (In P x \/ ~ In P x); try apply inv_dec_on with (add empty x);
 auto with arith.
simple induction 1; unfold In in |- *; auto with arith.
intro Px.
absurd (forall y : V, In (add empty x) y -> P y); auto with arith.
intros y y_in_singlx.
elim (singlx x y); auto with arith.
Qed.

Lemma onQ_not_All_Exist_not :
 forall (Q : set) (P : V -> Prop),
 finite Q ->
 inhabited Q ->
 decidable_on Q P ->
 ~ (forall x : V, In Q x -> P x) -> exists x : V, In Q x /\ ~ P x.
Proof.
intros Q' P'.
simple induction 1. (*---- Q = empty ------*)
intros H_inh H_dec H_notall.
absurd (inhabited empty); auto with arith.
unfold not in |- *; simple induction 1; unfold In in |- *; auto with arith.
(*---- Q -> (add Q x) -----*)
intros x Q x_not_in_Q Q_finite H_Q addQx_inh addQx_dec addQx_notall.
elim (inv_inh_addQx Q x); auto with arith.
      (* Q inhabited  *)
intro Q_inh.
elimtype (P' x \/ ~ P' x).
         (* case  (P' x) *)
intro H_P'x.
elim H_Q; auto with arith.
intro t; simple induction 1.
intros t_in_Q not_P't.
exists t; auto with arith.
apply dec_addQx_dec_Q with x; trivial with arith.
apply notall_addQx_notall_Q with x; trivial with arith.
         (* case ~(P' x) *)
intro H_not_P'x.
exists x; auto with arith.
   (* Proof of (P' x)\/~(P' x) *)
change (In P' x \/ ~ In P' x) in |- *; apply inv_dec_on with (add Q x);
 trivial with arith.
(*-----  Q uninhabited  -----*)
intro Q_eq_empty.
exists x; split; auto with arith.
apply notall_existnot_singleton; pattern empty in |- *;
 apply extensionality with Q; auto with arith; elim Q_eq_empty;
 auto with arith.
Qed.

(*---------------------------------------------------------------------------*)
  Lemma not_Exist_All_not
   : (*  Trivial with arith for any set V even infinite *)
   forall P : V -> Prop, ~ (exists x : V, P x) -> forall x : V, ~ P x.
(*---------------------------------------------------------------------------*)
Proof.
unfold not in |- *; intros P not_exist x H_Px.
apply not_exist; exists x; auto with arith.
Qed.

(*---------------------------------------------------------------------------*)
  Lemma not_All_Exist_not :
   forall P : V -> Prop,
   finite all_ ->
   inhabited all_ ->
   decidable P -> ~ (forall x : V, P x) -> exists x : V, ~ P x.
(*---------------------------------------------------------------------------*)
Proof.
intros P V_finite V_inhabited P_dec not_all_P.
elim (onQ_not_All_Exist_not all_ P); auto with arith.
intro x; simple induction 1.
intros Triv not_Px.
exists x; auto with arith.
apply Def_dec_on.
change (forall x : V, True -> In P x \/ ~ In P x) in |- *.
elim P_dec; auto with arith.
Qed.

Lemma P_dec_on_Q_AllP_dec_on_Q :
 forall Q : set,
 finite Q ->
 forall P : V -> Prop,
 decidable_on Q P ->
 (forall x : V, In Q x -> P x) \/ ~ (forall x : V, In Q x -> P x).
Proof.
simple induction 1.
(*  Q = empty  *)
intros P P_dec.
left.
intro x; unfold In, empty in |- *; contradiction.
(*  Q -> (add Q x) *)
clear H Q.
intros x Q x_not_in_Q Q_finite H_Q P P_dec_addQx.
elim (H_Q P).
   (* Case P(x) for all x in Q *)
intro AllP_onQ.
elimtype (P x \/ ~ P x);
 [ idtac
 | idtac
 | change (In P x \/ ~ In P x) in |- *; apply inv_dec_on with (Q := add Q x);
    auto with arith ].
intro Px.
left.
intro v.
unfold add, In in |- *; simple induction 1; auto with arith.
simple induction 1; trivial with arith.
right.
unfold not in |- *.
intro H_absurde.
absurd (P x); auto with arith.
   (* Case not P(x) for all x in Q *)
intro not_AllP_onQ.
right.
unfold not in not_AllP_onQ.
unfold not in |- *.
intro H.
apply not_AllP_onQ.
intros v v_in_Q.
apply H; auto with arith.
(* (decidable_on Q P) *)
apply dec_addQx_dec_Q with (x := x); trivial with arith.
Qed.

(*--------------------------------------------------------------------------*)
 Lemma P_dec_AllP_dec :
  finite all_ ->
  forall P : V -> Prop,
  decidable P -> (forall x : V, P x) \/ ~ (forall x : V, P x).
(*--------------------------------------------------------------------------*)
Proof.
intros V_finite P P_dec.
elim (P_dec_on_Q_AllP_dec_on_Q all_ V_finite P); auto with arith.
(* (decidable_on all_ P) *)
apply Def_dec_on.
change (forall x : V, True -> In P x \/ ~ In P x) in |- *.
elim P_dec; auto with arith.
Qed.


(*****************************)
(*       Ordered sets        *)
(*****************************)

Variable R : V -> V -> Prop.
Variable V_eq : V -> V -> Prop.
Definition reflexivity := forall x : V, R x x.
Definition anti_symetry := forall x y : V, R x y -> R y x -> V_eq x y.
Definition transitivity := forall x y z : V, R x y -> R y z -> R x z.

Definition order := reflexivity /\ anti_symetry /\ transitivity.

Definition totality := forall x y : V, R x y \/ R y x.
Definition total_order := order /\ totality.

Inductive greatest (E : set) (g : V) : Prop :=
    Def_greatest : In E g -> (forall y : V, In E y -> R y g) -> greatest E g.

Lemma inv_greatest_In : forall (E : set) (g : V), greatest E g -> In E g.
Proof.
simple induction 1; auto with arith.
Qed.
Hint Resolve inv_greatest_In.

Lemma inv_greatest_R :
 forall (E : set) (g : V), greatest E g -> forall y : V, In E y -> R y g.
Proof.
simple induction 1; auto with arith.
Qed.

Section Greatest.
 Hypothesis R_total_order : total_order.

(*---------------------------------------------------------------------------*)
  Lemma Card_gtO_exist_greatest :
   forall (E : set) (c : nat),
   cardinal E c -> c > 0 -> exists g : V, greatest E g.
(*---------------------------------------------------------------------------*)
Proof.
simple induction 1.
(* c = O *)
intro Habs.
absurd (0 > 0); auto with arith.
(* E ->(add E x) *)
clear H c E.
intros E cE x Def_cE H_E x_not_in_E H_triv.
elim (gt_O_eq cE).
  (* subcase cE > O *)
intro cE_gt_O.
elim H_E; auto with arith.
intros gE Def_gE.
elim R_total_order.
intros R_order R_total.
unfold totality in R_total.
elim (R_total x gE).
(* (R x gE) -> (Ex([g:V](greatest (add E x) g))) *)
intro x_R_gE.
exists gE; apply Def_greatest.
unfold add, In in |- *; left; change (In E gE) in |- *; auto with arith.
intro y; unfold add in |- *; unfold In at 1 in |- *.
simple induction 1.
intro y_in_E; apply inv_greatest_R with (E := E); auto with arith.
simple induction 1; trivial with arith.
(*  (R gE x) -> (Ex([g:V](greatest (add E x) g))) *)
intro gE_R_x.
exists x; apply Def_greatest; auto with arith.
intro y; unfold add in |- *; unfold In at 1 in |- *.
unfold order in R_order.
elim R_order.
intros R_refl Rasym_and_trans.
unfold reflexivity in R_refl.
elim Rasym_and_trans.
intros R_asym R_trans.
unfold transitivity in R_trans.
simple induction 1; try simple induction 1; auto with arith.
intro y_in_E.
apply R_trans with (y := gE); auto with arith.
apply inv_greatest_R with (E := E); auto with arith.
  (* subcase cE=O *)
intro cE_eq_O.
exists x.
apply Def_greatest; auto with arith.
pattern E in |- *; apply extensionality with (U := empty).
apply set_eq_sym.
change (inv_card E 0) in |- *.
apply cardinal_inv.
rewrite cE_eq_O; trivial with arith.
intro y.
unfold add, empty, In in |- *.
elim R_total_order.
intros R_order R_total.
elim R_order.
intros Rrefl Rasym_and_trans.
unfold reflexivity in Rrefl.
simple induction 1; [ contradiction | simple induction 1; auto with arith ].
Qed.

End Greatest.
End sets.

Hint Resolve in_empty in_allV incl_allV incl_empty incl_Q_add in_add_x
  finite_empty finite_add set_eq_refl.
