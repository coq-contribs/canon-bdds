(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*           Definitions and lemmas about Paths, Implicants and Primes      *)
(*                                                                          *)
(****************************************************************************)
(*                              Prelude_Paths.v                             *)
(****************************************************************************)


Require Export List.
Require Import Prelude_BDT.
Require Import bdd.rauzy.algorithme1.Boolean_functions.
Require Import bdd.rauzy.algorithme1.BDTs.

(*-------------                    Paths                    --------------*)

Definition Path := list nat.
Definition Cons := cons (A:=nat).
Definition Nil := nil (A:=nat).
Definition Of := In (A:=nat).    
Hint Unfold Of.

Lemma Of_path_dec : forall (p : Path) (i : nat), Of i p \/ ~ Of i p.
Proof.
exact (In_list_dec nat eq_nat_dec).
Qed.

Lemma I_of_cons_ip : forall (p : Path) (i : nat), Of i (Cons i p).
Proof.
simpl in |- *; auto with v62.
Qed.
Hint Resolve I_of_cons_ip.

Lemma Of_p_of_cons_ip :
 forall (p : Path) (i j : nat), Of j p -> Of j (Cons i p).
Proof.
intros p i j.
unfold Of, Cons in |- *; auto with v62.
Qed.
Hint Resolve Of_p_of_cons_ip.

Lemma Of_cons_ip_of_p :
 forall (p : Path) (i j : nat), Of j (Cons i p) -> i <> j -> Of j p.
Proof.
intros p i j.
unfold Of at 1 in |- *; simpl in |- *; simple induction 1;
 [ intro; simple induction 1; assumption | trivial with v62 ].
Qed.

Lemma Not_of_cons_ip :
 forall (p : Path) (i j : nat), ~ Of j p -> i <> j -> ~ Of j (Cons i p).
Proof.
intros.
change (~ (i = j \/ Of j p)) in |- *.
apply deMorgan_not_or; trivial with v62.
Qed.
Hint Resolve Not_of_cons_ip.

Lemma Nil_or_not_Nil : forall p : Path, p = Nil \/ (exists k : nat, Of k p).
Proof.
simple induction p.
auto with v62.
intros a tl H.
right; exists a; auto with v62.
Qed.

Lemma Empty_is_Nil : forall p : Path, (forall i : nat, ~ Of i p) -> p = Nil.
Proof.
intro p; elim (Nil_or_not_Nil p); auto with v62.
simple induction 1; intros k Hk Hp; absurd (Of k p); auto with v62.
Qed.




(*----------     Inclusion of paths   =   Division of products    -----------*)


Definition Divides (p1 p2 : Path) := forall i : nat, Of i p1 -> Of i p2.

Lemma Divides_reflexive : forall p : Path, Divides p p.
Proof.
unfold Divides in |- *; auto with v62.
Qed.
Hint Resolve Divides_reflexive.


Lemma Divides_trans :
 forall p1 p2 p3 : Path, Divides p1 p2 -> Divides p2 p3 -> Divides p1 p3.
Proof.
unfold Divides in |- *; auto with v62.
Qed.

Lemma Divides_p_cons_ip : forall (p : Path) (i : nat), Divides p (Cons i p).
Proof.
unfold Divides in |- *.
intros p i; exact (Of_p_of_cons_ip p i).
Qed.
Hint Resolve Divides_p_cons_ip.

Lemma Nil_divides_all : forall p : Path, Divides Nil p.
Proof.
unfold Divides, Of, Nil in |- *; exact (nil_included_all nat).
Qed.

Lemma Divides_Nil_is_Nil : forall p : Path, Divides p Nil -> p = Nil.
Proof.
intro p.
unfold Divides in |- *; intro H.
apply Empty_is_Nil; exact H.
Qed.

Lemma L8 :
 forall (p1 p2 : Path) (i : nat),
 Divides p1 (Cons i p2) -> ~ Of i p1 -> Divides p1 p2.
Proof.
intros p1 p2 i H1 H2.
unfold Divides in |- *.
intros j Hj.
elim (H1 j Hj);
 [ intro Habs; absurd (Of j p1); [ elim Habs; assumption | assumption ]
 | trivial with v62 ].
Qed.

Lemma L80 :
 forall (p1 p2 : Path) (i : nat), Divides p1 p2 -> ~ Of i p2 -> ~ Of i p1.
Proof.
intros p1 p2 i.
unfold Divides in |- *; intros H1 H2.
apply Contra with (Of i p2); auto with v62.
Qed.

Lemma Divides_tail_divides_cons :
 forall (p1 p2 : Path) (i : nat),
 Divides p1 p2 -> Divides (Cons i p1) (Cons i p2).
Proof.
intros p1 p2 i.
unfold Divides in |- *; intros H1 j; simpl in |- *.
simple induction 1; auto with v62.
Qed.
Hint Resolve Divides_tail_divides_cons.


(*-----------     Ordered paths  (for solutions of BDT)       -------------*)


Definition Head (p : Path) :=
  match p return nat with
  | nil =>
      (*   Nil   *)  0
      (* [i,tlp] *) 
  | i :: tlp => i
  end.

Lemma Tail_exists :
 forall (p : Path) (i : nat),
 Of i p -> exists p' : Path, p = Cons (Head p) p'.
Proof.
simple induction p.
intros.
absurd (Of i nil); try assumption.
unfold Of in |- *; simpl in |- *; contradiction.
clear p.
intros j p Hp i Hi.
exists p; trivial with v62.
Qed.

Lemma Head_of_p_in_p : forall (p : Path) (i : nat), Of i p -> Of (Head p) p.
Proof.
simple induction p; [ simpl in |- *; contradiction | auto with v62 ].
Qed.


Inductive Ordered : Path -> Prop :=
  | Nil_ordered : Ordered Nil
  | Cons_ordered :
      forall p : Path,
      Ordered p -> forall i : nat, i > Head p -> Ordered (Cons i p).

Hint Resolve Nil_ordered Cons_ordered.


Definition inv_Ordered (p : Path) :=
  match p return Prop with
  | nil =>
      (*   Nil   *)  True
      (* [i,tlp] *) 
  | i :: tlp => i > Head tlp /\ Ordered tlp
  end.


Lemma p_inv_Ordered : forall p : Path, Ordered p -> inv_Ordered p.
Proof.
simple induction 1; simpl in |- *; auto with v62.
Qed.
Hint Resolve p_inv_Ordered.

Lemma Ordered_cons_ordered_tail :
 forall (i : nat) (p : Path), Ordered (Cons i p) -> Ordered p.
Proof.
intros i p H.
elim (p_inv_Ordered (Cons i p) H); auto with v62.
Qed.

Lemma L11 : forall (i : nat) (p : Path), Ordered (Cons i p) -> ~ Of i p.
Proof.
intro i; simple induction p;
 [ intro; exact (in_nil (a:=i)) | clear p; intros j q Hq H ].
change (~ (j = i \/ Of i q)) in |- *.
apply deMorgan_not_or.
apply Contra with (i = j); [ auto with v62 | apply gt_neq ].
elim (p_inv_Ordered (Cons i (Cons j q))); auto with v62.
apply Hq.
elim (p_inv_Ordered (Cons j q));
 [ intros H1 H2 | apply Ordered_cons_ordered_tail with i; assumption ].
apply Cons_ordered;
 [ assumption
 | apply gt_trans with j;
    [ elim (p_inv_Ordered (Cons i (Cons j q))); auto with v62 | assumption ] ].
Qed.

Lemma Head_max_of_ordered_path :
 forall p : Path, Ordered p -> forall i : nat, Of i p -> i <= Head p.
Proof.
simple induction 1;
 [ simpl in |- *; contradiction | clear H p; intros p Hp Hrec i Hi j Hj ].
simpl in |- *; simpl in Hj.
elim Hj; [ simple induction 1; trivial with v62 | intro ].
apply gt_le_weak; apply gt_le_trans with (Head p); auto with v62.
Qed.

Lemma La_4bis :
 forall p : Path,
 Ordered p ->
 forall i : nat, Of i p -> (forall j : nat, j > i -> ~ Of j p) -> i = Head p.
Proof.
intros p Hp i H1i H2i.
elim (le_lt_or_eq i (Head p) (Head_max_of_ordered_path p Hp i H1i));
 [ intro Habsurde | trivial with v62 ].
absurd (Of (Head p) p);
 [ apply H2i; apply lt_gt; assumption
 | apply Head_of_p_in_p with i; assumption ].
Qed. 

Lemma Divides_cons_divides_tail :
 forall (p1 p2 : Path) (i : nat),
 Ordered (Cons i p1) ->
 Ordered (Cons i p2) -> Divides (Cons i p1) (Cons i p2) -> Divides p1 p2.
Proof.
intros p1 p2 i H1 H2.
unfold Divides in |- *; simpl in |- *.
intros H j Hj.
elim (H j); [ idtac | trivial with v62 | auto with v62 ].
intro Habsurde.
absurd (Of i p1); [ exact (L11 i p1 H1) | rewrite Habsurde; assumption ].
Qed.

Lemma Pth_ord8 :
 forall p : Path, Ordered p -> forall i : nat, Of i p -> i > 0.
Proof.
simple induction 1.
intros i Hi.
absurd (Of i Nil); [ exact (in_nil (a:=i)) | assumption ].
clear H p; intros p H Hrec i Hi j Hj.
unfold Of in Hj; elim Hj.
  (* case i=j *)
simple induction 1; apply gt_le_trans with (Head p); auto with v62.
  (* case j in p *)
auto with v62.
Qed.

Lemma Pth_ord9 :
 forall (i : nat) (p1 : Path),
 Ordered (Cons i p1) ->
 forall p2 : Path, Ordered p2 -> Divides p2 p1 -> Ordered (Cons i p2).
Proof.
simple induction p2.
  (* case p2=nil *)
intros.
apply Cons_ordered;
 [ assumption | apply (Pth_ord8 (Cons i p1) H i); auto with v62 ].
  (* case p2=/= nil *)  
clear p2; intros hp2 tlp2 Hrec Hp2 Hdiv.
apply Cons_ordered; try assumption.
apply gt_le_trans with (Head p1);
 [ elim (p_inv_Ordered (Cons i p1) H); auto with v62
 | apply Head_max_of_ordered_path ].
elim (p_inv_Ordered (Cons i p1) H); auto with v62.
unfold Divides in Hdiv.
apply Hdiv; apply Head_of_p_in_p with (i := hp2); auto with v62.
Qed.

Lemma Cons_equal_head_equal :
 forall (i1 : nat) (tl1 : Path),
 Ordered (Cons i1 tl1) ->
 forall (i2 : nat) (tl2 : Path),
 Ordered (Cons i2 tl2) ->
 Divides (Cons i1 tl1) (Cons i2 tl2) ->
 Divides (Cons i2 tl2) (Cons i1 tl1) -> i1 = i2.
Proof.
intros i1 tl1 HO1 i2 tl2 HO2 Hdiv1 Hdiv2.
apply le_antisym.
change (Head (Cons i1 tl1) <= Head (Cons i2 tl2)) in |- *.
apply Head_max_of_ordered_path; auto with v62.
change (Head (Cons i2 tl2) <= Head (Cons i1 tl1)) in |- *.
apply Head_max_of_ordered_path; auto with v62.
Qed.

Lemma Ordered_paths_eq :
 forall p1 : Path,
 Ordered p1 ->
 forall p2 : Path, Ordered p2 -> Divides p1 p2 -> Divides p2 p1 -> p1 = p2.
Proof.
simple induction 1; clear H p1.
simple induction 1; try clear H p2.
(* case Nil Nil *)
trivial with v62.
(* case Nil Cons *)
intros p1 HO1 Hrec1 i Hi Hdiv1 Hdiv2.
unfold Divides in Hdiv2.
absurd (Of i Nil); [ exact (in_nil (a:=i)) | auto with v62 ].
intros tl1 HO_tl1 Hrec_tl1 i1 Hi1.
simple induction 1.
(* case Cons Nil *)
intro Hdiv1.
unfold Divides in Hdiv1.
absurd (Of i1 Nil); [ exact (in_nil (a:=i1)) | auto with v62 ].
(* case Cons Cons *)
intros tl2 HO_tl2 Hrec_tl2 i2 Hi2 Hdiv1 Hdiv2.
elim (Hrec_tl1 tl2 HO_tl2).
elim
 (Cons_equal_head_equal i1 tl1 (Cons_ordered tl1 HO_tl1 i1 Hi1) i2 tl2
    (Cons_ordered tl2 HO_tl2 i2 Hi2) Hdiv1 Hdiv2); 
 trivial with v62.
apply (Divides_cons_divides_tail tl1 tl2 i1);
 [ auto with v62
 | pattern i1 in |- *;
    rewrite
     (Cons_equal_head_equal i1 tl1 (Cons_ordered tl1 HO_tl1 i1 Hi1) i2 tl2
        (Cons_ordered tl2 HO_tl2 i2 Hi2) Hdiv1 Hdiv2)
     ; auto with v62
 | pattern i1 at 2 in |- *;
    rewrite
     (Cons_equal_head_equal i1 tl1 (Cons_ordered tl1 HO_tl1 i1 Hi1) i2 tl2
        (Cons_ordered tl2 HO_tl2 i2 Hi2) Hdiv1 Hdiv2)
     ; assumption ].
apply (Divides_cons_divides_tail tl2 tl1 i1);
 [ pattern i1 in |- *;
    rewrite
     (Cons_equal_head_equal i1 tl1 (Cons_ordered tl1 HO_tl1 i1 Hi1) i2 tl2
        (Cons_ordered tl2 HO_tl2 i2 Hi2) Hdiv1 Hdiv2)
     ; auto with v62
 | auto with v62
 | pattern i1 at 1 in |- *;
    rewrite
     (Cons_equal_head_equal i1 tl1 (Cons_ordered tl1 HO_tl1 i1 Hi1) i2 tl2
        (Cons_ordered tl2 HO_tl2 i2 Hi2) Hdiv1 Hdiv2)
     ; assumption ].
Qed.

Lemma Ordered_divisor_of_cons_ip :
 forall (i : nat) (p : Path),
 Ordered (Cons i p) ->
 forall p' : Path,
 Divides p' (Cons i p) ->
 Ordered p' -> Of i p' -> exists tl' : Path, p' = Cons i tl'.
Proof.
intros i p HO p' H1 H2 H3.
elim (Tail_exists p' i H3); intros tl' Def_tl'.
exists tl'.
rewrite (La_4bis p' H2 i H3); [ trivial with v62 | intros j Hj ].
unfold not in |- *; intro Habs; absurd (j > i);
 [ unfold Divides in H1; apply le_not_gt | assumption ].
change (j <= Head (Cons i p)) in |- *; apply Head_max_of_ordered_path;
 auto with v62.
Qed.


(*------------------         Solutions of a BDT       --------------------*)

Inductive Solution : Path -> BDT -> Prop :=
  | Sol_One : Solution Nil One
  | Sol_Left :
      forall (i : nat) (h l : BDT) (p : Path),
      Solution p h -> Solution (Cons i p) (Node i h l)
  | Sol_Right :
      forall (i : nat) (h l : BDT) (p : Path),
      Solution p l -> Solution p (Node i h l).

Hint Resolve Sol_One Sol_Left Sol_Right.


Definition Inv_Solution (p : Path) (b : BDT) :=
  match b return Prop with
  | Zero =>
      (* Zero *)  False
      (* One  *) 
  | One => p = Nil :>Path
      (* Node(i,h,l) *) 
  | Node i h l =>
      Solution p l \/ (exists p' : Path, Solution p' h /\ p = Cons i p')
  end.

Hint Unfold Inv_Solution.


Lemma p_inv_Solution :
 forall (p : Path) (b : BDT), Solution p b -> Inv_Solution p b.
Proof.
simple induction 1; [ auto with v62 | idtac | auto with v62 ].
clear H b p.
intros i h l p Def_p H.
unfold Inv_Solution in |- *.
right; exists p; auto with v62.
Qed.
Hint Resolve p_inv_Solution.

Lemma No_solution_Zero : forall p : Path, ~ Solution p Zero.
Proof.
unfold not in |- *; intros p H.
change (Inv_Solution p Zero) in |- *; auto with v62.
Qed.

Lemma Solution_of_One_is_Nil : forall p : Path, Solution p One -> p = Nil.
Proof.
intros.
change (Inv_Solution p One) in |- *; auto with v62.
Qed.

Lemma L1 :
 forall (i : nat) (h l : BDT) (p : Path),
 Solution p (Node i h l) ->
 Solution p l \/ (exists p' : Path, Solution p' h /\ p = Cons i p').
Proof.
intros i h l p H.
change (Inv_Solution p (Node i h l)) in |- *; auto with v62.
Qed.

Lemma Head_of_solution_le_dim :
 forall (p : Path) (b : BDT), Solution p b -> OBDT b -> Head p <= Dim b.
Proof.
simple induction 1;
 [ auto with v62
 | auto with v62
 | clear H p b; intros i h l p Def_p Hrec HO ].
apply le_trans with (Dim l);
 [ apply Hrec; elim (ordered_node_ordered_sons i h l HO); auto with v62
 | apply gt_le_weak; elim (dim_node_dim_sons i h l); auto with v62 ].
Qed.

Lemma Solution_OBDT_ordered :
 forall (b : BDT) (p : Path), Solution p b -> OBDT b -> Ordered p.
Proof.
simple induction 1;
 [ auto with v62
 | clear H p b; intros i h l p Def_p Hrec Hnode
 | clear H p b; intros i h l p Def_p Hrec Hnode ].
apply Cons_ordered.
apply Hrec; elim (ordered_node_ordered_sons i h l Hnode); auto with v62.
apply gt_le_trans with (Dim h);
 [ elim (dim_node_dim_sons i h l); auto with v62
 | apply (Head_of_solution_le_dim p h Def_p);
    elim (ordered_node_ordered_sons i h l Hnode); auto with v62 ].
apply Hrec; elim (ordered_node_ordered_sons i h l Hnode); auto with v62.
Qed.

Lemma Gt_dim_out_of_solution :
 forall (b : BDT) (p : Path),
 Solution p b -> OBDT b -> forall i : nat, i > Dim b -> ~ Of i p.
Proof.
intros b p Def_p Hb i Hi.
unfold not in |- *; intro Habsurde.
absurd (i > i); [ auto with v62 | apply gt_le_trans with (Head p) ].
apply gt_le_trans with (Dim b);
 [ assumption | exact (Head_of_solution_le_dim p b Def_p Hb) ].
exact
 (Head_max_of_ordered_path p (Solution_OBDT_ordered b p Def_p Hb) i Habsurde).
Qed.

Lemma Tail_exists_with_dim_head :
 forall (i : nat) (h l : BDT),
 OBDT (Node i h l) ->
 forall p : Path,
 Solution p (Node i h l) ->
 forall p' : Path,
 Ordered p' ->
 Of i p' -> Divides p' p -> exists tlp' : Path, p' = Cons i tlp'.
Proof.
intros i h l HO p Def_p p' H1p' H2p' H3p'.
elim (Tail_exists p' i H2p'); intros tlp' Def_tlp'.
exists tlp'.
elim (le_antisym (Head p') i);
 [ assumption | idtac | exact (Head_max_of_ordered_path p' H1p' i H2p') ].
apply le_trans with (Head p);
 [ idtac | exact (Head_of_solution_le_dim p (Node i h l) Def_p HO) ].
apply Head_max_of_ordered_path;
 [ exact (Solution_OBDT_ordered (Node i h l) p Def_p HO) | idtac ].
unfold Divides in H3p'; apply H3p'.
pattern p' at 2 in |- *; rewrite Def_tlp'; trivial with v62.
Qed.

Lemma LT1 :
 forall b : BDT, OBDT b -> b = Zero \/ (exists p : Path, Solution p b).
Proof.
simple induction 1;
 [ auto with v62
 | right; exists Nil; trivial with v62
 | intros l r HOl Hl HOr Hr i H1i H2i Hsons ].
elim Hr; [ intro Hr0 | simple induction 1; intros sr Def_sr ].
elim Hl; [ intro Hl0 | simple induction 1; intros sl Def_sl ].
clear Hl. clear Hr.
elim Hsons; rewrite Hl0; rewrite Hr0; trivial with v62.
right; exists (Cons i sl); auto with v62.
right; exists sr; auto with v62.
Qed.


(*--------------      Assignments defined by a Path        --------------*)


Definition Assignment_of (p : Path) (A : Assign) :=
  (forall i : nat, Of i p -> A i = true) /\
  (forall i : nat, ~ Of i p -> A i = false).

Lemma Ass_of_well_defined :
 forall p : Path, exists A : Assign, Assignment_of p A.
Proof.
simple induction p.
(*  p=Nil  *)
exists (fun i : nat => false).
unfold Assignment_of in |- *; split;
 [ intros i Habs; absurd (Of i nil); try assumption; unfold Of in |- *;
    exact (in_nil (a:=i))
 | trivial with v62 ].
(*  p=Cons(a,l)  *)
intros a l.
simple induction 1; intros Al Def_Al; clear H.
unfold Assignment_of in Def_Al; elim Def_Al; intros HAl1 HAl2; clear Def_Al.
exists (Upd Al a true).
unfold Assignment_of in |- *; split.
     (* variables assigned to true *)
intro i; replace (Of i (a :: l)) with (a = i \/ In i l); trivial with v62.
simple induction 1.
(* PB Changein Intros i Hi; Change a=i \/ (In nat i l) in Hi.
Elim Hi; Clear Hi.*)
simple induction 1; exact (L_Assign2 Al a true).
intro H_i_in_l.
elim (eq_nat_dec a i);
 [ simple induction 1; exact (L_Assign2 Al a true)
 | intro adifi; rewrite <- (HAl1 i H_i_in_l);
     
    (* PB was Exact (L_Assign3 Al a i adifi true)].*)
    exact (L_Assign3 Al a i adifi (Al i)) ].
     (* variables assigned to false *)
intro i; replace (~ Of i (a :: l)) with (~ (a = i \/ In i l));
 trivial with v62; intro Hi.
elim (deMorgan_and_not (a = i) (In i l) Hi); intros Hi_1 Hi_2; clear Hi.
rewrite <- (HAl2 i Hi_2).
exact (L_Assign3 Al a i Hi_1 true).
Qed.

Lemma Div_div_ass_eq :
 forall p1 p2 : Path,
 Divides p1 p2 ->
 Divides p2 p1 ->
 forall A1 : Assign,
 Assignment_of p1 A1 ->
 forall A2 : Assign, Assignment_of p2 A2 -> Ass_eq A1 A2.
Proof.
intros p1 p2.
unfold Divides in |- *; intros H12 H21.
intros A1 Def_A1 A2 Def_A2.
unfold Assignment_of in Def_A1; elim Def_A1; intros HA1_in HA1_out;
 clear Def_A1.
unfold Assignment_of in Def_A2; elim Def_A2; intros HA2_in HA2_out;
 clear Def_A2.
unfold Ass_eq in |- *; intro i.
elim (Of_path_dec p1 i); intro H.
apply (trans_equal (A:=bool)) with true;
 [ auto with v62 | symmetry  in |- *; auto with v62 ].
apply (trans_equal (A:=bool)) with false;
 [ auto with v62 | symmetry  in |- * ].
apply HA2_out; apply Contra with (Of i p1); auto with v62.
Qed.

Lemma Assign_of_cons :
 forall (p : Path) (i : nat) (A : Assign),
 Assignment_of (Cons i p) A -> A i = true.
Proof.
intros p i A.
unfold Assignment_of in |- *.
simple induction 1; intros H1 H2; clear H.
apply H1; unfold Of, Cons in |- *; trivial with v62.
Qed.

Lemma Inv_Assignment_of_true :
 forall (p : Path) (A : Assign),
 Assignment_of p A -> forall i : nat, A i = true -> Of i p.
Proof.
intros p A.
unfold Assignment_of in |- *.
simple induction 1; intros H1 H2; clear H.
intros i Def_i.
elim (Of_path_dec p i);
 [ trivial with v62 | intro Habsurde; absurd (A i = false) ].
rewrite Def_i; exact diff_true_false.
auto with v62.
Qed.

Lemma Inv_Assignment_of_false :
 forall (p : Path) (A : Assign),
 Assignment_of p A -> forall i : nat, A i = false -> ~ Of i p.
Proof.
intros p A.
unfold Assignment_of in |- *.
simple induction 1; intros H1 H2; clear H.
intros i Def_i.
elim (Of_path_dec p i);
 [ intro Habsurde; absurd (A i = true) | trivial with v62 ].
apply Contra with (true = A i);
 [ auto with v62 | rewrite Def_i; exact diff_true_false ].
auto with v62.
Qed.

Lemma Assign_of_cons_eq :
 forall (p : Path) (A : Assign),
 Assignment_of p A ->
 forall (i : nat) (A' : Assign),
 Assignment_of (Cons i p) A' -> A' = Upd A i true.
Proof.
intros p A Def_A i A' Def_A'.
apply Extensionality_Assignments; unfold Ass_eq in |- *.
intro j.
unfold Assignment_of in Def_A'; elim Def_A'; intros HA'_in HA'_out.
(* PB Change (Assignment_of (Cons i p) A') in Def_A'. *)
generalize Def_A';
 change (Assignment_of (Cons i p) A' -> A' j = Upd A i true j) in |- *;
 clear Def_A'; intro Def_A'.
unfold Assignment_of in Def_A; elim Def_A; intros HA_in HA_out.
(* PB Change (Assignment_of p A) in Def_A. *)
generalize Def_A; change (Assignment_of p A -> A' j = Upd A i true j) in |- *;
 clear Def_A; intro Def_A.
elim (Of_path_dec p j); elim (eq_nat_dec i j); intros H1 H2.
(*-- (Of j p) /\ i=j --*)
apply (trans_equal (A:=bool)) with true;
 [ elim H1; apply (Assign_of_cons p); assumption
 | elim H1; symmetry  in |- *; exact (L_Assign2 A i true) ].
(*-- (Of j p) /\ ~ i=j --*)
apply (trans_equal (A:=bool)) with true;
 [ apply HA'_in; auto with v62
 | apply (trans_equal (A:=bool)) with (A j);
    [ symmetry  in |- *; apply HA_in; trivial with v62
    | symmetry  in |- *; exact (L_Assign3 A i j H1 true) ] ].
(*-- ~(Of j p) /\ i=j --*)
apply (trans_equal (A:=bool)) with true;
 [ elim H1; apply (Assign_of_cons p); assumption
 | elim H1; symmetry  in |- *; exact (L_Assign2 A i true) ].
(*-- ~(Of j p) /\ ~ i=j --*)
apply (trans_equal (A:=bool)) with false;
 [ apply HA'_out; auto with v62
 | apply (trans_equal (A:=bool)) with (A j);
    [ symmetry  in |- *; apply HA_out; trivial with v62
    | symmetry  in |- *; exact (L_Assign3 A i j H1 true) ] ].
Qed.

Lemma Cons_of_non_depvar :
 forall (p : Path) (A : Assign),
 Assignment_of p A ->
 forall (i : nat) (A' : Assign),
 Assignment_of (Cons i p) A' -> forall f : BF, ~ Dep_Var f i -> f A = f A'.
Proof.
intros p A Def_A i A' Def_A' f Hi.
rewrite (Assign_of_cons_eq p A Def_A i A' Def_A'). 
change (f A = Frestr f i true A) in |- *.
generalize A; change (BF_eq f (Frestr f i true)) in |- *.
apply L_Dep_Var1; trivial with v62.    
Qed.


(*----------     Subtraction of an element in a Path         --------------*)


Definition Sub (p : Path) (i : nat) : Path :=
  (fix F (l : list nat) : Path :=
     match l with
     | nil => Nil
     | n :: l0 =>
         match eq_nat_dec i n with
         | left _ => F l0
         | right _ => Cons n (F l0)
         end
     end) p.
(*     Nil     *) 
(* (Cons j tl) *) 

Lemma I_out_of_Sub_ip : forall (p : Path) (i : nat), ~ Of i (Sub p i).
Proof.
simple induction p.
simpl in |- *; unfold not in |- *; trivial with v62.
clear p; intros a p Hp i; simpl in |- *.
elim (eq_nat_dec i a); auto with v62.
Qed.
Hint Resolve I_out_of_Sub_ip.

Lemma jofp_jofsub_ip :
 forall (p : Path) (i j : nat), Of j p -> i <> j -> Of j (Sub p i).
Proof.
simple induction p.
simpl in |- *; contradiction.
clear p; intros a p Hp i j H1j H2j; simpl in |- *.
elim (eq_nat_dec i a); intro H.
apply Hp; try assumption.
apply Of_cons_ip_of_p with i; try assumption.
rewrite H; assumption.
simpl in |- *; simpl in H1j.
elim H1j; auto with v62.
Qed.
Hint Resolve jofp_jofsub_ip.

Lemma Of_sub_pi_of_p :
 forall (p : Path) (i j : nat), Of j (Sub p i) -> Of j p.
Proof.
simple induction p.
simpl in |- *; contradiction.
clear p; intros a p Hp i j; simpl in |- *.
elim (eq_nat_dec i a);
 [ intros; right; apply Hp with i; assumption
 | intro; simpl in |- *; simple induction 1;
    [ auto with v62 | intro; right; apply Hp with i; assumption ] ].
Qed.

Lemma Outof_p_outof_sub_ip :
 forall (p : Path) (i j : nat), ~ Of j p -> ~ Of j (Sub p i).
Proof.
intros.
apply Contra with (Of j p); [ exact (Of_sub_pi_of_p p i j) | assumption ].
Qed.
Hint Resolve Outof_p_outof_sub_ip.

Lemma Head_sub_ordered :
 forall p : Path, Ordered p -> forall i : nat, Head (Sub p i) <= Head p.
Proof.
simple induction 1;
 [ simpl in |- *; trivial with v62
 | clear H p; intros p H1p H2p i Hi j; simpl in |- * ].
elim (eq_nat_dec j i); intro Cas.
(* case i=j *)
apply le_trans with (Head p); auto with v62.
(* case i=/=j *)
auto with v62.
Qed.

Lemma Ordered_p_ordered_sub_pi :
 forall (i : nat) (p : Path), Ordered p -> Ordered (Sub p i).
Proof.
intro i; simple induction p;
 [ simpl in |- *; trivial with v62 | intros hp tlp Hrec Hp ].
simpl in |- *; elim (eq_nat_dec i hp); intro Cas.
apply Hrec; apply Ordered_cons_ordered_tail with hp; assumption.
apply Cons_ordered;
 [ apply Hrec; apply Ordered_cons_ordered_tail with hp; assumption
 | apply gt_le_trans with (Head tlp) ].
elim (p_inv_Ordered (Cons hp tlp) Hp); auto with v62.
apply Head_sub_ordered; apply Ordered_cons_ordered_tail with hp; assumption.
Qed.


(*------------    Assignments of subtracted paths      ---------------*)

Lemma Assign_of_sub :
 forall (p : Path) (i : nat) (A : Assign),
 Assignment_of (Sub p i) A -> A i = false.
Proof.
intros p i A.
unfold Assignment_of in |- *.
simple induction 1; intros H1 H2; clear H.
apply H2; auto with v62.
Qed.

Lemma Assign_of_sub_eq :
 forall (p : Path) (A : Assign),
 Assignment_of p A ->
 forall (i : nat) (A' : Assign),
 Assignment_of (Sub p i) A' -> A' = Upd A i false.
Proof.
intros p A Def_A i A' Def_A'.
apply Extensionality_Assignments; unfold Ass_eq in |- *.
intro j.
unfold Assignment_of in Def_A'; elim Def_A'; intros HA'_in HA'_out.
(* PB Change (Assignment_of (Sub p i) A') in Def_A'. *)
generalize Def_A';
 change (Assignment_of (Sub p i) A' -> A' j = Upd A i false j) in |- *;
 clear Def_A'; intro Def_A'.
unfold Assignment_of in Def_A; elim Def_A; intros HA_in HA_out.
(* PB Change (Assignment_of p A) in Def_A. *)
generalize Def_A;
 change (Assignment_of p A -> A' j = Upd A i false j) in |- *; 
 clear Def_A; intro Def_A.
elim (Of_path_dec p j); elim (eq_nat_dec i j); intros H1 H2.
(*-- (Of j p) /\ i=j --*)
apply (trans_equal (A:=bool)) with false;
 [ elim H1; apply (Assign_of_sub p); assumption
 | elim H1; symmetry  in |- *; exact (L_Assign2 A i false) ].
(*-- (Of j p) /\ ~ i=j --*)
apply (trans_equal (A:=bool)) with true;
 [ apply HA'_in; auto with v62
 | apply (trans_equal (A:=bool)) with (A j);
    [ symmetry  in |- *; apply HA_in; trivial with v62
    | symmetry  in |- *; exact (L_Assign3 A i j H1 false) ] ].
(*-- ~(Of j p) /\ i=j --*)
apply (trans_equal (A:=bool)) with false;
 [ elim H1; apply (Assign_of_sub p); assumption
 | elim H1; symmetry  in |- *; exact (L_Assign2 A i false) ].
(*-- ~(Of j p) /\ ~ i=j --*)
apply (trans_equal (A:=bool)) with false;
 [ apply HA'_out; auto with v62
 | apply (trans_equal (A:=bool)) with (A j);
    [ symmetry  in |- *; apply HA_out; trivial with v62
    | symmetry  in |- *; exact (L_Assign3 A i j H1 false) ] ].
Qed.

Lemma Sub_of_non_depvar :
 forall (p : Path) (A : Assign),
 Assignment_of p A ->
 forall (i : nat) (A' : Assign),
 Assignment_of (Sub p i) A' -> forall f : BF, ~ Dep_Var f i -> f A = f A'.
Proof.
intros p A Def_A i A' Def_A' f Hi.
rewrite (Assign_of_sub_eq p A Def_A i A' Def_A'). 
change (f A = Frestr f i false A) in |- *.
generalize A; change (BF_eq f (Frestr f i false)) in |- *.
apply L_Dep_Var1; trivial with v62.    
Qed.
