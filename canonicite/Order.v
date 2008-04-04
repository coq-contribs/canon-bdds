(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*       Ordered sets                                                       *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                  Order.v                                 *)
(****************************************************************************)

Section VR.

Variable V : Set.          (* The Universe of discourse *)
Variable R : V -> V -> Prop.   (* Given with order relation R *)
Variable V_eq : V -> V -> Prop. (* and equality V_eq *)

Definition reflexivity := forall x : V, R x x.
Definition anti_symetry := forall x y : V, R x y -> R y x -> V_eq x y.
Definition transitivity := forall x y z : V, R x y -> R y z -> R x z.

Definition order := reflexivity /\ anti_symetry /\ transitivity.

Definition totality := forall x y : V, R x y \/ R y x.
Definition total_order := order /\ totality.

End VR.
