(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                  Complements de Prelude  Logiques                        *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                Prelude0.v                                *)
(****************************************************************************)

(* ought to be integrated in SYSTEM libraries *)

Lemma Contra : forall P Q : Prop, (P -> Q) -> ~ Q -> ~ P.
unfold not in |- *; auto.
Qed.

Lemma Morgan_or : forall P Q : Prop, ~ P -> ~ Q -> ~ (P \/ Q).
unfold not in |- *.
intros P Q notP notQ Dis.
elim Dis; auto.
Qed.

Lemma Morgan_and_not : forall P Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q.
unfold not in |- *.
intros.
split; auto.
Qed.
