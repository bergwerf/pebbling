(*
A2. Lifting Binary Operators
============================
*)

From graph_pebbling Require Import A1_misc.

(* Lift a binary operator to functions. *)
Definition lift2 {A B C D} (op : B -> C -> D) (f : A -> B) (g : A -> C) a :=
  op (f a) (g a).

(* Lift a binary relation to functions. *)
Definition liftR {A B C} (R : B -> C -> Prop) (f : A -> B) (g : A -> C) :=
  ∀ a, lift2 R f g a.

Global Arguments lift2 {_ _ _ _} _ _ _ _ /.

Section Equivalence.

Global Instance refl_liftR `{refl : Reflexive B R} {A} :
  Reflexive (@liftR A B B R).
Proof. firstorder. Qed.

Global Instance sym_liftR `{sym : Symmetric B R} {A} :
  Symmetric (@liftR A B B R).
Proof. firstorder. Qed.

Global Instance trans_liftR `{trans : Transitive B R} {A} :
  Transitive (@liftR A B B R).
Proof. intros x y z H1 H2 a; cbn; etrans; [apply H1|apply H2]. Qed.

End Equivalence.

Section Algebraic.

Ltac lift_proof H := repeat intro; extensionality a; apply H.

Global Instance assoc_lift2 `{assoc : Assoc B (=) f} {A} :
  Assoc (=) (@lift2 A B B B f).
Proof. lift_proof assoc. Qed.

Global Instance comm_lift2 `{comm : Comm C B (=) f} {A} :
  Comm (=) (@lift2 A B B C f).
Proof. lift_proof comm. Qed.

Global Instance left_distr_lift2 `{distr : LeftDistr B B (=) f1 f2} {A} :
  LeftDistr (=) (@lift2 A B B B f1) (lift2 f2).
Proof. lift_proof distr. Qed.

Global Instance right_distr_lift2 `{distr : RightDistr B B (=) f1 f2} {A} :
  RightDistr (=) (@lift2 A B B B f1) (lift2 f2).
Proof. lift_proof distr. Qed.

Global Instance left_id_lift2 `{left_id : LeftId B (=) b f} {A} :
  LeftId (=) (const b) (@lift2 A B B B f).
Proof. lift_proof left_id. Qed.

Global Instance right_id_lift2 `{right_id : RightId B (=) b f} {A} :
  RightId (=) (const b) (@lift2 A B B B f).
Proof. lift_proof right_id. Qed.

Global Instance left_absorb_lift2 `{left_absorb : LeftAbsorb B (=) b f} {A} :
  LeftAbsorb (=) (const b) (@lift2 A B B B f).
Proof. lift_proof left_absorb. Qed.

Global Instance right_absorb_lift2 `{right_absorb : RightAbsorb B (=) b f} {A} :
  RightAbsorb (=) (const b) (@lift2 A B B B f).
Proof. lift_proof right_absorb. Qed.

End Algebraic.

Section Special.

Lemma left_distr_compose_lift2 `{distr : LeftDistr B B (=) f h} {A} g1 g2 b :
  f b ∘ lift2 h g1 g2 = @lift2 A B B B h (f b ∘ g1) (f b ∘ g2).
Proof. extensionality a; cbn; done. Qed.

Lemma right_distr_compose_lift2 {A B C D}
  (f : A -> B) (g1 g2 : B -> C) (h : C -> C -> D) :
  lift2 h g1 g2 ∘ f = lift2 h (g1 ∘ f) (g2 ∘ f).
Proof. done. Qed.

Global Instance left_comm_alter_lift2
  `{EqDecision A, l_comm : CondLeftComm B (=) P f h} (a : A) :
  CondLeftComm (=) (λ g, P (g a)) (alter f a) (lift2 h).
Proof.
intros g1 g2 HP; extensionality a'.
dec (a' = a); simpl_alter; cbn; simpl_alter.
apply l_comm; done. done.
Qed.

End Special.
