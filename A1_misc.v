(*
A1. Miscellaneous Lemmas
========================
*)

From Coq Require Export ZifyNat FunctionalExtensionality.
From stdpp Require Export base relations functions finite.
From stdpp Require Export fin vector list list_numbers numbers.

Open Scope nat_scope.

Ltac inv H := inversion H; subst; clear H.
Ltac dec E := let H := fresh "H" in destruct (decide E) as [H|H]; simplify_eq.
Ltac inst H x := let Hx := fresh "H" in assert (Hx:=H x); cbn in Hx; revert Hx.
Ltac clia := cbn; repeat intro; cbn; lia.

Ltac simpl_lookup H1 H2 := repeat (rewrite ?H1; try (rewrite H2; [|try done])).
Ltac simpl_alter := simpl_lookup fn_lookup_alter fn_lookup_alter_ne.
Ltac simpl_insert := simpl_lookup fn_lookup_insert fn_lookup_insert_ne.

Ltac simpl_elem_of :=
  repeat match goal with
  | H : _ ∈ [] |- _ =>
    apply elem_of_nil in H; done
  | H : ?x ∈ ?y :: ?l |- _ =>
    apply elem_of_cons in H as [<-|H]
  | H : ?x ∈ ?l1 ++ ?l2 |- _ =>
    apply elem_of_app in H as [H|H]
  end.

(* Any predicate promoted to a class. *)
Class Premise (P : Prop) : Prop :=
  premise : P.

(* A binary function f that is left-distributive over g. *)
Class LeftDistr {A B} (R : relation A) (f : B -> A -> A) (g : A -> A -> A) :=
  left_distr b a1 a2 : R (f b (g a1 a2)) (g (f b a1) (f b a2)).

(* A binary function f that is right-distributive over g. *)
Class RightDistr {A B} (R : relation A) (f : A -> B -> A) (g : A -> A -> A) :=
  right_distr a1 a2 b : R (f (g a1 a2) b) (g (f a1 b) (f a2 b)).

(* A property that is left-dominant under a binary function. *)
Class LeftDominant {A} (P : A -> Prop) (f : A -> A -> A) :=
  left_dominant a b : P a -> P (f a b).

(* A unary and binary function that are left-commutative on a subset. *)
Class CondLeftComm {A}
  (R : relation A) (P : A -> Prop) (f : A -> A) (g : A -> A -> A) :=
  cond_left_comm a b : P a -> R (g (f a) b) (f (g a b)).

Global Instance left_dominant_True {A} (f : A -> A -> A) :
  LeftDominant (λ _, True) f.
Proof. done. Qed.

(* The minimum value in some ordering R for which P holds. *)
Record minimal {A} (R : relation A) (P : A -> Prop) (a : A) : Prop := {
  minimal_valid : P a;
  minimal_least : ∀ b, P b -> R a b;
}.

Lemma contrapositive `{Decision Q} P : (¬ Q -> ¬ P) -> P -> Q.
Proof. intros H1 H2; dec Q; [done|exfalso]; apply H1; done. Qed.

Definition neq {A} : A -> A -> Prop := λ a a', a ≠ a'.

Global Arguments neq _ _ /.

Global Instance neq_irrefl {A} :
  Irreflexive (@neq A).
Proof. intros a; unfold complement; done. Qed.

Global Instance neq_dec `{EqDecision A} :
  RelDecision (@neq A).
Proof. solve_decision. Qed.

Global Instance :
  RelDecision Bool.lt.
Proof. intros [] []; cbn; solve_decision. Qed.

Global Instance :
  Irreflexive Bool.lt.
Proof. intros []; unfold complement; done. Qed.

Lemma irrefl_neq `{irrefl : Irreflexive A R} a b : R a b -> a ≠ b.
Proof. repeat intro; subst; eapply irrefl; done. Qed.

(* A generic step relations. *)
Class Step (X : Type) := step : X -> X -> Prop.

Notation "x --> y" := (step x y).
Notation "x '-->*' y" := (rtc step x y) (at level 70).

Lemma unwrap_rtc `{refl : Reflexive A R, trans : Transitive A R} a b :
  rtc R a b -> R a b.
Proof. apply rtc_ind_r_weak; firstorder. Qed.

(* Swap the elements in a product. *)
Definition swap {A B} (p : A * B) := (p.2, p.1).
Global Arguments swap _ _ _ /.

Global Instance inj_swap {A B} : Inj eq eq (@swap A B).
Proof. intros [] []; cbn; congruence. Qed.

Section Function_Composition.

Lemma compose_def {A B C} (f : A -> B) (g : B -> C) a :
  (g ∘ f) a = g (f a).
Proof. done. Qed.

Lemma assoc_compose {A B C D} (f : A -> B) (g : B -> C) (h : C -> D) :
  h ∘ (g ∘ f) = h ∘ g ∘ f.
Proof. extensionality a; done. Qed.

Lemma left_id_compose {A B} (f : A -> B) :
  id ∘ f = f.
Proof. extensionality a; done. Qed.

Lemma right_id_compose {A B} (f : A -> B) :
  f ∘ id = f.
Proof. extensionality a; done. Qed.

End Function_Composition.

Section Function_Inversion.

Definition invertible {A B} (f : A -> B) :=
  ∃ inv : B -> A, inv ∘ f = id ∧ f ∘ inv = id.

Lemma invertible_id {A} : invertible (@id A).
Proof. exists id; split; extensionality a; done. Qed.

Lemma invertible_inj {A B} (f : A -> B) :
  invertible f -> Inj (=) (=) f.
Proof.
intros (inv & H_inv & _) a a' H1.
assert (H2 : (inv ∘ f) a = (inv ∘ f) a') by (cbn; congruence).
rewrite H_inv in H2; done.
Qed.

End Function_Inversion.

Section Finite_Types.

Lemma length_fin_enum n : length (fin_enum n) = n.
Proof. induction n; cbn; [done|]. rewrite fmap_length, IHn; done. Qed.

Global Instance inj_vcons_tl {A} n (a : A) : Inj (=) (=) (@vcons _ a n).
Proof. intros u v; apply vcons_inj_2. Qed.

Lemma not_forall_exists `{fin : Finite A, P_dec : ∀ a : A, Decision (P a)} :
  (¬ ∀ a, P a) -> ∃ a, ¬ P a.
Proof.
intros; destruct (decide (∃ a, ¬ P a)) as [?|Hex]; [done|exfalso].
apply H; intros; dec (P a); [done|exfalso].
apply Hex; exists a; done.
Qed.

End Finite_Types.
