(*
B1. Graph Pebbling
==================
*)

From graph_pebbling Require Import A_primitives.

Notation conf G := (valuation (V G)).

Class Pebbling_Graph (G : graph) : Prop := {
  pebbling_weight_gt1 : ∀ u v, E G u v -> weight G u v > 1;
}.

Global Hint Mode Pebbling_Graph ! : typeclass_instances.

Global Instance pebb_unit_graph :
  Pebbling_Graph unit_graph.
Proof. done. Qed.

Global Instance pebb_complete_graph n k :
  Premise (k ≥ 2) -> Pebbling_Graph (complete_graph n k).
Proof. intros H; apply @premise in H; split; clia. Qed.

Global Instance product_graph_pebb
  `{graph_G : Basic_Graph G, pebb_G : Pebbling_Graph G}
  `{graph_H : Basic_Graph H, pebb_H : Pebbling_Graph H}
  : Pebbling_Graph (G ☐ H).
Proof.
split; cbn; intros [u1 u2] [v1 v2]; cbn; intros [[]|[]]; subst.
- dec (v2 = v2); apply pebbling_weight_gt1; done.
- dec (u2 = v2); [firstorder|]; dec (v1 = v1); apply pebbling_weight_gt1; done.
Qed.

Section Graph_Pebbling.

Context `{graph_G : Basic_Graph G}.

Notation V := (V G).
Notation E := (E G).
Notation weight := (weight G).
Notation conf := (conf G).

Inductive pebble_step : conf -> conf -> Prop :=
  one_pebble_step (c c' : conf) (u v : V)
  (H_edge : E u v)
  (H_conf : weight u v ≤ c u)
  (R_conf : c' = alter S v (alter (subtract (weight u v)) u c)) :
  pebble_step c c'.

Global Instance : Step conf := pebble_step.

Definition solvable (t : V) (n : nat) (c : conf) :=
  ∃ c', c -->* c' ∧ n ≤ c' t.

Definition vertex_pebbling_bound p t :=
  ∀ c, size c ≥ p -> solvable t 1 c.

Definition pebbling_bound p :=
  ∀ t, vertex_pebbling_bound p t.

Definition pebbling_number :=
  minimal (≤) pebbling_bound.

Section Lemmas.

Context `{pebb_G : Pebbling_Graph G}.

Lemma pebble_step_size c c' :
  c --> c' -> size c' < size c.
Proof.
inversion_clear 1; apply pebbling_weight_gt1 in H_edge.
assert (c u ≤ size c) by apply size_lwb.
subst; rewrite ?size_alter; cbn in *; lia.
Qed.

Lemma pebbling_add_r c c1 c2 :
  c1 -->* c2 -> (c .+ c1) -->* (c .+ c2).
Proof.
apply rtc_congruence; clear; intros c1 c2; inversion_clear 1.
eapply one_pebble_step; cbn in *; [done|lia|extensionality w].
dec (w = u); [dec (v = u)|dec (w = v)]; cbn; simpl_alter; clia.
Qed.

Lemma pebbling_add c1 c1' c2 c2' :
  c1 -->* c1' -> c2 -->* c2' -> (c1 .+ c2) -->* (c1' .+ c2').
Proof.
intros; etrans; [apply pebbling_add_r; done|].
rewrite (comm (.+) c1 c2'), (comm (.+) c1' c2').
apply pebbling_add_r; done.
Qed.

Lemma pebbling_minor c c' d :
  c -->* c' -> c .≤ d -> d -->* ((d .- c) .+ c').
Proof.
intros; replace d with ((d .- c) .+ c) at 1 by ext_lia.
eapply rtc_congruence; [|done]; generalize (d .- c); clear; intros x c c' H.
inv H; apply one_pebble_step with (u:=u)(v:=v); [done|cbn in *; lia|].
rewrite (comm (.+)), ?left_comm_alter_lift2, (comm (.+)); [done|done|].
dec (u = v); simpl_alter; cbn in *; lia.
Qed.

Lemma vertex_pebbling_repeat p t n c :
  vertex_pebbling_bound p t -> size c ≥ n*p -> solvable t n c.
Proof.
intros Hp; revert c; induction n; cbn; intros.
- exists c; split; [done|lia].
- destruct (fn_minor c p) as (c1 & H1 & H2); [lia|].
  destruct (Hp c1) as (c2 & H3 & H4); [lia|].
  destruct (IHn (c .- c1)) as (c3 & H5 & H6); [rewrite size_sub; [lia|done]|].
  exists (c2 .+ c3); cbn; split; [|lia].
  replace c with (c1 .+ (c .- c1)) by (extensionality v; inst H1 v; clia).
  apply pebbling_add; done.
Qed.

End Lemmas.

End Graph_Pebbling.

Global Arguments solvable _ {_}.
Global Arguments vertex_pebbling_bound _ {_}.
Global Arguments pebbling_bound _ {_}.
Global Arguments pebbling_number _ {_}.
