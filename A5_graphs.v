(*
A5. Graphs and Graph Products
=============================
*)

From graph_pebbling Require Import A1_misc.

Record graph := {
  graph_vertex : Type;
  graph_edge : relation graph_vertex;
  graph_edge_weight : graph_vertex -> graph_vertex -> nat;
}.

Notation V G := (graph_vertex G).
Notation E G := (graph_edge G).
Notation weight G := (graph_edge_weight G).

Class Basic_Graph (G : graph) := {
  graph_vertex_dec :> EqDecision (V G);
  graph_vertex_fin :> @Finite (V G) graph_vertex_dec;
  graph_edge_dec :> RelDecision (E G);
  graph_edge_irrefl :> Irreflexive (E G);
}.

Class Graph_Hom {G H} (h : V G -> V H) : Prop := {
  graph_hom_edge : ∀ u v, E G u v -> E H (h u) (h v);
  graph_hom_weight : ∀ u v, E G u v -> weight H (h u) (h v) = weight G u v;
}.

Global Hint Mode Basic_Graph ! : typeclass_instances.

Global Arguments Graph_Hom _ _ _ : clear implicits.
Notation Graph_Aut G := (Graph_Hom G G).

Section Basic_Graphs.

Definition unit_graph := {|
  graph_vertex := unit;
  graph_edge := λ _ _, False;
  graph_edge_weight := λ _ _, 0;
|}.

Global Instance basic_unit_graph :
  Basic_Graph unit_graph.
Proof.
esplit.
- typeclasses eauto.
- solve_decision.
- firstorder. 
Defined.

Variable n k : nat.

Definition complete_graph : graph := {|
  graph_vertex := fin n;
  graph_edge := λ u v, u ≠ v;
  graph_edge_weight := λ _ _, k;
|}.

Global Instance basic_complete_graph :
  Basic_Graph complete_graph.
Proof.
esplit.
- typeclasses eauto.
- solve_decision.
- firstorder. 
Defined.

End Basic_Graphs.

Section Cartesian_Product.

Context `{graph_G : Basic_Graph G}.
Context `{graph_H : Basic_Graph H}.

Definition product_graph : graph := {|
  graph_vertex := V G * V H;
  graph_edge := λ u v,
    (E G u.1 v.1 ∧ u.2 = v.2) ∨
    (E H u.2 v.2 ∧ u.1 = v.1);
  graph_edge_weight := λ u v,
    if (decide (u.2 = v.2)) then weight G u.1 v.1 else
    if (decide (u.1 = v.1)) then weight H u.2 v.2 else 0;
|}.

Global Instance basic_product_graph :
  Basic_Graph product_graph.
Proof.
esplit.
- typeclasses eauto.
- solve_decision.
- intros [u v] [[Hu _]|[Hv _]]; cbn in *;
  [apply graph_G in Hu|apply graph_H in Hv]; done.
Defined.

Lemma unfold_weight_product_graph i j u v :
  weight product_graph (i, u) (j, v) =
    if (decide (u = v)) then weight G i j else
    if (decide (i = j)) then weight H u v else 0.
Proof. done. Qed.

End Cartesian_Product.

Notation "G ☐ H" := (@product_graph G _ H _) (at level 50).
