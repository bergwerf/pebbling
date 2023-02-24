(*
C2. Pebbling in Hypercubes - Part III
=====================================
*)

From graph_pebbling Require Import A_primitives B_pebbling C1_basic_bounds.
From graph_pebbling Require Import C2_hypercube_I C2_hypercube_II.

Section Hypercube_Graph.

Context `{R_dec : RelDecision bool bool R, R_irrefl : Irreflexive bool R}.

Variable n : nat.
Variable weight : vec nat n.
Notation vertex := (vec bool n).

Definition hypercube_edge (u v : vertex) (i : fin n) : Prop :=
  R (u !!! i) (v !!! i) ∧ ∀ j, j ≠ i -> u !!! j = v !!! j.

Definition hypercube_edge_weight (u v : vertex) : nat :=
  let result := vec_find (λ p, p.1 ≠ p.2) (vzip_with pair u v) in
  from_option (weight !!!.) 0 result.

Definition hypercube : graph := {|
  graph_vertex := vertex;
  graph_edge := λ u v, ∃ i, hypercube_edge u v i;
  graph_edge_weight := hypercube_edge_weight;
|}.

Global Instance basic_hypercube :
  Basic_Graph hypercube.
Proof.
esplit.
- typeclasses eauto.
- solve_decision.
- intros v [i H]; destruct H.
  apply R_irrefl in H; done.
Defined.

Global Instance pebb_hypercube :
  Premise (Forall (le 2) weight) -> Pebbling_Graph hypercube.
Proof.
intros H; apply @premise in H; split; cbn; intros u v [i []].
unfold hypercube_edge_weight; destruct (vec_find _ _) as [k|] eqn:E; cbn.
- eapply Forall_vlookup, Forall_impl; [|apply H]; lia.
- exfalso; eapply vec_find_complete; [|apply E]; cbn.
  rewrite vlookup_zip_with; cbn; apply irrefl_neq; done.
Qed.

End Hypercube_Graph.

Global Arguments hypercube _ _ _ : clear implicits.

Section Hypercube_Homomorphisms.

Context `{R_dec : RelDecision bool bool R, R_irrefl : Irreflexive bool R}.

Definition hom_hypercube_0 : V unit_graph -> vec bool 0 :=
  λ _, [#].

Definition hom_hypercube_S n : bool * vec bool n -> vec bool (S n) :=
  λ v, vcons v.1 v.2.

Global Instance hom_hypercube_0_surj :
  Surj (=) hom_hypercube_0.
Proof. intros v; inv_vec v; exists (); done. Qed.

Global Instance hom_hypercube_S_surj n :
  Surj (=) (hom_hypercube_S n).
Proof. intros v; inv_vec v; intros b v; exists (b, v); done. Qed.

Global Instance hom_hypercube_0_spec :
  Graph_Hom unit_graph (hypercube R 0 [#]) hom_hypercube_0.
Proof. done. Qed.

Global Instance hom_hypercube_S_spec n k ks :
  Graph_Hom
    (edge_graph R k ☐ hypercube R n ks)
    (hypercube R (S n) (vcons k ks))
    (hom_hypercube_S n).
Proof.
split; intros [i u] [j v]; intros H; cbn in H.
- destruct H as [[H ->]|[[i' [H1 H2]] <-]]; [exists 0%fin|exists (FS i')];
  unfold hom_hypercube_S; split; cbn; try done.
  + intros j'; inv_fin j'; done.
  + intros j'; inv_fin j'; cbn; [done|].
    intros; apply H2; intros ->; done.
- rewrite unfold_weight_product_graph.
  destruct H as [[H ->]|[[i' [H _]] <-]]; apply irrefl_neq in H.
  + dec (v = v); cbn; destruct (decide _); done.
  + dec (u = v); dec (i = i); cbn; unfold hypercube_edge_weight.
    destruct (decide _), (vec_find _ _); done.
Qed.

End Hypercube_Homomorphisms.

Section Undirected_Hypercube.

Variable n : nat.
Variable ks : vec nat n.
Hypothesis ks_ge2 : Forall (le 2) ks.
Hypothesis ks_ord : ordered (≤) ks.

Notation hypercube := (hypercube neq).

Theorem pebbling_the_hypercube l :
  pebbling_bound (hypercube n ks) (product ks) ∧
  pebbling_property (hypercube n ks) 2 (hd l ks) (2 * product ks).
Proof.
revert l ks_ge2 ks_ord; induction n as [|m];
inv_vec ks; [intros|clear ks; intros k ks; cbn; intros; clear l].
- split.
  + eapply @surj_hom_pebbling_bound.
    * apply hom_hypercube_0_spec.
    * apply hom_hypercube_0_surj.
    * apply pebbling_number_unit_graph.
  + eapply @surj_hom_pebbling_property.
    * apply hom_hypercube_0_spec.
    * apply hom_hypercube_0_surj.
    * apply pebbling_property_unit_graph.
- replace (_ + (_ + 0)) with (2 * k * product ks) by lia.
  inv ks_ge2; cbn in ks_ord; assert (Premise (Forall (le 2) ks)) by done.
  apply ordered_cons_inv_tl in ks_ord as H_ks.
  apply ordered_cons_inv_hd in ks_ord; [|typeclasses eauto].
  apply (IHm ks k) in H_ks as [IH1 IH2]; [|done]; split.
  + eapply @surj_hom_pebbling_bound.
    * apply hom_hypercube_S_spec.
    * apply hom_hypercube_S_surj.
    * apply pebbling_bound_path2_prod with (l:=hd k ks); done.
  + eapply @surj_hom_pebbling_property.
    * apply hom_hypercube_S_spec.
    * apply hom_hypercube_S_surj.
    * apply pebbling_property_path2_prod with (l:=hd k ks); done.
Qed.

Corollary pebbling_bound_hypercube :
  pebbling_bound (hypercube n ks) (product ks).
Proof.
apply pebbling_the_hypercube; done.
Qed.

End Undirected_Hypercube.

Section Directed_Hypercube.

Variable n : nat.
Variable ks : vec nat n.
Hypothesis ks_ge2 : Forall (le 2) ks.
Hypothesis ks_ord : ordered (≤) ks.

Notation hypercube := (hypercube Bool.lt).
Notation ones n := (vreplicate n true).
Notation P2 := (edge_graph _ _).

Theorem pebbling_the_directed_hypercube l :
  vertex_pebbling_bound (hypercube n ks) (product ks) (ones n) ∧
  vertex_pebbling_property (hypercube n ks) 2 (hd l ks)
    (2 * product ks) (ones n).
Proof.
revert l ks_ge2 ks_ord; induction n as [|m];
inv_vec ks; [intros|clear ks; intros k ks; cbn; intros; clear l].
- split.
  + eapply @surj_hom_pebbling_bound.
    * apply hom_hypercube_0_spec.
    * apply hom_hypercube_0_surj.
    * apply pebbling_number_unit_graph.
  + eapply @surj_hom_pebbling_property.
    * apply hom_hypercube_0_spec.
    * apply hom_hypercube_0_surj.
    * apply pebbling_property_unit_graph.
- replace (_ + (_ + 0)) with (2 * k * product ks) by lia.
  inv ks_ge2; cbn in ks_ord; assert (Premise (Forall (le 2) ks)) by done.
  assert (Pebbling_Graph (hypercube m ks)) by typeclasses eauto.
  replace (vcons true _) with (hom_hypercube_S _ (true, ones m)) by done.
  apply ordered_cons_inv_tl in ks_ord as H_ks.
  apply ordered_cons_inv_hd in ks_ord; [|typeclasses eauto].
  apply (IHm ks k) in H_ks as [IH1 IH2]; [|done]; split.
  + eapply (@surj_hom_vertex_pebbling_bound (P2 ☐ hypercube _ _)).
    * apply hom_hypercube_S_spec.
    * apply hom_hypercube_S_surj.
    * apply @vertex_pebbling_bound_arrow_prod with (l:=hd k ks); done.
  + eapply (@surj_hom_vertex_pebbling_property (P2 ☐ hypercube _ _)).
    * apply hom_hypercube_S_spec.
    * apply hom_hypercube_S_surj.
    * apply @vertex_pebbling_property_arrow_prod with (l:=hd k ks); done.
Qed.

Corollary vertex_pebbling_bound_directed_hypercube :
  vertex_pebbling_bound (hypercube n ks) (product ks) (ones n).
Proof.
apply pebbling_the_directed_hypercube; done.
Qed.

End Directed_Hypercube.
