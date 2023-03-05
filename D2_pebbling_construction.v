(*
D2. The Pebbling Construction Principle
=======================================
*)

From graph_pebbling Require Import A_primitives B1_graph_pebbling.

Section Pebbling_Construction.

Context `{graph_G : Basic_Graph G}.
Notation V := (V G).

Variable A : Type.
Variable pebbles : list A.
Variable well_placed : V -> list A -> Prop.

Hypothesis initialize : ∀ a,
  a ∈ pebbles -> ∃ v, well_placed v [a].

Hypothesis step : ∀ u v ls,
  E G u v -> Forall (well_placed u) ls ->
  length ls = weight G u v ->
  ∃ l, l ⊆+ concat ls ∧ well_placed v l.

Record pc_conf l c (f : V -> list (list A)) : Prop := {
  pc_sound : ∀ v, Forall (well_placed v) (f v);
  pc_size : ∀ v, length (f v) = c v;
  pc_part : concat (concat (f <$> enum V)) ⊆+ l;
}.

Definition pc_realizable c := ∃ f, pc_conf pebbles c f.

Lemma pc_start :
  ∃ c, size c = length pebbles ∧ pc_realizable c.
Proof.
clear step; unfold pc_realizable.
induction pebbles as [|a l]; cbn.
- exists (const 0); split; [rewrite size_const; done|].
  exists (const []); split; cbn; [done|done|].
  rewrite fmap_const, concat_repeat_nil; done.
- destruct IHl as (c & <- & f & Hf); [set_solver|].
  destruct Hf as [H1 H2 H3]; assert (Ha : a ∈ a :: l) by set_solver.
  apply initialize in Ha as (v & Hl).
  exists (alter S v c); split; [rewrite size_alter; done|].
  exists (alter (cons [a]) v f); split.
  + intros w; dec (v = w); simpl_alter; [constructor|]; done.
  + intros w; dec (v = w); simpl_alter; cbn; rewrite H2; done.
  + rewrite foldr_alter; [cbn|done|apply elem_of_enum|apply NoDup_enum].
    constructor; done.
Qed.

Lemma pc_step c c' :
  c --> c' -> pc_realizable c -> pc_realizable c'.
Proof.
clear initialize; inversion_clear 1; intros [f [H1 H2 H3]].
remember (weight G u v) as k eqn:Hk; cbn in Hk.
edestruct step with (ls:=take k (f u)) as (l & H4 & H5);
[done|apply Forall_take; done|rewrite take_length, H2, <-Hk; lia|].
exists (alter (cons l) v (alter (drop k) u f)); split.
- intros w; dec (w = v); [dec (u = v)|dec (w = u)]; simpl_alter;
  try constructor; try apply Forall_drop; done.
- intros w; dec (w = v); [dec (u = v)|dec (w = u)]; simpl_alter;
  cbn; rewrite ?drop_length, ?H2; done.
- etrans; [|done]; apply irrefl_ne in H_edge.
  revert H_edge H4; clear; intros H1 H2.
  assert (∃ vs, enum V ≡ₚ u :: v :: vs ∧ u ∉ vs ∧ v ∉ vs).
  + (* Move u and v to the front. *)
    cut (v ∈ enum V); [|apply elem_of_enum].
    assert (Hu : u ∈ enum V) by apply elem_of_enum.
    apply elem_of_Permutation in Hu as [us H_us]; intros.
    assert (Hv : v ∈ us) by (rewrite H_us in H; set_solver).
    apply elem_of_Permutation in Hv as [vs H_vs].
    assert (NoDup (u :: v :: vs)).
    * rewrite <-H_vs, <-H_us; apply NoDup_enum.
    * inv H0; inv H6; exists vs; rewrite H_us, H_vs; set_solver.
  + (* Simplify concatenation. *)
    destruct H as (vs & -> & Hu & Hv); cbn; simpl_alter.
    rewrite ?fmap_no_alter; [|done|done].
    rewrite ?foldr_comm; cbn; rewrite ?(assoc (++)).
    repeat (apply submseteq_app; [|done]).
    erewrite <-(take_drop _ (f u)) at 2.
    rewrite foldr_comm, (comm (++)).
    apply submseteq_app; done.
Qed.

Lemma pebbling_construction t :
  vertex_pebbling_bound G (length pebbles) t ->
  ∃ l, l ⊆+ pebbles ∧ well_placed t l.
Proof.
destruct pc_start as (c & H1 & H2).
intros (c' & H3 & H4); [rewrite H1; red; done|].
assert (H5 : pc_realizable c').
- revert H3; apply rtc_ind_r; [done|].
  intros ? ? _; apply pc_step.
- destruct H5 as [f [H5 H6 H7]].
  assert (H8 : length (f t) ≠ 0) by (rewrite H6; lia).
  apply non_empty_length, non_empty_inv in H8 as [l H8].
  exists l; split; [|eapply list.Forall_forall; done].
  etrans; [|done]; apply sublist_submseteq.
  eapply sublist_concat_r, elem_of_concat; [apply H8|].
  apply elem_of_list_fmap_1, elem_of_enum.
Qed.

End Pebbling_Construction.
