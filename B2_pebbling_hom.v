(*
B2. Pebbling Homomorphisms
==========================
*)

From graph_pebbling Require Import A_primitives B1_graph_pebbling.

Section Pebbling_Embedding.

Context `{graph_G : Basic_Graph G}.
Context `{graph_H : Basic_Graph H}.
Context `{hom : Graph_Hom G H h}.

(*
Injective Embedding
-------------------
*)
Section Injective.

Context {inj : Inj (=) (=) h}.

Theorem inj_hom_solvable_le t n (c_g : conf G) (c_h : conf H) :
  (∀ v, c_g v ≤ c_h (h v)) -> solvable G t n c_g -> solvable H (h t) n c_h.
Proof.
intros H_le (c' & Hc & Ht); revert c_h H_le.
induction Hc as [c_g|c1_g c2_g c'_g H1]; intros.
- eexists; split; [reflexivity|].
  etrans; [apply Ht|apply H_le].
- inversion_clear H1; cbn in H_conf.
  pose (w_uv := weight H (h u) (h v));
  pose (c2_h := alter add1 (h v) (alter (subtract w_uv) (h u) c_h)).
  apply IHHc with (c_h:=c2_h) in Ht as (c'_h & H2 & H3).
  + exists c'_h; split; [|done]. eapply rtc_l; [|done].
    eapply one_pebble_step; [apply graph_hom_edge; done|cbn|done].
    etrans; [|apply H_le]; etrans; [|apply H_conf].
    rewrite graph_hom_weight; done.
  + intros w; unfold c2_h, w_uv; rewrite R_conf.
    assert (H2 := graph_hom_weight u v); assert (H3 := H_le w).
    dec (w = u); [dec (v = u)|dec (w = v)]; simpl_alter;
    cbn; try apply not_inj; try done; lia.
Qed.

Corollary inj_hom_solvable t n (c : conf H) :
  solvable G t n (c ∘ h) -> solvable H (h t) n c.
Proof. apply inj_hom_solvable_le; done. Qed.

End Injective.

(*
Surjective Embedding
-------------------
*)
Section Surjective.

Context {surj : Surj (=) h}.

Lemma pebble_step_map_conf c c' :
  c --> c' -> dmap h c --> dmap h c'.
Proof.
inversion_clear 1; subst.
assert (Hh_edge : E H (h u) (h v)) by (apply graph_hom_edge; done).
eapply one_pebble_step; [done|cbn|].
- rewrite graph_hom_weight; [|done]; etrans; [apply H_conf|].
  apply elem_of_summation, elem_of_list_fmap_1, elem_of_inv.
- apply irrefl_neq in H_edge as ?, Hh_edge.
  extensionality w; unfold dmap.
  assert (Hw := NoDup_inv h w).
  (* Simplify left side. *)
  destruct (decide (u ∈ inv h w)) as [Hu|Hu], (decide (v ∈ inv h w)) as [Hv|Hv];
  repeat (rewrite foldr_alter; [|done|done|done])
    || (rewrite fmap_no_alter; [|done]).
  (* Simplify right side. *)
  all: try apply elem_of_inv_spec in Hu; subst.
  all: try apply elem_of_inv_spec in Hv; subst. 1: done.
  all: try apply not_elem_of_inv_spec in Hu as H1.
  all: try apply not_elem_of_inv_spec in Hv as H2.
  all: simpl_alter; cbn; try done.
  rewrite graph_hom_weight; done.
Qed.

Theorem surj_hom_solvable t n (c : conf G) :
  solvable G t n c -> solvable H (h t) n (dmap h c).
Proof.
intros (c' & H1 & H2); exists (dmap h c'); split.
- revert H1; apply rtc_congruence, pebble_step_map_conf.
- etrans; [apply H2|apply elem_of_summation, elem_of_list_fmap_1, elem_of_inv].
Qed.

Lemma surj_hom_vertex_pebbling_bound n t :
  vertex_pebbling_bound G n t -> vertex_pebbling_bound H n (h t).
Proof.
intros Hn c Hc; rewrite <-inv_dmap_spec; apply surj_hom_solvable, Hn.
rewrite size_inv_dmap; done.
Qed.

Corollary surj_hom_pebbling_bound n :
  pebbling_bound G n -> pebbling_bound H n.
Proof.
intros Hn t; destruct (surj t) as [t' <-].
apply surj_hom_vertex_pebbling_bound; done.
Qed.

End Surjective.

End Pebbling_Embedding.
