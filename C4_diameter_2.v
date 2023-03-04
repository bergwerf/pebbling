(*
C4. Pebbling in graphs with diameter 2
======================================
*)

From graph_pebbling Require Import A_primitives B_pebbling.

Section Diameter_2.

Context `{graph_G : Basic_Graph G, pebb_G : Pebbling_Graph G}.

Notation V := (V G).
Notation E := (E G).

Hypothesis diam2 : ∀ u v, u = v ∨ E u v ∨ ∃ w, E u w ∧ E w v.
Hypothesis weight2 : ∀ u v, weight G u v = 2.

Ltac pebble_step s t := eapply rtc_l;
  [eapply one_pebble_step with (u:=s)(v:=t);
  cbn; rewrite ?weight2; [done|try (lia || simpl_alter; clia)|done]|].

Lemma diam2_solve_4 c v t :
  c v ≥ 4 -> solvable G t 1 c.
Proof.
intros; dec (v = t); [|dec (E v t)].
- eexists; split; [done|lia].
- eexists; split. pebble_step v t; done. simpl_alter; lia.
- destruct (diam2 v t) as [|[|(w & Hu & Hv)]]; [done|done|].
  apply irrefl_neq in Hu as ?, Hv as ?; eexists; split.
  pebble_step v w; pebble_step v w; pebble_step w t; done.
  simpl_alter; lia.
Qed.

Notation vs := (enum V).

Theorem pebbling_diameter_2 :
  pebbling_bound G (card V + 1).
Proof.
intros t c H; unfold card in H.
(* Partition the vertices into three sets. *)
pose (vs0 := filter (λ v, c v = 0) vs);
pose (vs1 := filter (λ v, c v = 1) vs);
pose (xs := filter (λ v, 2 ≤ c v) vs);
assert (vs ≡ₚ vs0 ++ vs1 ++ xs). { unfold vs0, vs1, xs; etrans.
  eapply filter_app_Permutation. apply Permutation_app_head; etrans.
  apply filter_app_Permutation with (P:=λ v, c v = 1). apply Permutation_app;
  erewrite list_filter_filter, list_filter_iff; [done|clia|done|clia]. }
(* Determine c t = 0. *)
(* Determine NoDup xs and Forall (eq 0) xs. *)
(* Determine ys with Forall2 (λ x y, E x y ∧ E y t) xs ys. *)
(* Determine NoDup ys and length vs0 ≥ length xs + 1. *)
(* Determine v with c v ≥ 3 and xs ≡ₚ v :: xs'. *)
(* Determine zs with Forall2 (λ x z, E x z ∧ E z v) xs' zs. *)
(* Determine length vs0 ≥ 2 * length xs. *)
(* Determine w with c w ≥ 4. *)
Admitted.

End Diameter_2.
