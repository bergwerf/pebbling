(*
C1. Basic Pebbling Bounds
=========================
*)

From graph_pebbling Require Import A_primitives B_pebbling.

Section Pebbling_Lower_Bound.

Context `{graph_G : Basic_Graph G, pebb_G : Pebbling_Graph G}.

Lemma vertex_pebbling_lower_bound p t :
  vertex_pebbling_bound G p t -> p ≥ card (V G).
Proof.
intros Ht; dec (p < card (V G)); [exfalso|lia].
destruct (Ht (alter (subtract 1) t (const 1))) as (c' & H1 & H2).
- rewrite size_alter; [|clia]; rewrite size_const; clia.
- apply rtc_inv in H1 as [<-|(c1 & H3 & H4)].
  + revert H2; simpl_alter; clia.
  + inv H3; apply pebbling_weight_gt1 in H_edge.
    revert H_conf; dec (u = t); simpl_alter; clia.
Qed.

Corollary vertex_pebbling_bound_ge1 p t :
  vertex_pebbling_bound G p t -> p ≥ 1.
Proof.
intros H; apply vertex_pebbling_lower_bound in H.
destruct (card (V G)) eqn:E; [|lia].
eapply card_0_inv; [apply E|apply t].
Qed.

Corollary supp_le_vertex_pebbling_bound t p (c : conf G) :
  vertex_pebbling_bound G p t -> supp c ≤ p.
Proof.
intros Hp; etrans; [apply supp_le_card|].
eapply vertex_pebbling_lower_bound, Hp.
Qed.

Corollary no_pebbling_bound_lt_card p :
  p < card (V G) -> ¬ pebbling_bound G p.
Proof.
intros; destruct (finite_inhabited (V G)) as [t]; [lia|]; intros Hp.
assert (Ht := Hp t); apply vertex_pebbling_lower_bound in Ht; lia.
Qed.

End Pebbling_Lower_Bound.

Section Basic_Pebbling_Bounds.

Theorem pebbling_number_unit_graph :
  pebbling_number unit_graph 1.
Proof.
split.
- intros [] c Hc; cbn in *; exists c; split; [done|lia].
- intro; apply contrapositive; intros; apply no_pebbling_bound_lt_card; clia.
Qed.

Theorem pebbling_number_complete_graph n k :
  pebbling_number (complete_graph (S n) (S k)) (n * k + 1).
Proof.
split; [intros t c Hc|intros q; apply contrapositive; intros Hq H].
- (* Solution strategy *)
  dec (1 ≤ c t); [exists c; done|]; assert (supp c ≤ n).
  + etrans. apply supp_lt_card with (z:=[t]). apply NoDup_singleton.
    decompose_Forall; lia. cbn; rewrite fmap_length, length_fin_enum; lia.
  + assert (Hk : @size _ _ graph_vertex_fin c > k * supp c) by nia.
    apply supp_pigeon_hole in Hk as (s & Hs).
    assert (Ht : s ≠ t) by (intro; subst; lia); eexists; split.
    eapply rtc_once, one_pebble_step with (u:=s)(v:=t); try done; clia.
    simpl_alter; lia.
- (* Unsolvable configuration *)
  destruct (H 0%fin (alter (subtract k) 0%fin (const k))) as (c' & H1 & H2).
  + rewrite size_alter; cbn; [|lia].
    rewrite summation_const, fmap_length, length_fin_enum; lia.
  + apply rtc_inv in H1 as [<-|(c1 & H3 & H4)].
    * revert H2; simpl_alter; clia.
    * inv H3; revert H_conf; dec (u = 0%fin); simpl_alter; clia.
Qed.

End Basic_Pebbling_Bounds.
