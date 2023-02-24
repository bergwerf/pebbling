(*
C2. Pebbling in Hypercubes - Part II
====================================
*)

From graph_pebbling Require Import A_primitives B_pebbling C1_basic_bounds.
From graph_pebbling Require Import C2_hypercube_I.

(*
Pebbling in a product with P2
-----------------------------
*)
Section Two_Path_Product.

Ltac pebbling_left := eapply pebbling_add; [|reflexivity].
Ltac pebbling_right := eapply pebbling_add; [reflexivity|].
Ltac simpl_sub_conf := simpl_lookup lookup_sub_conf lookup_sub_conf_ne.

Context `{graph_G : Basic_Graph G, pebb_G : Pebbling_Graph G}.

Variable p l k : nat.
Hypothesis Hk : 2 ≤ k ≤ l.
Notation v0 := false.
Notation v1 := true.
Notation arrow := (edge_graph Bool.lt k).
Notation path2 := (edge_graph neq k).

(*
Pebbling with a fixed target
----------------------------
*)
Section Fixed_Target.

Variable t : V G.
Hypothesis H1p : vertex_pebbling_bound G p t.
Hypothesis H2p : vertex_pebbling_property G 2 l (2 * p) t.

Notation p_gt1 := (vertex_pebbling_bound_ge1 _ _ H1p).
Notation supp_le := (supp_le_vertex_pebbling_bound t _ _ H1p).
Notation ext_pp := (extend_vertex_pebbling_property 2 _ _ _ _ H1p H2p).

Notation sub0 := (@sub_conf G _ arrow _ v0).
Notation sub1 := (@sub_conf G _ arrow _ v1).
Notation "c ^0" := (c ∘ pair v0) (at level 5, format "c ^0").
Notation "c ^1" := (c ∘ pair v1) (at level 5, format "c ^1").

Local Lemma add_sub_confs (c : conf (arrow ☐ G)) :
  sub0 c^0 .+ sub1 c^1 = c.
Proof.
extensionality v; destruct v as [i v]; unfold sub_conf; cbn.
destruct i; repeat destruct (decide _); done.
Qed.

Local Lemma size_sub_confs (c : conf (arrow ☐ G)) :
  size c = size c^0 + size c^1.
Proof.
rewrite <-add_sub_confs at 1;
rewrite size_add, ?size_sub_conf; done.
Qed.

Local Lemma split_sub_minor (c0 c0' c1 c1' : conf G) :
  sub0 c0' .+ sub1 c1' .≤ sub0 c0 .+ sub1 c1 -> c0' .≤ c0 ∧ c1' .≤ c1.
Proof.
split; intros v; cbn.
- inst H (v0, v); simpl_sub_conf; lia.
- inst H (v1, v); simpl_sub_conf; lia.
Qed.

Local Lemma move_all_pebbles (c c' : conf G) :
  const k .* c' .≤ c -> sub0 c -->* sub1 c' .+ sub0 (c .- (const k .* c')).
Proof.
remember (const k .* c') as ck.
intros H; replace c with (ck .+ (c .- ck)) at 1 by ext_lia.
rewrite sub_conf_add; pebbling_left; subst. apply product_pebbling; done.
Qed.

Lemma vertex_pebbling_bound_arrow_prod :
  vertex_pebbling_bound (arrow ☐ G) (k * p) (v1, t).
Proof.
intros c Hc;
assert (H1c := size_sub_confs c);
assert (H2c : supp c^0 ≤ p) by apply supp_le.
dec (size c^1 < supp c^0).
- (*
  size c^0 > k*p - supp c^0
  -------------------------
  1. Move k pebbles to (0,t) in c^0.
  2. Move 1 pebble from (0,t) to (1,t).
  *)
  assert (H_c0 : size c^0 ≥ k*p + 1 - supp c^0) by nia.
  eapply ext_pp in H_c0 as (c0a & H1_c0 & H2_c0 & c1b & H3_c0 & H4_c0); [|lia].
  eexists; split; [eapply rtc_r|].
  + (* Move k pebbles to (0,t) in c^0. *)
    rewrite <-add_sub_confs at 1; pebbling_left; apply sub_pebbling.
    replace c^0 with ((c^0 .- c0a) .+ c0a) by ext_lia.
    pebbling_left; apply H3_c0.
  + (* Move 1 pebble from (0,t) to (1,t). *)
    apply one_pebble_step with (u:=(v0,t))(v:=(v1,t)); [cbn|cbn|done].
    left; done. dec (t = t); simpl_sub_conf; clia.
  + (* There is now 1 pebble at (1,t). *)
    simpl_alter; clia.
- (*
  size c^1 + rsize k c^0 / k ≥ p
  ------------------------------
  1. Move m/k pebbles from c^0 to c^1.
  2. Move 1 pebble to (1,t) in c^1.
  *)
  pose (m := rsize k c^0).
  assert (H_c0 : rsize k c^0 ≥ m/k*k) by nia.
  apply rsize_minor in H_c0 as (c0a & H1_c0a & H2_c0a); [|lia].
  assert (H_c1 : size (c^1 .+ c0a) ≥ p).
  { rewrite size_add, H2_c0a; unfold m, rsize; nia. }
  apply H1p in H_c1 as (c1a & H1_c1a & H2_c1a).
  eexists; split; [etrans|].
  + (* Move m/k pebbles from c^0 to c^1. *)
    rewrite <-add_sub_confs at 1; pebbling_left.
    apply move_all_pebbles; done.
  + (* Move 1 pebble to (1,t) in c^1. *)
    rewrite (comm (.+)), (assoc (.+)); pebbling_left.
    rewrite  <-sub_conf_add; apply sub_pebbling, H1_c1a.
  + (* There is now 1 pebble at (1,t). *)
    cbn; simpl_sub_conf; lia.
Qed.

Lemma vertex_pebbling_property_arrow_prod :
  vertex_pebbling_property (arrow ☐ G) 2 k (2 * k * p) (v1, t).
Proof.
intros c Hc;
assert (H1c : size c = size c^0 + size c^1) by apply size_sub_confs;
assert (H2c : supp c = supp c^0 + supp c^1) by apply size_sub_confs;
assert (H3c : supp c^1 ≤ p ∧ supp c^0 ≤ p) by (split; apply supp_le).
dec (2*p - supp c^1 < size c^1).
- (*
  size c^1 > 2*p - supp c^1
  -------------------------
  1. Move 2 pebbles to (1,t) and isolate pebbles in c^1.
  2. Isolate pebbles in c^0.
  *)
  assert (H_c1 : size c^1 ≥ 2*p + 1 - supp c^1) by lia.
  apply H2p in H_c1 as (c1a & H1_c1a & H2_c1a & c1b & H1_c1b & H2_c1b).
  destruct (rsize_add k (sub0 c^0) (sub1 c1a)) as (c' & H1_c' & H2_c').
  exists c'; repeat split.
  + (* c' is a minor of c. *)
    etrans; [done|]; intros [i v]; cbn in i; unfold sub0, sub1; cbn.
    destruct i; repeat destruct (decide _); try done; [|lia].
    cbn; apply H1_c1a.
  + (* c' isolates enough pebbles. *)
    red; etrans; [|apply H2_c']; rewrite ?rsize_sub_conf.
    cut (p ≥ 1 ∧ rsize k c1a ≥ size c^1 + supp c^1 - 2 * p - 1).
    * rewrite H1c, H2c; revert Hk H3c; clear; intros; unfold rsize at 1; nia.
    * split; [apply p_gt1|]. red; etrans; [apply H2_c1a|]; apply rsize_le; lia.
  + (* c .- c' is 2-fold solvable. *)
    eexists; split.
    * (* Move 2 pebbles to (1,t) in c^1. *)
      eapply pebbling_minor; [eapply sub_pebbling with (i:=v1), H1_c1b|].
      rewrite <-(add_sub_confs c') in H1_c';
      apply split_sub_minor in H1_c' as [_ H3_c1a].
      intros [i v]; cbn; destruct i; simpl_sub_conf; [cbn|lia].
      inst H3_c1a v; lia.
    * (* There are now 2 pebbles at (1,t). *)
      cbn; simpl_sub_conf; lia.
- (*
  size c^1 ≤ 2*p - supp c^1
  -------------------------
  1. Move k pebbles to (0,t) and isolate pebbles in c^0.
  2. Move m/k pebbles from c^0 to c^1.
  3. Move 1 pebble to (1,t) in c^1.
  4. Move 1 pebble from (0,t) to (1,t).
  *)
  pose (m := k*p - size c^1 - supp c^1).
  assert (H1_c0 : size c^1 ≤ 2*p - supp c^1) by lia.
  assert (H2_c0 : size c^0 ≥ k*p + 1 - supp c^0) by nia.
  eapply ext_pp in H2_c0 as (c0a & H2_c0 & H3_c0 & c0b & H4_c0 & H5_c0); [|lia].
  assert (H1_c0a : rsize k c0a ≥ m + size c + supp c - 2*k*p - 1).
  { red; etrans; [|etrans]; [|apply H3_c0|apply rsize_le; lia].
    rewrite H1c, H2c; revert H1_c0 Hk H3c; clear; nia. }
  assert (H2_c0a : rsize k c0a ≥ m/k*k) by lia.
  apply rsize_minor in H2_c0a as (c0c & H1_c0c & H2_c0c); [|lia].
  assert (H3_c0c : size (c^1 .+ c0c) ≥ p).
  { rewrite size_add, H2_c0c; revert Hk; clear.
    assert (supp c^1 ≤ size c^1) by apply supp_le_size; nia. }
  apply H1p in H3_c0c as (c1a & H1_c1a & H2_c1a).
  pose (c' := sub0 (c0a .- (const k .* c0c))); exists c'; repeat split.
  + (* c' is a minor of c. *)
    unfold c'; intros [i v]; cbn.
    destruct i; simpl_sub_conf; cbn; [lia|].
    inst H2_c0 v; clear; lia.
  + (* c' isolates enough pebbles. *)
    unfold c'; rewrite rsize_sub_conf.
    red; etrans; [|apply rsize_sub; done].
    rewrite size_mul_const, H2_c0c.
    revert H1_c0a; clear; lia.
  + (* c .- c' is 2-fold solvable. *)
    { eexists; split; [etrans|].
    - replace (c .- c') with (sub0 ((c^0.-c0a) .+ (const k.*c0c)) .+ sub1 c^1).
      pebbling_left; rewrite sub_conf_add; eapply pebbling_add.
      + (* Move k pebbles to (0,t). *)
        eapply sub_pebbling, H4_c0.
      + (* Move m/k pebbles to c^1. *)
        apply product_pebbling with (j:=v1); done.
      + extensionality v; destruct v as [i v]; cbn.
        destruct i; unfold c'; simpl_sub_conf; cbn; [clear; lia|].
        inst H2_c0 v; inst H1_c0c v; clear; lia.
    - (* Move 2 pebbles to (1,t). *)
      rewrite <-(assoc (.+)), <-sub_conf_add; apply pebbling_add.
      + (* Move 1 pebble from (0,t). *)
        apply rtc_once, one_pebble_step with (u:=(v0,t))(v:=(v1,t)).
        left; done. cbn; dec (t = t); simpl_sub_conf; lia. done.
      + (* Move 1 pebble in c^1. *)
        apply sub_pebbling; rewrite (comm (.+)); apply H1_c1a.
    - (* There are now 2 pebbles at (1,t). *)
      cbn; simpl_sub_conf; simpl_alter; revert H2_c1a; clear; lia.
    }
Qed.

End Fixed_Target.

Section Automorphism.

Definition arrow_prod_neg (v : V (arrow ☐ G)) : V (path2 ☐ G) :=
  (negb v.1, v.2).

Lemma arrow_prod_neg_id :
  arrow_prod_neg ∘ arrow_prod_neg = id.
Proof. extensionality v; destruct v as [[] v]; cbn; done. Qed.

Lemma hom_arrow_prod_id :
  Graph_Hom (arrow ☐ G) (path2 ☐ G) id.
Proof. split; intros [[] u] [[] v]; cbn; intuition; [left|right]; done. Qed.

Lemma hom_arrow_prod_neg :
  Graph_Hom (arrow ☐ G) (path2 ☐ G) arrow_prod_neg.
Proof. split; intros [[] u] [[] v]; cbn; intuition; [left|right]; done. Qed.

Lemma arrow_prod_normalize i v :
  ∃ h, invertible h ∧ Graph_Hom (arrow ☐ G) (path2 ☐ G) h ∧ (i, v) = h (v1, v).
Proof.
destruct i; [exists id|exists arrow_prod_neg].
- split; [|split]; [apply invertible_id|apply hom_arrow_prod_id|done].
- split; [|split]; [|apply hom_arrow_prod_neg|done].
  eexists; split; apply arrow_prod_neg_id.
Qed.

End Automorphism.

Hypothesis H1p : pebbling_bound G p.
Hypothesis H2p : pebbling_property G 2 l (2 * p).

Theorem pebbling_bound_path2_prod :
  pebbling_bound (path2 ☐ G) (k * p).
Proof.
intros [i r] c Hc;
destruct (arrow_prod_normalize i r) as (h & H_inv & H_aut & ->).
apply invertible_inj in H_inv; apply inj_hom_solvable.
apply vertex_pebbling_bound_arrow_prod; [done|done|].
rewrite size_compose; done.
Qed.

Theorem pebbling_property_path2_prod :
  pebbling_property (path2 ☐ G) 2 k (2 * k * p).
Proof.
intros [i r] c Hc;
destruct (arrow_prod_normalize i r) as (h & H_inv & H_aut & ->).
apply invertible_inj in H_inv as H1_inj.
destruct H_inv as (h_inv & H1_inv & H2_inv).
assert (H2_inj : Inj (=) (=) h_inv) by (apply invertible_inj; eexists; done).
edestruct vertex_pebbling_property_arrow_prod with (c:=c ∘ h) as (c' & H);
[done|done|rewrite size_compose, supp_compose; done|];
destruct H as (H1 & H2 & H3); exists (c' ∘ h_inv); repeat split.
- intros v; cbn; inst H1 (h_inv v).
  rewrite <-(compose_def h_inv h), H2_inv; done.
- rewrite rsize_compose; rewrite size_compose, supp_compose in H2; done.
- apply inj_hom_solvable; rewrite right_distr_compose_lift2, <-assoc_compose;
  rewrite H1_inv, right_id_compose; done.
Qed.

End Two_Path_Product.
