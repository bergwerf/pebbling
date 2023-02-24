(*
C2. Pebbling in Hypercubes - Part I
===================================
*)

From graph_pebbling Require Import A_primitives B_pebbling C1_basic_bounds.

(*
A graph on two vertices
-----------------------
*)
Section Edge_Graph.

Variable R : relation bool.
Variable k : nat.

Context `{R_dec : RelDecision _ _ R, R_irrefl : Irreflexive _ R}.

Definition edge_graph : graph := {|
  graph_vertex := bool;
  graph_edge := R;
  graph_edge_weight := λ _ _, k;
|}.

Global Instance basic_edge_graph :
  Basic_Graph edge_graph.
Proof.
esplit; typeclasses eauto.
Defined.

End Edge_Graph.

(*
Pebbling in a product
---------------------
*)
Section Product_Pebbling.

Context `{graph_G : Basic_Graph G}.
Context `{graph_H : Basic_Graph H}.

Definition sub_conf i : conf G -> conf (H ☐ G) := prod_sub_val i.

Lemma size_sub_conf i c : size (sub_conf i c) = size c.
Proof. apply size_prod_sub_val. Qed.

Lemma rsize_sub_conf k i c : rsize k (sub_conf i c) = rsize k c.
Proof. apply rsize_prod_sub_val. Qed.

Lemma sub_conf_add i c c' :
  sub_conf i (c .+ c') = sub_conf i c .+ sub_conf i c'.
Proof. apply prod_sub_val_add. Qed.

Lemma lookup_sub_conf i c v : sub_conf i c (i, v) = c v.
Proof. unfold sub_conf; cbn; dec (i = i); done. Qed.

Lemma lookup_sub_conf_ne i j c v : i ≠ j -> sub_conf i c (j, v) = 0.
Proof. unfold sub_conf; cbn; dec (j = i); done. Qed.

Ltac simpl_sub_conf := simpl_lookup lookup_sub_conf lookup_sub_conf_ne.

Lemma sub_conf_zero i :
  sub_conf i (const 0) = const 0.
Proof.
extensionality v; destruct v as [j v];
dec (i = j); simpl_sub_conf; done.
Qed.

Lemma sub_conf_alter i f v c :
  sub_conf i (alter f v c) = alter f (i, v) (sub_conf i c).
Proof.
extensionality p; destruct p as [j w]; dec (j = i); dec (w = v);
repeat (simpl_sub_conf; simpl_alter); congruence.
Qed.

Lemma sub_pebbling i (c c' : conf G) :
  c -->* c' -> sub_conf i c -->* sub_conf i c'.
Proof.
apply rtc_congruence; clear; intros c c'; inversion_clear 1.
apply one_pebble_step with (u:=(i,u))(v:=(i,v)).
- right; done.
- cbn; dec (u = v).
  + exfalso; apply graph_edge_irrefl in H_edge; done.
  + dec (i = i); simpl_sub_conf; apply H_conf.
- subst; rewrite ?sub_conf_alter; repeat f_equal; cbn.
  dec (i = i); dec (u = v); [exfalso|done].
  apply graph_edge_irrefl in H_edge; done.
Qed.

Lemma product_pebbling k i j (c : conf G) :
  E H i j -> weight H i j = k ->
  sub_conf i (const k .* c) -->* sub_conf j c.
Proof.
intros H_ij <-; revert c; apply fn_nat_ind.
- rewrite right_absorb_lift2, ?sub_conf_zero; done.
- intros c v IH; rewrite alter_add, left_distr.
  rewrite ?sub_conf_add; apply pebbling_add; [done|].
  apply rtc_once, one_pebble_step with (u:=(i,v))(v:=(j,v)).
  + left; done.
  + cbn; dec (v = v); simpl_sub_conf; cbn; simpl_insert; lia.
  + extensionality u; destruct u as [l u]; cbn in l.
    apply irrefl_neq in H_ij; dec (l = i); [|dec (l = j)]; dec (u = v);
    simpl_alter; simpl_sub_conf; cbn; simpl_insert; cbn; try congruence.
    dec (v = v); lia. lia.
Qed.

End Product_Pebbling.

(*
The generalized pebbling property
---------------------------------
*)
Section Pebbling_Property.

Context `{graph_G : Basic_Graph G, pebb_G : Pebbling_Graph G}.

Definition vertex_pebbling_property (n k p : nat) (t : V G) :=
  ∀ c, size c ≥ p + 1 - supp c -> ∃ c', c' .≤ c ∧
    rsize k c' ≥ size c + supp c - p - 1 ∧
    solvable G t n (c .- c').

Definition pebbling_property n k p :=
  ∀ t, vertex_pebbling_property n k p t.

Lemma extend_vertex_pebbling_property m n k p t :
  vertex_pebbling_bound G p t ->
  vertex_pebbling_property m k (m * p) t -> 2 ≤ m ≤ n ->
  vertex_pebbling_property n k (n * p) t.
Proof.
intros H1p H2p Hm c H1c.
assert (H2c : size c ≥ size c - (n - m)*p) by nia.
assert (supp c ≤ p) by (apply (supp_le_vertex_pebbling_bound t); done).
apply fn_minor_eq_supp in H2c as (c1 & H1 & H2 & H3); [|nia].
destruct (H2p c1) as (c2 & H4 & H5 & c3 & H6 & H7); [nia|].
assert (H8 : size (c .- c1) ≥ (n - m)*p) by (rewrite size_sub; [nia|done]).
apply (vertex_pebbling_repeat p t) in H8 as (c4 & H9 & H10); [|done].
exists c2; repeat split. trans c1; done. nia.
replace (c .- c2) with ((c .- c1) .+ (c1 .- c2)) by ext_lia.
eexists; split. apply pebbling_add; done. clia.
Qed.

End Pebbling_Property.

Global Arguments vertex_pebbling_property _ {_}.
Global Arguments pebbling_property _ {_}.

Lemma pebbling_property_unit_graph n k :
  pebbling_property unit_graph n k n.
Proof.
intros [] c Hc; cbn in Hc; assert (c () ≥ n) by lia; clear Hc.
exists (c .- const n); repeat split. clia. clia.
eexists; split; [done|]; clia.
Qed.

(*
Transferring the pebbling property via a homomorphism
-----------------------------------------------------
*)
Section Pebbling_Property_Homomorphism.

Context `{graph_G : Basic_Graph G}.
Context `{graph_H : Basic_Graph H}.
Context `{hom : Graph_Hom G H h}.
Context `{surj : Surj _ _ (=) h}.

Theorem surj_hom_vertex_pebbling_property n k p t :
  vertex_pebbling_property G n k p t -> vertex_pebbling_property H n k p (h t).
Proof.
intros Hp c Hc; destruct (Hp (inv_dmap h c)) as (c' & H1 & H2 & H3).
- rewrite size_inv_dmap, supp_inv_dmap; done.
- exists (dmap h c'); repeat split.
  + apply dmap_le; done.
  + red; etrans; [|apply rsize_dmap].
    rewrite size_inv_dmap, supp_inv_dmap in H2; done.
  + rewrite <-(inv_dmap_spec c), <-dmap_sub; [|done].
    apply surj_hom_solvable; done.
Qed.

Corollary surj_hom_pebbling_property n k p :
  pebbling_property G n k p -> pebbling_property H n k p.
Proof.
intros Hp t; destruct (surj t) as [t' <-].
apply surj_hom_vertex_pebbling_property; done.
Qed.

End Pebbling_Property_Homomorphism.
