(*
C3. Pebbling in a Divisor Lattice
=================================
*)

From graph_pebbling Require Import
  A_primitives B_pebbling C1_basic_bounds
  C2_hypercube_I C2_hypercube_II.

Section Prime_Factors.

Definition min_prime_factor (p n : nat) :=
  minimal (≤) (λ p, 1 < p ∧ p ∣ n) p.

Lemma find_min_prime_factor n :
  n > 1 -> ∃ p, min_prime_factor p n.
Proof.
intros Hn; destruct (list_find (λ p, 1 < p ∧ p ∣ n) (seq 0 (S n))) eqn:E.
- destruct p as [p p']; apply list_find_Some in E as (H' & [] & Hp).
  apply lookup_seq in H' as [-> ?].
  exists p; split; [done|]; intros q [? ?].
  dec (p ≤ q); [done|exfalso]; eapply (Hp q); [|lia|done].
  apply lookup_seq; split; [done|].
  apply Nat.divide_pos_le in H3; lia.
- apply list_find_None in E; assert (H : ¬ (1 < n ∧ n ∣ n)).
  + eapply list.Forall_forall in E; [done|].
    apply elem_of_seq; lia.
  + exfalso; apply H; done.
Qed.

End Prime_Factors.

Section Divisor_Lattice.

Variable n : nat.
Hypothesis non_zero : Premise (n > 0).

Definition divisor_lattice : graph := {|
  graph_vertex := dsig (λ p, p ∣ n );
  graph_edge := λ p q, `p ≠ `q ∧ `p ∣ `q;
  graph_edge_weight := λ p q, `q `div` `p;
|}.

Definition top_divisor : V divisor_lattice :=
  @dexist _ (λ p, p ∣ n) _ n (Nat.divide_refl n).

Global Instance divisor_lattice_vertex_fin :
  Finite (V divisor_lattice).
Proof.
exists (dsig_filter _ (seq 1 n)).
- apply NoDup_dsig_filter, NoDup_seq.
- intros [p Hp]; apply elem_of_dsig_filter; cbn.
  apply bool_decide_unpack in Hp; apply elem_of_seq.
  apply @premise in non_zero; split; [destruct Hp; lia|].
  apply Nat.divide_pos_le in Hp; lia.
Qed.

Global Instance basic_divisor_lattice :
  Basic_Graph divisor_lattice.
Proof.
esplit; try typeclasses eauto.
- solve_decision.
- intros p [H _]; done.
Defined.

Global Instance pebb_divisor_lattice :
  Pebbling_Graph divisor_lattice.
Proof.
split; intros [p Hp] [q Hq]; cbn; intros [H [m ->]].
apply bool_decide_unpack in Hp, Hq; apply @premise in non_zero.
rewrite Nat.div_mul; [|lia]; destruct Hq, m; nia.
Qed.

End Divisor_Lattice.

Section Divisor_Pebbling.

Section Unit_Homomorphism.

Lemma divisor_lattice_unit_hom_spec :
  Graph_Hom unit_graph (divisor_lattice 1) (const (top_divisor 1)).
Proof. done. Qed.

Lemma divisor_lattice_unit_hom_surj :
  @Surj unit _ (=) (const (top_divisor 1)).
Proof.
intros [p Hp]; exists (); cbn.
apply dsig_eq; cbn; apply bool_decide_unpack in Hp.
destruct Hp as [[]]; lia.
Qed.

End Unit_Homomorphism.

Section Composite_Homomorphism.

Variable p n : nat.
Hypothesis n_pos : Premise (n > 0).
Hypothesis p_pri : min_prime_factor p (p * n).
Notation P := (edge_graph Bool.lt p).

Lemma hom_composite_certificate (b : bool) (d : V (divisor_lattice n)) :
  (if b then p else 1) * `d ∣ p * n.
Proof.
destruct d as [d Hd], b; cbn; apply bool_decide_unpack in Hd.
- apply Nat.mul_divide_mono_l; done.
- rewrite Nat.add_0_r; apply Nat.divide_mul_r; done.
Qed.

Definition hom_composite (f : V P * V (divisor_lattice n)) :
  V (divisor_lattice (p * n)) :=
  let (b, d) := f in dexist
    ((if b then p else 1) * `d)
    (hom_composite_certificate b d).

Lemma hom_composite_surj :
  Surj (=) hom_composite.
Proof.
assert (Hp : 1 < p) by (destruct p_pri as [[Hp _] _]; done).
intros [i H]; apply bool_decide_unpack in H as Hi.
destruct (decide (p ∣ i)) as [[m Hm]|].
- (* p is a factor of i. *)
  rewrite Nat.mul_comm in Hm; subst.
  apply Nat.mul_divide_cancel_l in Hi; [|lia].
  exists (true, dexist m Hi); apply dsig_eq; done.
- (* p is not a factor of i. *)
  apply Nat.gauss in Hi.
  + exists (false, dexist i Hi); apply dsig_eq; apply Nat.add_0_r.
  + (* i and p are coprime. *)
    apply Nat.gcd_unique; [lia|apply Nat.divide_1_l|apply Nat.divide_1_l|].
    intros q H1 H2.
    dec (q = 0); [apply Nat.divide_0_l in H2; lia|].
    dec (q = 1); [done|exfalso].
    (* Since p is prime, any non-trivial factor is equal to p. *)
    assert (Hq : q > 1 ∧ q ∣ p * n).
    * split; [lia|apply Nat.divide_mul_l; done].
    * apply p_pri in Hq; apply Nat.divide_pos_le in H2; [|lia].
      assert (q = p) by lia; subst; done.
Qed.

Lemma hom_composite_spec :
  Graph_Hom (P ☐ divisor_lattice n) (divisor_lattice (p * n)) hom_composite.
Proof.
apply @premise in n_pos as Hn; destruct p_pri as [[Hp _] _]; split.
- intros [[] [q Hq]] [[] [r Hr]]; cbn; intuition;
  simplify_eq; rewrite ?Nat.add_0_r; try done; try nia.
  + apply Nat.mul_divide_cancel_l; [lia|done].
  + apply bool_decide_unpack in Hr as []; nia.
  + apply Nat.divide_factor_r.
- intros [[] [q Hq]] [[] [r Hr]]; cbn; intuition;
  repeat destruct (decide _); simplify_eq; rewrite ?Nat.add_0_r; try nia.
  apply Nat.div_mul; apply bool_decide_unpack in Hr as H; destruct H; lia.
Qed.

End Composite_Homomorphism.

Theorem pebbling_the_divisor_lattice n (non_zero : Premise (n > 0)) p :
  (n = 1 ∨ min_prime_factor p n) ->
  vertex_pebbling_bound (divisor_lattice n) n (top_divisor n) ∧
  vertex_pebbling_property (divisor_lattice n) 2 p (2 * n) (top_divisor n).
Proof.
apply @premise in non_zero as Hn.
revert p; induction n as [n IH] using lt_wf_ind; intros p [->|Hp].
- split.
  + eapply @surj_hom_pebbling_bound.
    * apply divisor_lattice_unit_hom_spec; done.
    * apply divisor_lattice_unit_hom_surj; done.
    * apply pebbling_number_unit_graph.
  + eapply @surj_hom_pebbling_property.
    * apply divisor_lattice_unit_hom_spec; done.
    * apply divisor_lattice_unit_hom_surj; done.
    * apply pebbling_property_unit_graph.
- assert (Hm := Hp); destruct Hp as [[Hp [m E]] _];
  rewrite Nat.mul_comm in E; subst n; assert (m > 0) by lia.
  cut (∃ q, p ≤ q ∧ (m = 1 ∨ min_prime_factor q m)).
  + intros (q & H1q & H2q); assert (Premise (m > 0)) by done.
    eapply IH in H2q as [H1m H2m]; [|nia|done].
    replace (top_divisor _) with (hom_composite p m (true, top_divisor m))
    by (apply dsig_eq; done); split.
    * eapply (@surj_hom_vertex_pebbling_bound (_ ☐ _)).
      apply hom_composite_spec; done.
      apply hom_composite_surj; done.
      apply vertex_pebbling_bound_arrow_prod with (l:=q); done.
    * eapply (@surj_hom_vertex_pebbling_property (_ ☐ _)).
      apply hom_composite_spec; done.
      apply hom_composite_surj; done. rewrite Nat.mul_assoc.
      apply vertex_pebbling_property_arrow_prod with (l:=q); done.
  + dec (m = 1).
    * exists p; split; [|left]; done.
    * destruct (find_min_prime_factor m) as [q [[]]]; [lia|exists q].
      split; [|right; done]. apply Hm; split; [done|].
      apply Nat.divide_mul_r; done.
Qed.

Corollary vertex_pebbling_bound_divisor_lattice n (non_zero : Premise (n > 0)) :
  vertex_pebbling_bound (divisor_lattice n) n (top_divisor n).
Proof.
apply @premise in non_zero as H; dec (n = 1).
- apply pebbling_the_divisor_lattice with (p:=0); left; done.
- edestruct (find_min_prime_factor n) as [p Hp]; [lia|].
  eapply pebbling_the_divisor_lattice; right; done.
Qed.

End Divisor_Pebbling.
