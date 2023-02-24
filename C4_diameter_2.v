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

Theorem pebbling_diameter_2 :
  pebbling_bound G (card V + 1).
Proof.
(* TODO *)
Admitted.

End Diameter_2.