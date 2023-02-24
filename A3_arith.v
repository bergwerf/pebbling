(*
A3. Arithmetic Properties
=========================
*)

From graph_pebbling Require Import A1_misc A2_lift.

Infix ".≤" := (liftR le) (at level 60).
Infix ".+" := (lift2 Nat.add) (at level 50).
Infix ".-" := (lift2 Nat.sub) (at level 50).
Infix ".*" := (lift2 Nat.mul) (at level 50).

Notation "(+)" := Nat.add (only parsing).
Notation "(-)" := Nat.sub (only parsing).
Notation "(.+)" := (lift2 Nat.add) (only parsing).
Notation "(.-)" := (lift2 Nat.sub) (only parsing).
Notation "(.*)" := (lift2 Nat.mul) (only parsing).

Notation min := Nat.min.
Notation max := Nat.max.
Notation lift_min := (lift2 min).
Notation lift_max := (lift2 max).
Notation add1 := (Nat.add 1).

Notation gcd := Nat.gcd.
Notation "m ∣ n" := ((m | n)) (at level 50).

Ltac inst_lift_le x :=
  repeat match goal with
  | H : _ .≤ _ |- _ => inst H x; clear H
  end.

Ltac ext_lia :=
  let x := fresh "x" in
  extensionality x;
  inst_lift_le x; cbn; lia.

(* Nat.sub with the subtrahend first. *)
Definition subtract (n k : nat) := k - n. 
Global Arguments subtract _ _ /.
Global Arguments min _ _ : simpl nomatch.

Section Properties.

Ltac see H := repeat intro; cbn; apply H.

Global Instance : IdemP (=) Nat.max := Nat.max_id.
Global Instance : IdemP (=) Nat.min := Nat.min_id.

Global Instance : LeftId (=) 0 Nat.max := Nat.max_0_l.
Global Instance : RightId (=) 0 Nat.max := Nat.max_0_r.
Global Instance : LeftId (=) 0 Nat.add := Nat.add_0_l.
Global Instance : RightId (=) 0 Nat.add := Nat.add_0_r.
Global Instance : LeftId (=) 1 Nat.mul := Nat.mul_1_l.
Global Instance : RightId (=) 1 Nat.mul := Nat.mul_1_r.

Global Instance : LeftAbsorb (=) 0 Nat.min := Nat.min_0_l.
Global Instance : RightAbsorb (=) 0 Nat.min := Nat.min_0_r.
Global Instance : LeftAbsorb (=) 0 Nat.mul := Nat.mul_0_l.
Global Instance : RightAbsorb (=) 0 Nat.mul := Nat.mul_0_r.

Global Instance : Assoc (=) Nat.min := Nat.min_assoc.
Global Instance : Assoc (=) Nat.max := Nat.max_assoc.
Global Instance : Assoc (=) Nat.add := Nat.add_assoc.
Global Instance : Assoc (=) Nat.mul := Nat.mul_assoc.

Global Instance : Comm (=) Nat.min := Nat.min_comm.
Global Instance : Comm (=) Nat.max := Nat.max_comm.
Global Instance : Comm (=) Nat.add := Nat.add_comm.
Global Instance : Comm (=) Nat.mul := Nat.mul_comm.

Global Instance : LeftDistr (=) Nat.mul Nat.add := Nat.mul_add_distr_l.
Global Instance : RightDistr (=) Nat.mul Nat.add := Nat.mul_add_distr_r.
Global Instance : LeftDistr (=) Nat.mul Nat.sub. see Nat.mul_sub_distr_l. Qed.
Global Instance : RightDistr (=) Nat.mul Nat.sub. see Nat.mul_sub_distr_r. Qed.
Global Instance : LeftDistr (=) Nat.mul subtract. see Nat.mul_sub_distr_l. Qed.
Global Instance : RightDistr (=) Nat.mul subtract. see Nat.mul_sub_distr_r. Qed.

Global Instance left_dominant_le n :
  LeftDominant (le n) (+).
Proof. clia. Qed.

Global Instance left_comm_add_add n :
  CondLeftComm (=) (λ _, True) ((+) n) (+).
Proof. clia. Qed.

Global Instance left_comm_subtract_add n :
  CondLeftComm (=) (le n) (subtract n) (+).
Proof. clia. Qed.

End Properties.

Lemma alter_add `{EqDecision A} (f : A -> nat) n a :
  alter ((+) n) a f = f .+ <[a:=n]> (const 0).
Proof.
extensionality b; dec (b = a);
simpl_alter; cbn; simpl_insert; clia.
Qed.
