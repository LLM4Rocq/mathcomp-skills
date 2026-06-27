From mathcomp Require Import all_ssreflect.

Local Open Scope ring_scope.

Lemma t1 x : x = x.
Proof. apply : erefl. Qed.

Lemma foo_is_zero : (0 : nat) = 0.
Proof. by []. Qed.

Definition g : {ffun 'I_3 -> nat} := fun i => 0.
