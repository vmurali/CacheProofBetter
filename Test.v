Require Import Arith Omega.

Section Test.
  Variable msg: Type.
  Variable process avail cond : msg -> nat -> Prop.
  Variable classical: forall P, P \/ ~ P.
  Axiom processImpAvail: forall {x t}, process x t -> avail x t.
  Axiom processImpCond: forall {x t}, process x t -> cond x t.
  Axiom availNoProcess: forall {x t}, avail x t -> ~ process x t -> avail x (S t).
  Axiom processImpNoAvail: forall {x t}, process x t -> forall {t'}, t' > t -> ~ avail x t'.

  Lemma noProcessAvailAll: forall {x t}, avail x t ->
    forall {t'}, (forall t'', t <= t'' < t + t' -> ~ process x t'') -> avail x (t + t').
  Proof.
    intros x t availt t' noProcess.
    induction t'.
    assert (tEq0: t + 0 = t) by omega.
    congruence.
    assert (forall t'', t <= t'' < t + t' -> ~ process x t'') by (intros t'' cond2;
      assert (t <= t'' < t + S t') by omega; firstorder).
    specialize (IHt' H).
    assert (~ process x (t + t')) by (assert (t <= t + t' < t + S t') by omega; firstorder).
    pose proof (availNoProcess IHt' H0).
    assert (t + S t' = S (t + t')) by omega.
    congruence.
  Qed.

  Lemma noProcess: forall {x t}, avail x t -> forall {t'}, t <= t' -> (forall t'', t <= t'' < t' ->
    ~ process x t'') -> avail x t'.
  Proof.
    intros x t availt t' tLeT' noProcess.
    remember (t'-t) as td.
    assert (t' = t + td) by omega.
    rewrite H in *.
    apply (noProcessAvailAll availt noProcess).
  Qed.

  Section test.
    Variable (x: msg) (t: nat).
    Variable availt: avail x t.
    Variable forever: forall {t'}, t' >= t -> exists t'', t'' >= t' /\ (avail x t'' -> cond x t'').

    Lemma canGet: exists t', t' >= t /\ avail x t' /\ cond x t'.
    Proof.
      assert (tGeT: t >= t) by omega.
      specialize (forever t tGeT).
      destruct forever as [t'' [t''GeT fn]].      
      destruct (classical (exists t', t <= t' < t'' /\ process x t')) as [proc | noProc].
      destruct proc as [t' [cond2 processt']].
      exists t'.
      pose proof (processImpAvail processt').
      pose proof (processImpCond processt').
      firstorder.
      assert (noProc': forall t', t <= t' < t'' -> ~ process x t') by (
        firstorder).
      assert (H: t'' = t \/ t'' > t) by omega.
      destruct H as [t''EqT | t''GtT].
      rewrite t''EqT in *.
      exists t.
      firstorder.
      pose proof (noProcess availt t''GeT noProc') as H.
      exists t''.
      firstorder.
    Qed.
  End test.
End Test.