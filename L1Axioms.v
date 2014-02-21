Require Import Coq.Logic.Classical Rules DataTypes MsiState L1 Omega Coq.Relations.Relation_Operators Coq.Lists.Streams DataTypes.

Module mkL1Axioms : L1Axioms mkDataTypes.
  Import mkDataTypes.

  Theorem deqOrNot: forall t, {x| deqR (fst x) (snd x) t} + {forall c i, ~ deqR c i t}.
  Proof.
    intros t.
    unfold deqR.
    destruct (trans oneBeh t);
      solve [left; apply (exist _ (c, (req (sys oneBeh t) c))); intuition | intuition].
  Qed.

  Theorem deqLeaf: forall {c i t}, deqR c i t -> leaf c.
  Proof.
    intros c i t deqr.
    unfold deqR in deqr.
    destruct (trans oneBeh t);
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]);
    assert (c = c0) by auto; firstorder.
  Qed.

  Theorem deqDef: forall {c i t}, deqR c i t -> defined c.
  Proof.
    intros c i t deqr.
    unfold deqR in deqr.
    destruct (trans oneBeh t);
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]);
    assert (c = c0) by auto; firstorder.
  Qed.

  Theorem uniqDeqProc: forall {c i1 t i2},
                       deqR c i1 t -> deqR c i2 t ->
                       i1 = i2.
  Proof.
    intros c i1 t i2 deq1 deq2.
    unfold deqR in *.
    destruct (trans oneBeh t).
    simpl in *; destruct deq1 as [_ use1]; destruct deq2 as [_ use2];
                                           rewrite use1 in use2; firstorder.
    simpl in *; destruct deq1 as [_ use1]; destruct deq2 as [_ use2];
                                           rewrite use1 in use2; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.

  Theorem processDeq: forall {c i t}, deqR c i t ->
                                      let q := reqFn c i in
                                      match desc q with
                                        | Ld => sle Sh (state c (loc q) t)
                                        | St => state c (loc q) t = Mo
                                      end.
  Proof.
    intros c i t deqr.
    unfold state.
    unfold deqR in *.
    destruct (trans oneBeh t).

    destruct deqr as [eq u1].
    rewrite eq in *.
    rewrite u1 in *.
    rewrite e in *.
    assumption.

    destruct deqr as [eq u1].
    rewrite eq in *.
    rewrite u1 in *.
    rewrite e in *.
    assumption.

    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.



  Theorem reqGe: forall {c t1 t2}, t1 <= t2 -> req (sys oneBeh t2) c >= req (sys oneBeh t1) c.
  Proof.
    intros c t1 t2 le.
    remember (t2 - t1) as td.
    assert (t2 = t1 + td) by omega.
    rewrite H in *; clear le Heqtd H.
    induction td.
    assert (t1 + 0 = t1) by omega.
    rewrite H.
    omega.
    assert (t1 + S td = S (t1 + td)) by omega.
    rewrite H; clear H.
    assert (req (sys oneBeh (S (t1 + td))) c >= req (sys oneBeh (t1 + td)) c).
    destruct (trans oneBeh (t1 + td)).

    simpl.
    destruct (decTree c c0); omega.
    simpl.
    destruct (decTree c c0); omega.
    simpl.
    omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
  Qed.

  Theorem reqGeConv: forall {c t1 t2}, req (sys oneBeh t1) c < req (sys oneBeh t2) c -> t1 < t2.
  Proof.
    intros c t1 t2 reqEq.
    assert (t1 >= t2 \/ t1 < t2) by omega.
    destruct H.
    pose proof (@reqGe c _ _ H) as contra; omega.
    assumption.
  Qed.

  Theorem reqGt: forall {c i t1 t2}, t1 < t2 -> deqR c i t1 ->
                                     req (sys oneBeh t2) c > i.
  Proof.
    intros c i t1 t2 cond deqr.
    assert (S t1 <= t2) by omega.
    assert (req (sys oneBeh (S t1)) c > i).
    unfold deqR in *.
    destruct (trans oneBeh t1).
    simpl.
    destruct deqr as [eq sth].
    rewrite eq in *.
    destruct (decTree c c).
    rewrite sth; omega.
    firstorder.
    simpl.
    destruct deqr as [eq sth].
    rewrite eq in *.
    destruct (decTree c c).
    rewrite sth; omega.
    firstorder.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    pose proof (@reqGe c _ _ H).
    omega.
  Qed.

  Theorem uniqDeqProc2: forall {c i t1 t2},
                        deqR c i t1 -> deqR c i t2 -> t1 = t2.
  Proof.
    intros c i t1 t2 deq1 deq2.
    unfold Time in *.
    assert (t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.
    destruct H as [e1 | [e2 | e3]].
    assumption.
    pose proof (reqGt e2 deq1).
    unfold deqR in deq2.
    destruct (trans oneBeh t2).
    destruct deq2 as [_ u2].
    omega.
    destruct deq2 as [_ u2].
    omega.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    pose proof (reqGt e3 deq2).
    unfold deqR in deq1.
    destruct (trans oneBeh t1).
    destruct deq1 as [_ u2].
    omega.
    destruct deq1 as [_ u2].
    omega.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.

  Theorem uniqDeqProc3: forall {c1 i1 t c2 i2},
                          deqR c1 i1 t -> deqR c2 i2 t ->
                          c1 = c2 /\ i1 = i2.
  Proof.
    intros c1 i1 t c2 i2 deq1 deq2.
    unfold deqR in *.
    destruct (trans oneBeh t);
      solve [
          repeat match goal with
                   | [d: _ /\ _ |- _] => destruct d
                 end;
          rewrite <- H1 in *; rewrite <- H in *;
          rewrite <- H2; rewrite <- H0;
          intuition| intuition].
  Qed.

  Theorem incReqImpDeq: forall {c t i},
                           req (sys oneBeh t) c > i ->
                           exists t', t' < t /\ deqR c i t'.
  Proof.
    intros c t i reqEq.
    induction t.
    pose proof (init oneBeh) as sth.
    rewrite sth in reqEq; clear sth.
    unfold initGlobalState in *; simpl in *.
    omega.
    assert (inc:req (sys oneBeh (S t)) c = req (sys oneBeh t) c \/
                req (sys oneBeh (S t)) c = S (req (sys oneBeh t) c)).
    destruct (trans oneBeh t).
    simpl in *.
    destruct (decTree c c0).
    right.
    intuition.
    left.
    intuition.
    simpl in *.
    destruct (decTree c c0).
    right.
    intuition.
    left.
    intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.

    destruct inc.
    rewrite H in reqEq.
    specialize (IHt reqEq).
    destruct IHt as [t' [t'_lt_t deq]].
    exists t'.
    assert (t' < S t) by omega; intuition.
    rewrite H in reqEq.
    assert (opts: req (sys oneBeh t) c > i \/ req (sys oneBeh t) c = i) by omega.
    destruct H.
    destruct opts.
    specialize (IHt H).
    destruct IHt as [t' [t'_lt_t deq]].
    exists t'.
    constructor.
    omega.
    assumption.
    rewrite <- H in *; clear H.
    exists t.
    constructor.
    omega.
    unfold deqR.
    destruct (trans oneBeh t).
    simpl in *.
    destruct (decTree c c0).
    constructor; auto.
    omega.
    simpl in *.
    destruct (decTree c c0).
    constructor; auto.
    omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
  Qed.

  Theorem deqImpDeqBefore: forall {c i1 i2 t},
                             deqR c i1 t -> i2 < i1 -> exists t', t' < t /\ deqR c i2 t'.
  Proof.
    intros c i1 i2 t deq i2_lt_i1.
    unfold deqR in deq.
    destruct (trans oneBeh t).
    destruct deq as [eq sth].
    rewrite eq in *.
    rewrite <- sth in *.
    pose proof (incReqImpDeq i2_lt_i1) as [x [z y]]; exists x; intuition.
    destruct deq as [eq sth].
    rewrite eq in *.
    rewrite <- sth in *.
    pose proof (incReqImpDeq i2_lt_i1) as [x [z y]]; exists x; intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.

  Theorem deqOrder: forall {c i1 t1 i2 t2},
                      deqR c i1 t1 -> deqR c i2 t2 ->
                      i1 < i2 -> ~ t1 > t2.
  Proof.
    unfold not; intros c i1 t1 i2 t2 deq1 deq2 iLess t2Less.
    pose proof (reqGt t2Less deq2).
    unfold deqR in deq1.
    destruct (trans oneBeh t1).
    destruct deq1 as [_ u]; omega.
    destruct deq1 as [_ u]; omega.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.
End mkL1Axioms.