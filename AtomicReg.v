Require Import DataTypes StoreAtomicity Case NamedTrans Useful.

Set Implicit Arguments.

Record State := { mem: Addr -> Data;
                  next: Cache -> nat
                }.

Inductive AtomicTrans s: State -> Set :=
| Req: forall c, AtomicTrans s (Build_State
                                  (match desc (reqFn c (next s c)) with
                                     | Ld => mem s
                                     | St =>
                                       fun t
                                       =>
                                         match decAddr t (loc (reqFn c (next s c))) with
                                           | left _ => dataQ (reqFn c (next s c))
                                           | _ => mem s t
                                         end
                                   end)
                                  (fun t => match decTree t c with
                                              | left _ => S (next s t)
                                              | _ => next s t
                                            end))
| Idle: AtomicTrans s s.

Module Bisum (d: DataTypes) (s: StoreAtomicity d).
  Import d s.

  Section SomeList.
    Definition SomeList := TransList AtomicTrans (Build_State initData (fun t => 0)).

    About NextTrans.
    Variable (getTransNext: forall n s, SomeList n s -> NextTrans AtomicTrans s).

    Lemma nextLe t c: next (getTransState getTransNext t) c <=
                      next (getTransState getTransNext (S t)) c.
    Proof.
      pose (getTrans getTransNext t) as trans;
      unfold getTransState;
      unfold getTransList;
      fold (getTransList getTransNext t).
      simpl; destruct trans; [simpl; destruct (decTree c c0) | ]; omega.
    Qed.

    Lemma nextStarLe t1 t2 c (cond: t1 <= t2): next (getTransState getTransNext t1) c <=
                                               next (getTransState getTransNext t2) c.
    Proof.
      remember (t2-t1) as td; assert (H: t2 = t1 + td) by omega;
      rewrite H in *; clear t2 cond H Heqtd.
      induction td.
      assert (H: t1 + 0 = t1) by omega; rewrite H; omega.
      assert (H: t1 + S td = S (t1 + td)) by omega; rewrite H; clear H;
      pose proof (nextLe (t1 + td) c) as sth.
      omega.
    Qed.

    Lemma reqImpGt t: match getTrans getTransNext t with
                        | Req c => S (next (getTransState getTransNext t) c) =
                                   next (getTransState getTransNext (S t)) c /\
                                   forall c', c' <> c ->
                                              next (getTransState getTransNext t ) c' =
                                              next (getTransState getTransNext (S t)) c'
                        | Idle => forall c, next (getTransState getTransNext t ) c =
                                            next (getTransState getTransNext (S t)) c
                      end.
    Proof.
      unfold getTransState.
      unfold getTransList; fold (getTransList getTransNext t); simpl.
      destruct (getTrans getTransNext t).
      simpl.
      destruct (decTree c c).
      constructor. omega.
      intros c' c'_neq.
      destruct (decTree c' c); intuition.
      intuition.
      intuition.
    Qed.

    Theorem uniqAtomLabels:
      forall t1 t2,
        match getTrans getTransNext t1, getTrans getTransNext t2 with
          | Req c1, Req c2 =>
            c1 = c2 ->
            next (getTransState getTransNext t1) c1 =
            next (getTransState getTransNext t2) c2 ->
            t1 = t2
          | _, _ => True
        end.
    Proof.
      intros t1 t2.
      pose proof (reqImpGt t1) as sth1.
      pose proof (reqImpGt t2) as sth2.
      destruct (getTrans getTransNext t1).
      destruct (getTrans getTransNext t2).
      intros c_eq n_eq.
      rewrite <- c_eq in *.
      assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.

      destruct sth1 as [u1 _];
        destruct sth2 as [u2 _].
      destruct opts as [eq | [lt | gt]].
      assumption.

      Ltac finish c cond :=
        pose proof (nextStarLe c cond) as use;
        omega.
      finish c lt.
      finish c gt.

      intuition.
      intuition.
    Qed.

    Theorem localAtomOrdering:
      forall t1 t2, match getTrans getTransNext t1, getTrans getTransNext t2 with
                      | Req c1, Req c2 =>
                        c1 = c2 ->
                        next (getTransState getTransNext t1) c1 <
                        next (getTransState getTransNext t2) c2 ->
                        t1 < t2
                      | _, _ => True
                    end.
    Proof.
      intros t1 t2.
      pose proof (reqImpGt t1) as sth1.
      pose proof (reqImpGt t2) as sth2.
      destruct (getTrans getTransNext t1).
      destruct (getTrans getTransNext t2).
      intros c_eq n_lt.
      rewrite <- c_eq in *.
      destruct sth1 as [u1 _]; destruct sth2 as [u2 _].
      assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.
      destruct opts as [eq | [lt | gt]].
      rewrite eq in *; assert False by omega; intuition.
      intuition.
      pose proof (nextStarLe c gt) as use;
        assert False by omega; intuition.

      intuition.
      intuition.
    Qed.

    Theorem allAtomPrev t c i:
      next (getTransState getTransNext t) c > i ->
      exists t', t' < t /\ match getTrans getTransNext t' with
                             | Req c' => c = c' /\ next (getTransState getTransNext t') c' = i
                             | Idle => False
                           end.
    Proof.
      intros gt.
      induction t.
      simpl in gt.
      assert False by omega; intuition.
      pose proof (nextLe t c) as sth.
      assert (opts: next (getTransState getTransNext (S t)) c =
                    next (getTransState getTransNext t) c \/
                    next (getTransState getTransNext (S t)) c >
                    next (getTransState getTransNext t) c) by omega.
      destruct opts as [e|n].
      rewrite e in gt; destruct (IHt gt) as [t' [cond rest]]; exists t'; constructor;
      [ omega | intuition].
      assert (opts: next (getTransState getTransNext t) c = i \/
                    next (getTransState getTransNext t) c > i \/
                    next (getTransState getTransNext t) c < i) by omega.
      destruct opts as [eq | [lt | gtt]].
      exists t; constructor.
      omega. 
      pose proof (reqImpGt t) as sth2.
      destruct (getTrans getTransNext t).
      destruct sth2 as [u1 u2].
      destruct (decTree c c0).
      rewrite e in *; intuition.
      specialize (u2 c n0).
      assert False by omega; intuition.
      specialize (sth2 c);
      assert False by omega; intuition.

      destruct (IHt lt) as [t' cond].
      exists t'; constructor; [omega | intuition].

      pose proof (reqImpGt t) as sth2.
      destruct (getTrans getTransNext t).
      destruct sth2 as [u1 u2].
      specialize (u2 c).
      destruct (decTree c c0).
      rewrite <- e in *.
      assert False by omega; intuition.
      specialize (u2 n0); assert False by omega; intuition.
      specialize (sth2 c); assert False by omega; intuition.
    Qed.

    Definition noCurrAtomStore t a :=
      match getTrans getTransNext t with
        | Req c' =>
          let (a', descQ', dtQ') :=
              reqFn c' (next (getTransState getTransNext t) c') in
          a' = a -> descQ' = St -> False
        | _ => True
      end.

    Definition noAtomStore tl t a :=
      forall t', tl <= t' < t -> noCurrAtomStore t' a.

    Definition matchAtomStore cm tm t a :=
      let (am, descQm, dtQm) :=
          reqFn cm (next (getTransState getTransNext tm) cm) in
      mem (getTransState getTransNext t) a = dtQm /\
      am = a /\ descQm = St.

    Definition lastMatchAtomStore tm t a :=
      match getTrans getTransNext tm with
        | Req cm => matchAtomStore cm tm t a /\
                    noAtomStore (S tm) t a
        | _ => False
      end.

    Definition latestAtomValue t a :=
        (mem (getTransState getTransNext t) a = initData a /\
         noAtomStore 0 t a) \/
        (exists tm,
           tm < t /\ lastMatchAtomStore tm t a).

    Definition atomNoPrevNonSt t a :=
      noAtomStore 0 t a /\
      mem (getTransState getTransNext (S t)) a = initData a /\
      noCurrAtomStore t a.

    Definition atomPrevNonSt t a :=
      (exists tm,
         tm < t /\
         match getTrans getTransNext tm with
           | Req cm => matchAtomStore cm tm (S t) a /\
                       noAtomStore (S tm) t a
           | _ => False
         end) /\
      noCurrAtomStore t a.

    Definition atomSt t a :=
      lastMatchAtomStore t (S t) a.

    Lemma latestAtomInd t a (now: atomNoPrevNonSt t a \/ atomPrevNonSt t a \/ atomSt t a):
      latestAtomValue (S t) a.
    Proof.
      unfold latestAtomValue.
      destruct now as [noPrevNonSt | [prevNonSt | st]].

      Case "noPrevNonSt".
      unfold atomNoPrevNonSt in *.
      left.
      constructor.
      intuition.
      unfold noAtomStore in *.
      intros t' cond.
      assert (opts: 0 <= t' < t \/ t' = t) by omega.
      destruct opts as [done | eq]; [| rewrite eq]; intuition.

      Case "prevNonSt".
      right.
      unfold atomPrevNonSt in *.
      destruct prevNonSt as [[tm [cond lm]] noCurr].
      exists tm.
      constructor.
      omega.
      unfold lastMatchAtomStore in *.
      destruct (getTrans getTransNext tm).
      constructor.
      intuition.
      unfold noAtomStore.
      intros t' cond2.
      assert (opts: S tm <= t' < t \/ t' = t) by omega.
      destruct opts as [ez|ez2].
      intuition.
      rewrite ez2 in *; intuition.
      intuition.

      Case "st".
      right.
      unfold atomSt in st.
      exists t.
      constructor.
      omega.
      intuition.
    Qed.

    Lemma latestAtomValueHolds t a: latestAtomValue t a.
    Proof.
      induction t.

      Case "0".
      left; constructor; [| intros t' contra; assert False by omega]; intuition.

      Case "S t".
      apply latestAtomInd.

      unfold latestAtomValue in IHt.
      unfold lastMatchAtomStore in IHt.
      unfold atomNoPrevNonSt.
      unfold noCurrAtomStore.
      unfold atomPrevNonSt.
      unfold matchAtomStore in *.
      unfold noCurrAtomStore.

      unfold atomSt.
      unfold lastMatchAtomStore.
      unfold matchAtomStore.
      unfold noAtomStore.

      unfold getTransState at 1 3 in IHt.
      unfold getTransState at 1 2 4 5 6 7.
      unfold getTrans at 1 3 4.
      unfold getTransList; 
        fold (getTransList getTransNext t); simpl.
      destruct (trans (getTransNext (lTrans (getTransList getTransNext t))));
        simpl in *.

      SCase "Req".
      destruct (reqFn c (next (lSt (getTransList getTransNext t)) c)); simpl.
      destruct desc.

      SSCase "Ld".
      destruct IHt.

      SSSCase "NoPrev".
      left.
      intuition.
      discriminate.

      SSSCase "Prev".
      right; left.
      destruct (reqFn c (next (lSt (getTransList getTransNext t)) c)).
      intuition.
      discriminate.

      SSCase "St".
      destruct (decAddr a loc).

      SSSCase "addr match".
      right; right.
      constructor.
      auto.
      intros t' contra.
      assert False by omega; intuition.

      SSSCase "addr no match".
      destruct IHt; intuition.

      SCase "Idle".
      destruct IHt; intuition.
    Qed.


    Theorem storeAtomicityAtom:
      forall t,
        match getTrans getTransNext t with
          | Req c =>
            let (a, descQ, dtQ) := reqFn c (next (getTransState getTransNext t) c) in
            match descQ with
              | Ld => latestAtomValue t a
              | St => True 
            end
          | _ => True
        end.
    Proof.
      intros t.
      pose proof (latestAtomValueHolds t).
      destruct (getTrans getTransNext t).
      destruct (reqFn c (next (getTransState getTransNext t) c)) as [a desc _].
      destruct desc.
      apply latestAtomValueHolds.
      intuition.
      intuition.
    Qed.
  End SomeList.

  Definition atomicResp s s' (t: AtomicTrans s s') :=
    match t with
      | Req c => Some (Build_Resp c (next s c)
                                  match desc (reqFn c (next s c)) with
                                    | Ld => (mem s (loc (reqFn c (next s c))))
                                    | St => initData zero
                                  end)
      | Idle => None
    end.

  Definition AtomicList := TransList AtomicTrans (Build_State initData (fun t => 0)).

  Definition nextAtomicTrans n s (al: AtomicList n s) :=
    match respFn n with
      | Some r => Build_NextTrans _ _ _ (Req s (procR r))
      | None => Build_NextTrans _ _ _ (Idle s)
    end.

  About getTrans.

  Theorem obeysP: forall n,
                    respFn n = atomicResp (getTrans nextAtomicTrans n).
  Proof.
    apply strong_ind.
    intros t prevEq.
    unfold atomicResp.
    pose proof (@uniqRespLabels t) as uniq.
    pose proof (@allPrevious t) as allPrev.
    pose proof (@localOrdering t) as lo.
    unfold getTrans.
    unfold nextAtomicTrans at 2.
    pose proof (@uniqAtomLabels nextAtomicTrans t) as uniq2.
    unfold getTrans in uniq2.
    unfold nextAtomicTrans at 2 in uniq2.

    destruct (respFn t); simpl.

    Case "respFn is Some".
    destruct r; simpl in *.
    unfold Index in *.
    assert (opts: idx < next (lSt (getTransList nextAtomicTrans t)) procR \/
                  idx > next (lSt (getTransList nextAtomicTrans t)) procR \/
                  idx = next (lSt (getTransList nextAtomicTrans t)) procR) by omega.
    destruct opts.

    SCase "idx < next".
    pose proof (allAtomPrev nextAtomicTrans _ _ H) as [t' [t'_lt_t rest]].
    specialize (prevEq _ t'_lt_t).
    unfold atomicResp in prevEq.
    destruct (getTrans nextAtomicTrans t').

    SSCase "t'_idx is Req".
    specialize (uniq t').
    destruct (respFn t').

    SSSCase "respFn(t') is Some".
    destruct r.
    injection prevEq as _ idxEq pEq.
    rewrite pEq in *; rewrite idxEq in *.
    destruct rest as [u1 u2].
    assert (u3: idx = next (lSt (getTransList nextAtomicTrans t')) c) by auto.
    specialize (uniq u1 u3).
    omega.

    SSSCase "respFn(t') is None".
    discriminate.

    SSCase "t'_idx is None".
    intuition.

    destruct H.

    SCase "idx  > next".
    clear uniq.
    specialize (allPrev _ H).
    destruct allPrev as [t' respT'].
    specialize (lo t').
    specialize (prevEq t').
    specialize (uniq2 t').
    unfold nextAtomicTrans at 2 in uniq2.
    destruct (respFn t').

    SSCase "respFn t' is Some".
    destruct r.
    simpl in *.
    destruct respT' as [u1 u2].
    assert (L: procR = procR0) by auto;
      rewrite <- u2 in H;
      specialize (lo L H).
    specialize (prevEq lo).
    unfold atomicResp at 1 in prevEq.
    destruct (getTrans nextAtomicTrans t').

    SSSCase "atom t' is Req".
    injection prevEq as _ idEq pEq.
    rewrite u2 in idEq.
    rewrite <- pEq in idEq.
    specialize (uniq2 L idEq).
    assert False by omega; intuition.

    SSSCase "atom t' is None".
    discriminate.

    SSCase "respFn t' is None".
    intuition.

    SCase "idx = next".
    rewrite H in *.
    f_equal.
    f_equal.
    clear uniq idx allPrev lo uniq2 H.
    admit.

    Case "reqFn None".
    intuition.
  Qed.

  Definition getAtomicResp n := atomicResp (getTrans (@nextAtomicTrans) n).

  Theorem respEq n: respFn n = getAtomicResp n.
  Proof.
    apply (obeysP n).
  Qed.

  Print Assumptions respEq.
End Bisum.
