Require Import DataTypes Omega Coq.Logic.Classical MsiState.

Module Type L1Axioms (dt: DataTypes).
  Import dt.
  Axiom deqOrNot: forall t, {x| deqR (fst x) (snd x) t} + {forall c i, ~ deqR c i t}.
  Axiom deqLeaf: forall {c i t}, deqR c i t -> leaf c.
  Axiom deqDef: forall {c i t}, deqR c i t -> defined c.
  Axiom uniqDeqProc: forall {c i1 t i2},
                       deqR c i1 t -> deqR c i2 t ->
                       i1 = i2.
  Axiom uniqDeqProc2: forall {c i t1 t2},
                        deqR c i t1 -> deqR c i t2 -> t1 = t2.
  Axiom uniqDeqProc3: forall {c1 i1 t c2 i2},
                       deqR c1 i1 t -> deqR c2 i2 t ->
                       c1 = c2 /\ i1 = i2.
  Axiom deqOrder: forall {c i1 t1 i2 t2},
                    deqR c i1 t1 -> deqR c i2 t2 ->
                    i1 < i2 -> ~ t1 > t2.
  Axiom processDeq: forall {c i t}, deqR c i t -> let q := reqFn c i in
                                          match desc q with
                                            | Ld => sle Sh (state c (loc q) t)
                                            | St => state c (loc q) t = Mo
                                          end.
  Parameter deqImpDeqBefore: forall {c i1 i2 t},
                               deqR c i1 t -> i2 < i1 -> exists t', t' < t /\ deqR c i2 t'.
End L1Axioms.

Module Type L1Theorems (dt: DataTypes) (l1A: L1Axioms dt).
  Import dt l1A.
  Parameter latestValue:
  forall {c a t},
    defined c ->
    leaf c ->
    sle Sh (state c a t) ->
    (data c a t = initData a /\
     forall {ti}, 0 <= ti < t -> forall {ci ii},
                                   defined ci ->
                                   ~ (deqR ci ii ti /\ loc (reqFn ci ii) = a /\
                                      desc (reqFn ci ii) = St)) \/
    (exists cb ib tb, defined cb /\ tb < t /\ deqR cb ib tb /\ desc (reqFn cb ib) = St /\
                      loc (reqFn cb ib) = a /\
                      data c a t = dataQ (reqFn cb ib) /\
                      forall {ti}, tb < ti < t ->
                                   forall {ci ii},
                                     defined ci ->
                                     ~ (deqR ci ii ti /\ loc (reqFn ci ii) = a /\
                                        desc (reqFn ci ii) = St)
    ).

  Parameter uniqM:
  forall {c a t}, defined c -> leaf c ->
    state c a t = Mo -> forall {co}, defined co -> leaf co -> c <> co -> state co a t = In.

  Parameter deqOrNot: forall t, {x| deqR (fst x) (snd x) t} + {forall c i, ~ deqR c i t}.

End L1Theorems.
