Require Import Arith.
Set Implicit Arguments.

Section NamedTrans.
  Variable State: Set.
  Variable (Trans: State -> State -> Set).
  Variable (init: State).
  Variable (P: nat -> forall s s', Trans s s' -> Prop).

  Inductive TransList: nat -> State -> Set :=
    | TransInit: TransList 0 init
    | TransNext:
        forall n s,
          TransList n s ->
          forall s' (t: Trans s s'),
            P n t ->
            TransList (S n) s'.

  Record NextTrans n s : Set := { nextTransSt: State;
                                  nextTrans: Trans s nextTransSt;
                                  nextTransProp: P n nextTrans}.

  Variable (getTransNext: forall n s, TransList n s -> @NextTrans n s).

  Record NextTransList n : Set := { nextTransListSt: State;
                                    nextTransListTrans: TransList n nextTransListSt}.

  Fixpoint getTransList n :=
    match n as n0 return @NextTransList n0 with
      | 0 => Build_NextTransList TransInit
      | S k =>
        let ls := nextTransListTrans (getTransList k) in
        let t := getTransNext ls in
        Build_NextTransList (TransNext ls (nextTransProp t))
    end.

  Definition getTransState n := nextTransListSt (getTransList n).

  Definition getTrans n :=
    nextTrans (getTransNext (nextTransListTrans (getTransList n))).

  Definition obeysP n :=
    nextTransProp (getTransNext (nextTransListTrans (getTransList n))).

  Theorem getInit: getTransState 0 = init.
  Proof.
    reflexivity.
  Qed.
End NamedTrans.
