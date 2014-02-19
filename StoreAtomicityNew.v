Require Import DataTypes.

Module Type StoreAtomicity (dt: DataTypes).
  Import dt.

  Record Resp := { proc: Cache;
                   idx: Index;
                   datum: Data
                 }.

  Parameter respFn: Time -> option Resp.

  Axiom uniqRespLabels:
    forall {t1 t2}, match respFn t1, respFn t2 with
                      | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                        c1 = c2 -> i1 = i2 -> t1 = t2
                      | _, _ => True
                    end.

  Axiom localOrdering:
    forall {t1 t2}, match respFn t1, respFn t2 with
                      | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                        c1 = c2 -> i1 < i2 -> t1 < t2
                      | _, _ => True
                    end.

  Axiom allPrevious:
    forall {t2}, match respFn t2 with
                   | Some (Build_Resp c2 i2 _) =>
                     forall {i1}, i1 < i2 -> exists t1, match respFn t1 with
                                                          | Some (Build_Resp c1 i _) =>
                                                            c1 = c2 /\ i = i1
                                                          | None => False
                                                        end
                   | _ => True
                 end.

  Axiom storeAtomicity:
    forall {t},
      match respFn t with
        | Some (Build_Resp c i d) =>
          let (a, descQ, dtQ) := reqFn c i in
          match descQ with
            | Ld =>
              (d = initData a /\
               forall t', t' < t ->
                          match respFn t' with
                            | Some (Build_Resp c' i' d') =>
                              let (a', descQ', dtQ') := reqFn c' i' in
                              a' = a -> descQ' = St -> False
                            | _ => True
                          end) \/
              (exists tm,
                 tm < t /\
                 match respFn tm with
                   | Some (Build_Resp cm im dm) =>
                     let (am, descQm, dtQm) := reqFn cm im in
                     d = dtQm /\ am = a /\ descQm = St /\
                     forall t', tm < t' < t ->
                                match respFn t' with
                                  | Some (Build_Resp c' i' d') =>
                                    let (a', descQ', dtQ') := reqFn c' i' in
                                    a' = a -> descQ' = St -> False
                                  | _ => True
                                end
                   | _ => False
                 end)
            | St => d = initData zero 
          end
        | _ => True
      end.
End StoreAtomicity.