Set Implicit Arguments.

Require Import CpdtTactics.
Require Import Arith.

Section Fifo.
Variable A : Set.

Inductive Fifo : nat -> Set :=
| null : Fifo 0
| store : A -> forall n, Fifo n -> Fifo (S n).

Definition s_n_0 n (pf : S n = 0) : False :=
  match pf in (_ = e) return match e with
                             | 0 => False
                             | S _ => True
                             end with
  | eq_refl => I
  end.

Fixpoint first' n (f : Fifo n) : forall m, S m = n -> A :=
  match f in Fifo n0 return forall m, S m = n0 -> A with
  | null => fun _ pf0 => match s_n_0 pf0 with end
  | store x _ f1 => fun _ _ => match f1 in (Fifo n2) return (forall m, S m = n2 -> A) -> A with
                               | null => fun _ => x
                               | store _ n3 _ => fun val_pf => val_pf n3 eq_refl
                               end (first' f1)
  end.

Fixpoint deq' n (f : Fifo n) : forall m, S m = n -> Fifo (pred n) :=
  match f in Fifo n0 return forall m, S m = n0 -> Fifo (pred n0) with
  | null => fun _ pf0 => match s_n_0 pf0 with end
  | store x _ f1 => fun _ _ => match f1 in (Fifo n2) return (forall m, S m = n2 -> Fifo (pred n2)) -> Fifo n2 with
                               | null => fun _ => null
                               | store _ n3 _ => fun val_pf => store x (val_pf n3 eq_refl)
                               end (deq' f1)
  end.

Variable size : nat.

Record fifo := mkfifo
{ num : nat
; obj : Fifo num
; bound : num <= size
}.

Lemma le_pred_le n m : n <= m -> pred n <= m.
  crush.
Qed.

Lemma lt_S_le n m : n < m -> S n <= m.
  crush.
Qed.

Lemma lt_pred_lt n m : n < m -> pred n < m.
  crush.
Qed.

Lemma O_le n : 0 <= n.
  crush.
Qed.

Definition emptyFifo :=
  {| num := 0
   ; obj := null
   ; bound := O_le size
   |}.

Definition enq x (f : fifo) (pf : num f < size) : fifo :=
  {| num := S (num f)
   ; obj := store x (obj f)
   ; bound := lt_S_le pf
   |}.

Definition first (f : fifo) : forall m, S m = num f -> A := first' (obj f).

Definition deq (f : fifo) m (pf : S m = num f) : fifo :=
  {| num := pred (num f)
   ; obj := deq' (obj f) pf
   ; bound :=  le_pred_le (bound f)
   |}.

End Fifo.
