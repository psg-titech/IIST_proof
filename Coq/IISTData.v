Require Import IIST.EqOneDec.
Require Import IIST.PartInvFun.

Open Scope part_inv_fun_scope.



Inductive IIST : Type -> Type -> Type :=
| IIST_mapfold : forall {A X Y : Type},
   A -> (A -> X <~~> Y) -> (A -> X -> A) -> IIST X Y
| IIST_delay : forall {X : Type} (x : X) `{e : EqOneDec X x}, IIST X X
| IIST_hasten : forall {X : Type} (x : X) `{e : EqOneDec X x}, IIST X X
| IIST_seqcomp : forall {X Y Z : Type}, IIST X Y -> IIST Y Z -> IIST X Z
| IIST_parcomp : forall {X1 X2 Y1 Y2 : Type}, IIST X1 Y1 -> IIST X2 Y2 -> IIST (X1 * X2) (Y1 * Y2)
.


Fixpoint delay_fwd {X Y : Type} (e : IIST X Y) : nat :=
match e with
| IIST_mapfold _ _ _ => 0
| IIST_delay _ => 0
| IIST_hasten _ => 1
| IIST_seqcomp xz zy => delay_fwd xz + delay_fwd zy
| IIST_parcomp xy1 xy2 => max (delay_fwd xy1) (delay_fwd xy2)
end.

Fixpoint delay_bwd {X Y : Type} (e : IIST X Y) : nat :=
match e with
| IIST_mapfold _ _ _ => 0
| IIST_delay _ => 1
| IIST_hasten _ => 0
| IIST_seqcomp xz zy => delay_bwd xz + delay_bwd zy
| IIST_parcomp xy1 xy2 => max (delay_bwd xy1) (delay_bwd xy2)
end.

