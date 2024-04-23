Require Import IIST.EqOneDec.
Require Import IIST.OptionBind.
Require Import IIST.PartInvFun.


CoInductive PartColist (A : Type) : Type :=
| cnil : PartColist A
| ccons : A -> PartColist A -> PartColist A
| cfail : PartColist A.


Arguments cnil {A}.
Arguments ccons {A} a l.
Arguments cfail {A}.

Declare Scope part_colist_scope.

Bind Scope part_colist_scope with PartColist.

Infix "::" := ccons (at level 60, right associativity) : part_colist_scope.

Notation "[ ]" := cnil (format "[ ]") : part_colist_scope.
Notation "[ x ]" := (ccons x cnil) : part_colist_scope.
Notation "[ x ; y ; .. ; z ]" := (ccons x (ccons y .. (ccons z cnil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : part_colist_scope.

Notation "-*-" := cfail (format "-*-") : part_colist_scope.


Open Scope part_colist_scope.


(* 使う？ *)
CoFixpoint coapp {A : Type} (l m : PartColist A) : PartColist A :=
 match l with
 | [] => m
 | a :: l => a :: coapp l m
 | -*- => -*-
 end.

Infix "++" := coapp (right associativity, at level 60) : part_colist_scope.


CoFixpoint coslide {A : Type} (a : A) (l : PartColist A) : PartColist A :=
 match l with
 | [] => []
 | x :: l => a :: coslide x l
 | -*- => -*-
 end.




CoInductive coprefix {A : Type} : PartColist A -> PartColist A -> Prop :=
| copre_nil : forall l, coprefix [] l
| copre_cons : forall a l1 l2, coprefix l1 l2 -> coprefix (a :: l1) (a :: l2)
| copre_fail : coprefix -*- -*-.


Theorem coprefix_reflexive :
 forall A (l : PartColist A), coprefix l l.
intro A.
cofix f.
intro l; destruct l as [ | a l | ]; constructor.
now auto.
Qed.


Theorem coprefix_transitive :
 forall A (l1 l2 l3 : PartColist A),
  coprefix l1 l2 -> coprefix l2 l3 -> coprefix l1 l3.
intro A.
cofix f.
intros l1 l2 l3 H12 H23.
inversion H12; subst.
+ now constructor.
+ inversion H23; subst.
  constructor; now eauto.
+ inversion H23; now constructor.
Qed.





CoFixpoint cozip {A B : Type} (la : PartColist A) (lb : PartColist B) : PartColist (A*B) :=
 match la, lb with
 | [], _ | _, [] => []
 | -*-, _ | _, -*- => -*-
 | a :: la, b :: lb => (a, b) :: cozip la lb
 end.



CoFixpoint coleft {A B : Type} (lab : PartColist (A * B)) : PartColist A :=
 match lab with
 | [] => []
 | (a, _) :: lab => a :: coleft lab
 | -*- => -*-
 end.


CoFixpoint coright {A B : Type} (lab : PartColist (A * B)) : PartColist B :=
 match lab with
 | [] => []
 | (_, b) :: lab => b :: coright lab
 | -*- => -*-
 end.



CoInductive n_list_status : Set :=
| le_n | fail_n | more_n.

Fixpoint n_look_ahead {A : Type} (n : nat) (l : PartColist A) : n_list_status :=
 match n, l with
 | _, [] => le_n
 | O, _ => more_n
 | S n, -*- => fail_n
 | S n, _ :: l => n_look_ahead n l
 end.

CoFixpoint drop_tl_n {A : Type} (n : nat) (l : PartColist A) : PartColist A :=
 match n_look_ahead n l with
 | le_n => []
 | fail_n => -*-
 | more_n =>
   match l with
   | [] | -*- => l
   | a :: l => a :: drop_tl_n n l
   end
 end.




Open Scope part_inv_fun_scope.

Require Import IIST.IISTData.


Definition optionPCbind {A B : Type} (sa : option A) (f : A -> PartColist B) : PartColist B :=
 match sa with
 | Some a => f a
 | None => -*-
 end.



CoFixpoint fwd_mapfold {A X Y : Type} (f : A -> X <~~> Y) (g : A -> X -> A) (a : A)
                                    (xs : PartColist X) : PartColist Y :=
 match xs with
 | [] => []
 | x :: xs =>
    optionPCbind ((forward _ _ (f a)) x) (fun y => y :: fwd_mapfold f g (g a x) xs)
 | -*- => -*-
end.


Fixpoint fwd {X Y : Type} (e : IIST X Y) : PartColist X -> PartColist Y :=
 match e with
 | IIST_mapfold a f g => fwd_mapfold f g a
 | IIST_delay x => coslide x
 | IIST_hasten x => fun xs =>
    match xs with
    | [] => []
    | x' :: xs => if equiv_one_dec x' then xs else -*-
    | -*- => -*-
    end
 | IIST_seqcomp xz zy => fun xs => (fwd zy (fwd xz xs))
 | IIST_parcomp xy1 xy2 => fun x12s =>
    cozip (drop_tl_n (delay_fwd xy2 - delay_fwd xy1) (fwd xy1 (coleft  x12s)))
          (drop_tl_n (delay_fwd xy1 - delay_fwd xy2) (fwd xy2 (coright x12s)))
 end.
(* 長さのずれをまとめる際に失敗を先んじて持ってくることで入力のタイミングに合わせて全体が失敗する *)
(* 証明できるわけなくない？ *)


