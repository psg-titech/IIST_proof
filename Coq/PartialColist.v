Require Import IIST.EqOneDec.
Require Import IIST.OptionBind.
Require Import IIST.PartInvFun.


CoInductive PartialColist (A : Type) : Type :=
| cnil : PartialColist A
| ccons : A -> PartialColist A -> PartialColist A
| cfail : PartialColist A.


Arguments cnil {A}.
Arguments ccons {A} a l.
Arguments cfail {A}.

Declare Scope part_colist_scope.

Bind Scope part_colist_scope with PartialColist.

Infix "::" := ccons (at level 60, right associativity) : part_colist_scope.

Notation "[ ]" := cnil (format "[ ]") : part_colist_scope.
Notation "[ x ]" := (ccons x cnil) : part_colist_scope.
Notation "[ x ; y ; .. ; z ]" := (ccons x (ccons y .. (ccons z cnil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : part_colist_scope.

Notation "-*-" := cfail (format "-*-") : part_colist_scope.


Open Scope part_colist_scope.


(* http://adam.chlipala.net/cpdt/html/Coinductive.html にあるtrick *)
Definition colist_frob {A : Type} (l : PartialColist A) : PartialColist A :=
 match l with
 | [] => []
 | a :: l => a :: l
 | -*- => -*-
 end.

Theorem colist_frob_eq :
 forall {A : Type} (l : PartialColist A),
  l = colist_frob l.
intros A l; destruct l; simpl; now auto.
Qed.




(* 使う？ *)
CoFixpoint coapp {A : Type} (l m : PartialColist A) : PartialColist A :=
 match l with
 | [] => m
 | a :: l => a :: coapp l m
 | -*- => -*-
 end.

Infix "++" := coapp (right associativity, at level 60) : part_colist_scope.


CoFixpoint coslide {A : Type} (a : A) (l : PartialColist A) : PartialColist A :=
 match l with
 | [] => []
 | x :: l => a :: coslide x l
 | -*- => -*-
 end.




CoInductive coprefix {A : Type} : PartialColist A -> PartialColist A -> Prop :=
| copre_nil : forall l, coprefix [] l
| copre_cons : forall a l1 l2, coprefix l1 l2 -> coprefix (a :: l1) (a :: l2)
| copre_fail : coprefix -*- -*-.


Theorem coprefix_reflexive :
 forall A (l : PartialColist A), coprefix l l.
intro A.
cofix f.
intro l; destruct l as [ | a l | ]; constructor.
now auto.
Qed.


Theorem coprefix_transitive :
 forall A (l1 l2 l3 : PartialColist A),
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


Theorem coprefix_slide :
 forall {A : Type} (a : A) l1 l2,
  coprefix l1 l2 -> coprefix (coslide a l1) (coslide a l2).
intro A; cofix cf.
intros a l1 l2 Hpre.
rewrite colist_frob_eq with (coslide a l1).
rewrite colist_frob_eq with (coslide a l2).
inversion Hpre; subst; simpl; constructor.
apply cf; now auto.
Qed.




CoFixpoint cozip {A B : Type} (la : PartialColist A) (lb : PartialColist B) : PartialColist (A*B) :=
 match la, lb with
 | [], _ | _, [] => []
 | -*-, _ | _, -*- => -*-
 | a :: la, b :: lb => (a, b) :: cozip la lb
 end.



CoFixpoint coleft {A B : Type} (lab : PartialColist (A * B)) : PartialColist A :=
 match lab with
 | [] => []
 | (a, _) :: lab => a :: coleft lab
 | -*- => -*-
 end.


CoFixpoint coright {A B : Type} (lab : PartialColist (A * B)) : PartialColist B :=
 match lab with
 | [] => []
 | (_, b) :: lab => b :: coright lab
 | -*- => -*-
 end.



CoInductive n_list_status : Set :=
| le_n | fail_n | more_n.

Fixpoint n_look_ahead {A : Type} (n : nat) (l : PartialColist A) : n_list_status :=
 match n, l with
 | _, [] => le_n
 | O, _ => more_n
 | S n, -*- => fail_n
 | S n, _ :: l => n_look_ahead n l
 end.

CoFixpoint drop_tl_n {A : Type} (n : nat) (l : PartialColist A) : PartialColist A :=
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


Definition optionPCbind {A B : Type} (sa : option A) (f : A -> PartialColist B) : PartialColist B :=
 match sa with
 | Some a => f a
 | None => -*-
 end.



CoFixpoint cofwd_mapfold {A X Y : Type} (f : A -> X <~~> Y) (g : A -> X -> A) (a : A)
                                    (xs : PartialColist X) : PartialColist Y :=
 match xs with
 | [] => []
 | x :: xs =>
    optionPCbind ((forward _ _ (f a)) x) (fun y => y :: cofwd_mapfold f g (g a x) xs)
 | -*- => -*-
end.



Fixpoint cofwd {X Y : Type} (e : IIST X Y) : PartialColist X -> PartialColist Y :=
 match e with
 | IIST_mapfold a f g => cofwd_mapfold f g a
 | IIST_delay x => coslide x
 | IIST_hasten x => fun xs =>
    match xs with
    | [] => []
    | x' :: xs => if equiv_one_dec x' then xs else -*-
    | -*- => -*-
    end
 | IIST_seqcomp xz zy => fun xs => cofwd zy (cofwd xz xs)
 | IIST_parcomp xy1 xy2 => fun x12s =>
    cozip (drop_tl_n (delay_fwd xy2 - delay_fwd xy1) (cofwd xy1 (coleft  x12s)))
          (drop_tl_n (delay_fwd xy1 - delay_fwd xy2) (cofwd xy2 (coright x12s)))
 end.
(* 長さのずれをまとめる際に失敗を先んじて持ってくることで入力のタイミングに合わせて全体が失敗する *)
(* 証明できるわけなくない？ *)



CoFixpoint cobwd_mapfold {A X Y : Type} (f : A -> X <~~> Y) (g : A -> X -> A) (a : A)
                                    (ys : PartialColist Y) : PartialColist X :=
 match ys with
 | [] => []
 | y :: ys' =>
    optionPCbind ((backward _ _ (f a)) y) (fun x => x :: cobwd_mapfold f g (g a x) ys')
 | -*- => -*-
 end.


Fixpoint cobwd {X Y : Type} (e : IIST X Y) : PartialColist Y -> PartialColist X :=
 match e with
 | IIST_mapfold a f g => cobwd_mapfold f g a
 | IIST_delay x => fun ys =>
    match ys with
    | [] => []
    | y' :: ys => if equiv_one_dec y' then ys else -*-
    | -*- => -*-
    end
 | IIST_hasten x => coslide x
 | IIST_seqcomp xz zy => fun ys => cobwd xz (cobwd zy ys)
 | IIST_parcomp xy1 xy2 => fun y12s =>
    cozip (drop_tl_n (delay_bwd xy2 - delay_bwd xy1) (cobwd xy1 (coleft  y12s)))
          (drop_tl_n (delay_bwd xy1 - delay_bwd xy2) (cobwd xy2 (coright y12s)))
 end.


Lemma cofwd_prefix : forall {X Y : Type} (e : IIST X Y) (xs xs' : PartialColist X),
  coprefix xs' xs -> coprefix (cofwd e xs') (cofwd e xs).
intros X Y e.
induction e as [A X Y a f g | X x e' | X x e' | X Y Z exy IHexy eyz IHeyz | X1 X2 Y1 Y2 e1 IHe1 e2 IHe2]; simpl.
+ revert a.
  cofix mf.
  intros a xs xs' Hpre.
  rewrite colist_frob_eq with (cofwd_mapfold f g a xs').
  rewrite colist_frob_eq with (cofwd_mapfold f g a xs).
  inversion Hpre; subst; simpl.
  - now constructor.
  - destruct (forward X Y (f a) a0); simpl; constructor.
    apply mf; now auto.
  - now constructor.
+ intros ? ?; now apply coprefix_slide.
+ intros xs xs' Hpre.
  inversion Hpre; subst; simpl; try constructor.
  destruct equiv_one_dec with a.
  - now auto.
  - now constructor.
+ now eauto.
+ admit.
Admitted.