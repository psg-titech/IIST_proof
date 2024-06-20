Require Import IIST.EqOneDec.
Require Import IIST.OptionBind.
Require Import IIST.PartInvFun.



Require Import Lia.
Lemma max_minus_plus1 : forall m n, max m n = m - n + n.
lia.
Qed.

Lemma max_minus_plus2 : forall m n, max m n = n - m + m.
lia.
Qed.





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


Ltac cl_red e := rewrite colist_frob_eq with e.
Ltac cl_red_in e H := rewrite colist_frob_eq with e in H.


CoInductive colist_cong {A : Type} :
 PartialColist A -> PartialColist A -> Prop :=
| cong_cnil : colist_cong [] []
| cong_ccons : forall a l1 l2, colist_cong l1 l2 -> colist_cong (a :: l1) (a :: l2)
| cong_cfail : colist_cong -*- -*-.
(* cubical TT か HoTT ほしい... *)

Infix "~=~" := colist_cong (at level 70, no associativity).



Lemma colist_cong_reflexive :
 forall {A : Type} (l : PartialColist A),
  colist_cong l l.
intro A.
cofix cf.
intros [ | a l | ]; constructor.
now auto.
Qed.


Lemma colist_cong_symmetric :
 forall {A : Type} (l1 l2 : PartialColist A),
  colist_cong l1 l2 -> colist_cong l2 l1.
intro A.
cofix cf.
intros l1 l2 Hcong.
inversion Hcong; subst; constructor.
now auto.
Qed.


Lemma colist_cong_transitive :
 forall {A : Type} (l1 l2 l3 : PartialColist A),
  colist_cong l1 l2 -> colist_cong l2 l3 -> colist_cong l1 l3.
intro A.
cofix cf.
intros l1 l2 l3 Hcong12 Hcong23.
inversion Hcong12; subst; inversion Hcong23; subst; constructor.
now eauto.
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
cl_red (coslide a l1).
cl_red (coslide a l2).
inversion Hpre; subst; simpl; constructor.
apply cf; now auto.
Qed.




CoFixpoint cozip {A B : Type} (la : PartialColist A) (lb : PartialColist B) : PartialColist (A*B) :=
 match la, lb with
 | -*-, _ | _, -*- => -*-
 | [], _ | _, [] => []
 | a :: la, b :: lb => (a, b) :: cozip la lb
 end.


Theorem cozip_prefix :
 forall {A B : Type} (la1 la2 : PartialColist A)
                     (lb1 lb2 : PartialColist B),
  coprefix la1 la2
  -> coprefix lb1 lb2
  -> coprefix (cozip la1 lb1) (cozip la2 lb2).
intros A B.
cofix cf.
intros la1 la2 lb1 lb2 Hpre1 Hpre2.
cl_red (cozip la1 lb1).
cl_red (cozip la2 lb2).
inversion Hpre1; subst;
 inversion Hpre2; subst;
 simpl; try constructor.
+ destruct la2; simpl; now constructor.
+ now auto.
Qed.


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



Theorem coleft_prefix :
 forall {A B : Type} (l1 l2 : PartialColist (A * B)),
  coprefix l1 l2 -> coprefix (coleft l1) (coleft l2).
intros A B.
cofix cf.
intros l1 l2 Hpre.
cl_red (coleft l1).
cl_red (coleft l2).
inversion Hpre; subst; simpl; try constructor.
destruct a; simpl.
constructor.
now auto.
Qed.

Theorem coright_prefix :
 forall {A B : Type} (l1 l2 : PartialColist (A * B)),
  coprefix l1 l2 -> coprefix (coright l1) (coright l2).
intros A B.
cofix cf.
intros l1 l2 Hpre.
cl_red (coright l1).
cl_red (coright l2).
inversion Hpre; subst; simpl; try constructor.
destruct a; simpl.
constructor.
now auto.
Qed.



Lemma cozip_left_right_cong :
 forall {A B : Type} (l : PartialColist (A * B)),
  l ~=~ cozip (coleft l) (coright l).
intros A B.
cofix cf.
intro l.
cl_red (cozip (coleft l) (coright l)).
cl_red (coleft l).
cl_red (coright l).
destruct l as [ | [a b] l | ]; simpl; constructor.
now apply cf.
Qed.



CoInductive n_list_status : Set :=
| lt_n | fail_n | more_n.

Fixpoint n_look_ahead {A : Type} (n : nat) (l : PartialColist A) : n_list_status :=
 match n, l with
 | O, _ => more_n
 | _, [] => lt_n
 | S n, -*- => fail_n
 | S n, _ :: l => n_look_ahead n l
 end.

(* 自明なのでカット(場合分けは3種類しかないから前提なくてもそうなる) *)
(*
Lemma coprefix_n_look_ahead_le :
 forall {A : Type} (n : nat) (l1 l2 : PartialColist A),
  coprefix l1 l2
   -> n_look_ahead n l1 = le_n
   -> n_look_ahead n l2 = le_n
      \/ n_look_ahead n l2 = more_n
      \/ n_look_ahead n l2 = fail_n.
*)


Lemma coprefix_n_look_ahead_more :
 forall {A : Type} (n : nat) (l1 l2 : PartialColist A),
  coprefix l1 l2
   -> n_look_ahead n l1 = more_n
   -> n_look_ahead n l2 = more_n.
intros A n.
induction n as [ | n IHn]; intros l1 l2 Hpre Hl1;
 inversion Hpre; subst; simpl in *; auto.
+ discriminate.
+ now eauto.
Qed.


Lemma coprefix_n_look_ahead_fail :
 forall {A : Type} (n : nat) (l1 l2 : PartialColist A),
  coprefix l1 l2
   -> n_look_ahead n l1 = fail_n
   -> n_look_ahead n l2 = fail_n.
intros A n.
induction n as [ | n IHn]; intros l1 l2 Hpre Hl1;
 inversion Hpre; subst; simpl in *; auto.
+ discriminate.
+ now eauto.
Qed.


Lemma cong_n_look_ahead_eq :
 forall {A : Type} (n : nat) (l1 l2 : PartialColist A),
  l1 ~=~ l2 -> n_look_ahead n l1 = n_look_ahead n l2.
intros A n.
induction n as [ | n IHn]; intros l1 l2 Hcong; inversion Hcong; simpl; now auto.
Qed.





CoFixpoint drop_tl_n {A : Type} (n : nat) (l : PartialColist A) : PartialColist A :=
 match l with
 | [] | -*- => l
 | a :: l =>
   match n_look_ahead n l with
   | lt_n => []
   | fail_n => -*-
   | more_n => a :: drop_tl_n n l
   end
 end.


Lemma drop_prefix :
 forall {A : Type} (n : nat) (l1 l2 : PartialColist A),
  coprefix l1 l2 -> coprefix (drop_tl_n n l1) (drop_tl_n n l2).
intros A.
cofix cf.
intros n l1 l2 Hpre.
cl_red (drop_tl_n n l1).
cl_red (drop_tl_n n l2).
inversion Hpre; subst.
+ simpl.
  now constructor.
+ simpl.
  destruct (n_look_ahead n l0) eqn: Hn.
  - now constructor.
  - rewrite coprefix_n_look_ahead_fail with (l1 := l0); auto.
    now constructor.
  - rewrite coprefix_n_look_ahead_more with (l1 := l0); auto.
    constructor.
    now auto.
+ simpl.
  now constructor.
Qed.


Lemma drop_0_cong :
 forall {A : Type} (l : PartialColist A),
  drop_tl_n 0 l ~=~ l.
intro A.
cofix cf.
intro l.
cl_red (drop_tl_n 0 l).
destruct l as [ | a l | ]; simpl; constructor.
now auto.
Qed.


Lemma drop_n_cnil :
 forall {A : Type} (n : nat), @drop_tl_n A n [] = [].
intros A n.
cl_red (@drop_tl_n A n []).
simpl; now auto.
Qed.

Lemma drop_n_cfail :
 forall {A : Type} (n : nat), @drop_tl_n A n -*- = -*-.
intros A n.
cl_red (@drop_tl_n A n -*-).
simpl; now auto.
Qed.

Lemma drop_n_ccons :
 forall {A : Type} (n : nat) (a : A) l,
  drop_tl_n n (a :: l) = [] /\ n_look_ahead n l = lt_n
   \/ drop_tl_n n (a :: l) = a :: drop_tl_n n l /\ n_look_ahead n l = more_n
   \/ drop_tl_n n (a :: l) = -*- /\ n_look_ahead n l = fail_n.
intros A n a l.
cl_red (drop_tl_n n (a :: l)).
destruct n; simpl; auto.
destruct l; simpl; auto.
destruct (n_look_ahead n l); now auto.
Qed.




Lemma cong_drop_rewrite :
 forall {A : Type} (l1 l2 : PartialColist A) (n : nat),
  l1 ~=~ l2 -> drop_tl_n n l1 ~=~ drop_tl_n n l2.
intro A.
cofix cf.
intros l1 l2 n Hcong.
inversion Hcong; subst; try apply colist_cong_reflexive.
assert (Hla := cong_n_look_ahead_eq n l0 l3 H).
destruct (drop_n_ccons n a l0) as [[Heq Hla0] | [[Heq Hla0] | [Heq Hla0]]]; rewrite Heq, Hla0 in *;
 destruct (drop_n_ccons n a l3) as [[Heq' Hla3] | [[Heq' Hla3] | [Heq' Hla3]]]; rewrite Heq', Hla3 in *;
  try discriminate; constructor.
now auto.
Qed.



Lemma look_ahead_tail_lt :
 forall {A : Type} (n : nat) (a : A) l,
  n_look_ahead n (a :: l) = lt_n -> n_look_ahead n l = lt_n.
intros A n.
induction n as [ | n IHn]; simpl; intros a l Hla.
+ discriminate.
+ clear a.
  destruct l as [ | a l | ].
  - now auto.
  - now eauto.
  - destruct n; simpl in Hla; discriminate.
Qed.

Lemma look_ahead_tail_fail :
 forall {A : Type} (n : nat) (a : A) l,
  n_look_ahead n (a :: l) = fail_n -> n_look_ahead n l = fail_n.
intros A n.
induction n as [ | n IHn]; simpl; intros a l Hla.
+ discriminate.
+ clear a.
  destruct l as [ | a l | ].
  - destruct n; simpl in Hla; discriminate.
  - now eauto.
  - now auto.
Qed.




Lemma drop_S_n_cong :
 forall {A : Type} (n : nat) (l : PartialColist A),
  drop_tl_n 1 (drop_tl_n n l) ~=~ drop_tl_n (S n) l.
intros A n.
cofix cf.
intro l.
destruct l as [ | a l | ].
+ clear cf.
  repeat rewrite drop_n_cnil.
  now constructor.
+ destruct (drop_n_ccons n a l)
   as [[Heqn Hlan] | [[Heqn Hlan] | [Heqn Hlan]]]; rewrite Heqn.
  - clear cf.
    rewrite drop_n_cnil.
    cl_red (drop_tl_n (S n) (a :: l)); simpl.
    destruct l as [ | a' l | ]; simpl.
    * now constructor.
    * rewrite (look_ahead_tail_lt _ _ _ Hlan).
      now constructor.
    * destruct n; simpl in Hlan; discriminate.
  - cl_red (drop_tl_n 1 (a :: drop_tl_n n l)).
    cl_red (drop_tl_n (S n) (a :: l)).
    simpl.
    destruct l as [ | a' l' | ] eqn: Heq; simpl; try constructor.
    destruct (n_look_ahead n l'); constructor.
    rewrite <- Heq in *; clear a' l' Heq.
    now apply cf.
  - clear cf.
    cl_red (drop_tl_n (S n) (a :: l)); simpl.
    destruct l as [ | a' l | ]; simpl.
    * destruct n; simpl in Hlan; discriminate.
    * rewrite (look_ahead_tail_fail _ _ _ Hlan).
      rewrite drop_n_cfail.
      now constructor.
    * rewrite drop_n_cfail.
      now constructor.
+ clear cf.
  repeat rewrite drop_n_cfail.
  now constructor.
Qed.



Lemma drop_nest_add_cong :
 forall {A : Type} (m n : nat) (l : PartialColist A),
  drop_tl_n m (drop_tl_n n l) ~=~ drop_tl_n (m + n) l.
intros A m n l.
induction m as [ | m IHm]; simpl.
+ now apply drop_0_cong.
+ apply colist_cong_transitive with (drop_tl_n 1 (drop_tl_n m (drop_tl_n n l))).
  - apply colist_cong_symmetric.
    now apply drop_S_n_cong.
  - apply colist_cong_transitive with (drop_tl_n 1 (drop_tl_n (m + n) l)).
    * apply cong_drop_rewrite.
      now apply IHm.
    * now apply drop_S_n_cong.
Qed.



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


Theorem cofwd_prefix : forall {X Y : Type} (e : IIST X Y) (xs xs' : PartialColist X),
  coprefix xs' xs -> coprefix (cofwd e xs') (cofwd e xs).
intros X Y e.
induction e as [A X Y a f g | X x e' | X x e' | X Y Z exy IHexy eyz IHeyz | X1 X2 Y1 Y2 e1 IHe1 e2 IHe2]; simpl.
+ revert a.
  cofix mf.
  intros a xs xs' Hpre.
  cl_red (cofwd_mapfold f g a xs').
  cl_red (cofwd_mapfold f g a xs).
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
+ intros xs xs' Hpre.
  apply cozip_prefix.
  - apply drop_prefix.
    apply IHe1.
    apply coleft_prefix.
    now auto.
  - apply drop_prefix.
    apply IHe2.
    apply coright_prefix.
    now auto.
Qed.


Theorem cobwd_prefix : forall {X Y : Type} (e : IIST X Y) (ys ys' : PartialColist Y),
  coprefix ys' ys -> coprefix (cobwd e ys') (cobwd e ys).
intros X Y e.
induction e as [A X Y a f g | X x e' | X x e' | X Y Z exy IHexy eyz IHeyz | X1 X2 Y1 Y2 e1 IHe1 e2 IHe2]; simpl.
+ revert a.
  cofix mf.
  intros a ys ys' Hpre.
  cl_red (cobwd_mapfold f g a ys').
  cl_red (cobwd_mapfold f g a ys).
  inversion Hpre; subst; simpl.
  - now constructor.
  - destruct (backward X Y (f a) a0); simpl; constructor.
    apply mf; now auto.
  - now constructor.
+ intros ys ys' Hpre.
  inversion Hpre; subst; simpl; try constructor.
  destruct equiv_one_dec with a.
  - now auto.
  - now constructor.
+ intros ? ?; now apply coprefix_slide.
+ now eauto.
+ intros ys ys' Hpre.
  apply cozip_prefix.
  - apply drop_prefix.
    apply IHe1.
    apply coleft_prefix.
    now auto.
  - apply drop_prefix.
    apply IHe2.
    apply coright_prefix.
    now auto.
Qed.




Lemma cofwd_nil :
 forall {X Y : Type} (e : IIST X Y),
  cofwd e [] = [].
intros X Y e.
induction e; rewrite colist_frob_eq with (cofwd _ []); simpl; auto.
+ rewrite IHe1.
  rewrite IHe2.
  simpl; now auto.
+ rewrite colist_frob_eq with (coleft []); simpl.
  rewrite IHe1.
  rewrite colist_frob_eq with (coright []); simpl.
  rewrite IHe2.
  destruct (delay_fwd e2 - delay_fwd e1);
   destruct (delay_fwd e1 - delay_fwd e2); simpl; now auto.
Qed.


Lemma cofwd_fail : 
 forall {X Y : Type} (e : IIST X Y),
  cofwd e -*- = -*-.
intros X Y e.
induction e; rewrite colist_frob_eq with (cofwd _ -*-); simpl; auto.
+ rewrite IHe1; rewrite IHe2; simpl.
  now auto.
+ rewrite colist_frob_eq with (coleft -*-); simpl.
  rewrite IHe1.
  now auto.
Qed.


CoInductive failless_colist {A : Type} : PartialColist A -> Prop :=
| flcnil : failless_colist []
| flccons : forall a l, failless_colist l -> failless_colist (a :: l).


Lemma failless_coslide_iff :
 forall {A : Type} (a : A) l,
  failless_colist l <-> failless_colist (coslide a l).
intros A a l.
split; revert a l; cofix cf; intros a l Hfl.
+ cl_red (coslide a l).
  destruct l as [ | a' l | ]; simpl.
  - now constructor.
  - constructor.
    inversion Hfl; subst; now auto.
  - now inversion Hfl.
+ cl_red_in (coslide a l) Hfl.
  destruct l as [ | a' l | ]; simpl in Hfl.
  - now constructor.
  - constructor.
    now inversion Hfl; subst; now eauto.
  - now inversion Hfl.
Qed.


Lemma failless_coleft_iff :
 forall {A B : Type} (l : PartialColist (A * B)),
  failless_colist l <-> failless_colist (coleft l).
intros A B l.
split; revert l; cofix cf; intros l Hfl.
+ cl_red (coleft l).
  destruct l as [ | [a b] l | ]; simpl.
  - now constructor.
  - constructor.
    inversion Hfl; subst; now auto.
  - now inversion Hfl.
+ cl_red_in (coleft l) Hfl.
  destruct l as [ | [a b] l | ]; simpl in Hfl.
  - now constructor.
  - constructor.
    now inversion Hfl; subst; now eauto.
  - now inversion Hfl.
Qed.


Lemma failless_coright_iff :
 forall {A B : Type} (l : PartialColist (A * B)),
  failless_colist l <-> failless_colist (coright l).
intros A B l.
split; revert l; cofix cf; intros l Hfl.
+ cl_red (coright l).
  destruct l as [ | [a b] l | ]; simpl.
  - now constructor.
  - constructor.
    inversion Hfl; subst; now auto.
  - now inversion Hfl.
+ cl_red_in (coright l) Hfl.
  destruct l as [ | [a b] l | ]; simpl in Hfl.
  - now constructor.
  - constructor.
    now inversion Hfl; subst; now eauto.
  - now inversion Hfl.
Qed.



Lemma failless_lookup_not_fail :
 forall {A : Type} (n : nat) (l : PartialColist A),
  failless_colist l -> n_look_ahead n l <> fail_n.
intros A n.
induction n as [ | n IHn]; simpl; intros l Hfl Hnl.
+ inversion Hfl; subst; now inversion Hnl.
+ inversion Hfl; subst; inversion Hnl.
  eapply IHn; now eauto.
Qed.


Lemma failless_drop :
 forall {A : Type} (n : nat) (l : PartialColist A),
  failless_colist l <-> failless_colist (drop_tl_n n l).
intros A n l.
split; revert n l; cofix cf; intros n l Hfl.
+ cl_red (drop_tl_n n l).
  destruct l as [ | a l | ]; simpl.
  - destruct n; simpl; now constructor.
  - destruct (n_look_ahead n l) eqn: Heq.
    * now constructor.
    * inversion Hfl; subst.
      elim failless_lookup_not_fail with n l; now auto.
    * constructor.
      inversion Hfl; now auto.
  - now inversion Hfl.
+ cl_red_in (drop_tl_n n l) Hfl.
  destruct l as [ | a l | ].
  - now constructor.
  - simpl in Hfl.
    constructor.
    destruct (n_look_ahead n l) eqn: Heq.
    * apply cf with n.
      rewrite colist_frob_eq.
      unfold drop_tl_n; simpl.
      {
      destruct l as [ | a' l | ].
      + now constructor.
      + rewrite (look_ahead_tail_lt _ _ _ Heq).
        now constructor.
      + destruct n; discriminate.
      }
    * now inversion Hfl.
    * inversion Hfl; subst.
      now eauto.
  - destruct n; simpl in Hfl; now inversion Hfl.
Qed.


CoInductive failless_coprefix {A : Type} : PartialColist A -> PartialColist A -> Prop :=
| flcopre_nil : forall l, failless_coprefix [] l
| flcopre_cons : forall a l1 l2, failless_coprefix l1 l2 -> failless_coprefix (a :: l1) (a :: l2).



Lemma failless_coprefix_prefix :
 forall {A : Type} (l1 l2 : PartialColist A),
  failless_coprefix l1 l2 -> coprefix l1 l2.
intro A.
cofix cf.
intros l1 l2 Hflpre.
inversion Hflpre; subst; constructor; now auto.
Qed.


Lemma failless_coprefix_failless :
 forall {A : Type} (l1 l2 : PartialColist A),
  failless_coprefix l1 l2 -> failless_colist l1.
intro A.
cofix cf.
intros l1 l2 Hflpre.
inversion Hflpre; subst; constructor; now eauto.
Qed.


Lemma coprefix_failless_flprefix :
 forall {A : Type} (l1 l2 : PartialColist A),
  coprefix l1 l2 -> failless_colist l1 -> failless_coprefix l1 l2.
intro A.
cofix cf.
intros l1 l2 Hpre Hfl.
inversion Hfl; subst; try constructor.
inversion Hpre; subst; constructor; now auto.
Qed.


Lemma failless_coprefix_prefix_compose :
 forall {A : Type} (l1 l2 l3 : PartialColist A),
  failless_coprefix l1 l2 -> coprefix l2 l3 -> failless_coprefix l1 l3.
intro A.
cofix cf.
intros l1 l2 l3 Hflpre Hpre.
inversion Hflpre; subst; try constructor.
inversion Hpre; subst; constructor; now eauto.
Qed.




CoInductive sync_colist {A B: Type} :
 PartialColist A -> PartialColist B -> Prop :=
| sycnil : sync_colist [] []
| syccons : forall a b l1 l2, sync_colist l1 l2 -> sync_colist (a :: l1) (b :: l2)
| sycfail_l : forall l, sync_colist -*- l
| sycfail_r : forall l, sync_colist l   -*-.



Lemma sync_colist_reflexive :
 forall {A : Type} (l : PartialColist A),
  sync_colist l l.
intro A.
cofix cf.
intro l.
destruct l; constructor.
now auto.
Qed.


Lemma sync_colist_symmetric :
 forall {A B : Type} (l1 : PartialColist A) (l2 : PartialColist B),
  sync_colist l1 l2 -> sync_colist l2 l1.
intros A B.
cofix cf.
intros l1 l2 Hsyn.
inversion Hsyn; subst; constructor.
now auto.
Qed.


(* transitivityは成り立たない（つなぐものがfailだと各々に条件がない） *)


Lemma sync_colist_zip_failless_left :
 forall {A B : Type} (l1 : PartialColist A) (l2 : PartialColist B),
  sync_colist l1 l2 -> failless_colist (cozip l1 l2) -> failless_colist l1.
intros A B.
cofix cf.
intros l1 l2 Hsyn Hfl.
cl_red_in (cozip l1 l2) Hfl.
inversion Hsyn; subst; simpl in *.
+ now constructor.
+ constructor.
  inversion Hfl; subst.
  now eauto.
+ now inversion Hfl; subst.
+ destruct l1; simpl in Hfl; now inversion Hfl.
Qed.


Lemma sync_colist_zip_failless_right :
 forall {A B : Type} (l1 : PartialColist A) (l2 : PartialColist B),
  sync_colist l1 l2 -> failless_colist (cozip l1 l2) -> failless_colist l2.
intros A B.
cofix cf.
intros l1 l2 Hsyn Hfl.
cl_red_in (cozip l1 l2) Hfl.
inversion Hsyn; subst; simpl in *.
+ now constructor.
+ inversion Hfl; subst; constructor; now eauto.
+ now inversion Hfl.
+ destruct l1; simpl in Hfl; now inversion Hfl.
Qed.



CoInductive oneway_sync_colist {A B : Type} :
 PartialColist A -> PartialColist B -> Prop :=
| owsycnil : oneway_sync_colist [] []
| owsyccons : forall a b l1 l2, oneway_sync_colist l1 l2 -> oneway_sync_colist (a :: l1) (b :: l2)
| owsycfail : forall l, oneway_sync_colist l -*-.


Lemma oneway_sync_reflexive :
 forall {A : Type} (l : PartialColist A),
  oneway_sync_colist l l.
intro A.
cofix cf.
intro l.
destruct l; constructor.
now auto.
Qed.


Lemma oneway_sync_transitive :
 forall {A B C : Type} (l1 : PartialColist A) (l2 : PartialColist B) (l3 : PartialColist C),
  oneway_sync_colist l1 l2 -> oneway_sync_colist l2 l3 -> oneway_sync_colist l1 l3.
intros A B C.
cofix cf.
intros l1 l2 l3 Hos12 Hos23.
inversion Hos12; subst; inversion Hos23; subst; constructor.
now eauto.
Qed.


Lemma cong_oneway_sync_rewrite_l :
 forall {A B : Type} (l1 l1' : PartialColist A) (l2 : PartialColist B),
  l1 ~=~ l1' -> oneway_sync_colist l1 l2 -> oneway_sync_colist l1' l2.
intros A B.
cofix cf.
intros l1 l1' l2 Hcong How;
 inversion Hcong; subst;
  inversion How; subst;
   try constructor.
now eauto.
Qed.


Lemma oneway_sync_sync :
 forall {A B : Type} (l1 : PartialColist A) (l2 : PartialColist B),
  oneway_sync_colist l1 l2 -> sync_colist l1 l2.
intros A B.
cofix cf.
intros l1 l2 Hos.
inversion Hos; subst; constructor; now auto.
Qed.



Lemma oneway_sync_look_ahead_lt :
 forall {A B : Type} (n : nat) (l1 : PartialColist A) (l2 : PartialColist B),
  oneway_sync_colist l1 l2 -> n_look_ahead n l2 = lt_n -> n_look_ahead n l1 = lt_n.
intros A B n.
induction n as [ | n IHn]; intros l1 l2 How Hnl;
 inversion How; subst; simpl in *; try discriminate; now eauto.
Qed.


Lemma oneway_sync_look_ahead_more :
 forall {A B : Type} (n : nat) (l1 : PartialColist A) (l2 : PartialColist B),
  oneway_sync_colist l1 l2 -> n_look_ahead n l2 = more_n -> n_look_ahead n l1 = more_n.
intros A B n.
induction n as [ | n IHn]; intros l1 l2 How Hnl;
 inversion How; subst; simpl in *; try discriminate; now eauto.
Qed.





Lemma oneway_sync_drop_rewrite :
 forall {A B : Type} (n : nat) (l1 : PartialColist A) (l2 : PartialColist B),
  oneway_sync_colist l1 l2 -> oneway_sync_colist (drop_tl_n n l1) (drop_tl_n n l2).
intros A B n; cofix cf; intros l1 l2 How.
cl_red (drop_tl_n n l1).
cl_red (drop_tl_n n l2).
inversion How; subst; simpl; try constructor.
destruct (n_look_ahead n l3) eqn: Heq.
+ rewrite (oneway_sync_look_ahead_lt _ _ _ H Heq).
  now constructor.
+ now constructor.
+ rewrite (oneway_sync_look_ahead_more n _ _ H Heq).
  constructor.
  now auto.
Qed.



Lemma oneway_sync_zip :
 forall {A B C D : Type}
        (la : PartialColist A) (lb : PartialColist B)
        (lc : PartialColist C) (ld : PartialColist D),
  oneway_sync_colist la lb
  -> oneway_sync_colist lc ld
  -> oneway_sync_colist (cozip la lc) (cozip lb ld).
intros A B C D.
cofix cf.
intros la lb lc ld Hosab Hoscd.
cl_red (cozip la lc).
cl_red (cozip lb ld).
inversion Hosab; subst;
 inversion Hoscd; subst;
  simpl; try constructor.
now eauto.
Qed.




CoInductive strict_sync_colist {A B : Type} :
 PartialColist A -> PartialColist B -> Prop :=
| stsycnil : strict_sync_colist [] []
| stsyccons : forall a b l1 l2, strict_sync_colist l1 l2 -> strict_sync_colist (a :: l1) (b :: l2)
| stsycfail : strict_sync_colist -*- -*-.


Lemma strict_sync_reflexive :
 forall {A : Type} (l : PartialColist A),
  strict_sync_colist l l.
intro A.
cofix cf.
intro l.
destruct l; constructor.
now auto.
Qed.


Lemma strict_sync_symmetric :
 forall {A B : Type} (l1 : PartialColist A) (l2 : PartialColist B),
  strict_sync_colist l1 l2 -> strict_sync_colist l2 l1.
intros A B.
cofix cf.
intros l1 l2 Hss.
inversion Hss; subst; constructor.
now auto.
Qed.


Lemma strict_sync_transitive :
 forall {A B C : Type} (l1 : PartialColist A) (l2 : PartialColist B) (l3 : PartialColist C),
  strict_sync_colist l1 l2 -> strict_sync_colist l2 l3 -> strict_sync_colist l1 l3.
intros A B C.
cofix cf.
intros l1 l2 l3 Hss12 Hss23.
inversion Hss12; subst; inversion Hss23; subst; constructor.
now eauto.
Qed.


Lemma strict_sync_oneway :
 forall {A B : Type} (l1 : PartialColist A) (l2 : PartialColist B),
  strict_sync_colist l1 l2 -> oneway_sync_colist l1 l2.
intros A B.
cofix cf.
intros l1 l2 Hss.
inversion Hss; subst; constructor.
now auto.
Qed.



Lemma coleft_right_strict_sync_colist :
 forall {A B : Type} (l : PartialColist (A * B)),
  strict_sync_colist (coleft l) (coright l).
intros A B.
cofix cf.
intro l.
cl_red (coleft l).
cl_red (coright l).
destruct l as [ | [a b] l | ]; simpl; constructor.
now auto.
Qed.



Lemma strict_sync_look_ahead :
 forall {A B : Type} (n : nat) (l1 : PartialColist A) (l2 : PartialColist B),
  strict_sync_colist l1 l2 -> n_look_ahead n l1 = n_look_ahead n l2.
intros A B n.
induction n as [ | IHn]; intros l1 l2 Hss; inversion Hss; subst; simpl; now auto.
Qed.


Lemma strict_sync_drop_rewrite :
 forall {A B : Type} (n : nat) (l1 : PartialColist A) (l2 : PartialColist B),
  strict_sync_colist l1 l2 -> strict_sync_colist (drop_tl_n n l1) (drop_tl_n n l2).
intros A B n; cofix cf; intros l1 l2 Hss.
cl_red (drop_tl_n n l1).
cl_red (drop_tl_n n l2).
inversion Hss; subst; simpl; try constructor.
rewrite (strict_sync_look_ahead n _ _ H).
destruct (n_look_ahead n l3); constructor.
now eauto.
Qed.


Lemma strict_sync_coslide :
 forall {A : Type} (a : A) l, strict_sync_colist l (coslide a l).
intro A.
cofix cf.
intros a l.
cl_red (coslide a l).
destruct l as [ | a' l | ]; simpl; constructor.
now auto.
Qed.



Lemma strict_sync_zip :
 forall {A B : Type} (l1 : PartialColist A) (l2 : PartialColist B),
  strict_sync_colist l1 l2
  -> strict_sync_colist l1 (cozip l1 l2).
intros A B.
cofix cf.
intros l1 l2 Hss.
cl_red (cozip l1 l2).
inversion Hss; subst; simpl; constructor.
now auto.
Qed.


Lemma cozip_drop_strict_distributive :
 forall {A B : Type} (n : nat) (l1 : PartialColist A)(l2 : PartialColist B),
  strict_sync_colist l1 l2
  -> cozip (drop_tl_n n l1) (drop_tl_n n l2) ~=~ drop_tl_n n (cozip l1 l2).
intros A B n.
cofix cf.
intros l1 l2 Hss.
cl_red (cozip (drop_tl_n n l1) (drop_tl_n n l2)).
cl_red (drop_tl_n n (cozip l1 l2)).
cl_red (drop_tl_n n l1).
cl_red (drop_tl_n n l2).
cl_red (cozip l1 l2).
inversion Hss; simpl; try constructor.
+ rewrite <- (strict_sync_look_ahead _ _ _ H).
  rewrite <- (strict_sync_look_ahead _ _ _ (strict_sync_zip _ _ H)).
  destruct (n_look_ahead n l0) eqn: Heq; constructor.
  now apply cf.
Qed.







Lemma strict_oneway_sync :
 forall {A B C D : Type}
        (la : PartialColist A)
        (lb : PartialColist B)
        (lc : PartialColist C)
        (ld : PartialColist D),
 strict_sync_colist la lb
  -> oneway_sync_colist la lc
  -> oneway_sync_colist lb ld
  -> sync_colist lc ld.
intros A B C D.
cofix cf.
intros la lb lc ld Hss Hos1 Hos2.
inversion Hss; subst;
 inversion Hos1; subst;
  inversion Hos2; subst;
   try constructor.
now eauto.
Qed.



Lemma cofwd_drop_oneway_sync :
 forall {X Y : Type} (e : IIST X Y) (xs : PartialColist X),
  oneway_sync_colist (drop_tl_n (delay_fwd e) xs) (cofwd e xs).
intros X Y e.
induction e as [A X Y a f g | X x e' | X x e' | X Y Z exy IHexy eyz IHeyz | X1 X2 Y1 Y2 e1 IHe1 e2 IHe2];
 intro xs; simpl.
+ apply cong_oneway_sync_rewrite_l with xs.
  - apply colist_cong_symmetric.
    now apply drop_0_cong.
  - revert a xs.
    cofix cf.
    intros a xs.
    cl_red (cofwd_mapfold f g a xs).
    destruct xs as [ | x xs | ]; simpl; try constructor.
    destruct (forward X Y (f a) x) as [ y | ]; simpl; constructor.
    now apply cf.
+ apply cong_oneway_sync_rewrite_l with xs.
  - apply colist_cong_symmetric.
    now apply drop_0_cong.
  - apply strict_sync_oneway.
    now apply strict_sync_coslide.
+ destruct xs as [ | x' xs | ]; simpl; try constructor.
  - rewrite drop_n_cnil.
    now constructor.
  - destruct (equiv_one_dec x') as [e | e]; try constructor.
    rewrite <- e; clear x' e e'.
    revert x xs; cofix cf; intros x xs.
    cl_red (drop_tl_n 1 (x :: xs)).
    destruct xs as [ | x' xs | ]; simpl; try constructor.
    now apply cf.
+ apply cong_oneway_sync_rewrite_l
   with (l1 := drop_tl_n (delay_fwd eyz) (drop_tl_n (delay_fwd exy) xs)).
  - rewrite PeanoNat.Nat.add_comm.
    now apply drop_nest_add_cong.
  - apply oneway_sync_transitive with (drop_tl_n (delay_fwd eyz) (cofwd exy xs)).
    * apply oneway_sync_drop_rewrite.
      now apply IHexy.
    * now apply IHeyz.
+ apply cong_oneway_sync_rewrite_l
   with (l1 := drop_tl_n (Nat.max (delay_fwd e1) (delay_fwd e2)) (cozip (coleft xs) (coright xs))).
  {
    apply cong_drop_rewrite.
    apply colist_cong_symmetric.
    now apply cozip_left_right_cong.
  }
  apply cong_oneway_sync_rewrite_l
   with (l1 := cozip (drop_tl_n (max (delay_fwd e1) (delay_fwd e2)) (coleft xs))
                     (drop_tl_n (max (delay_fwd e1) (delay_fwd e2)) (coright xs))).
  {
    apply cozip_drop_strict_distributive.
    now apply coleft_right_strict_sync_colist.
  }
  apply oneway_sync_zip.
  - rewrite max_minus_plus2.
    apply cong_oneway_sync_rewrite_l
     with (l1 := drop_tl_n (delay_fwd e2 - delay_fwd e1) (drop_tl_n (delay_fwd e1) (coleft xs))).
    * now apply drop_nest_add_cong.
    * apply oneway_sync_drop_rewrite.
      now auto.
  - rewrite max_minus_plus1.
    apply cong_oneway_sync_rewrite_l
     with (l1 := drop_tl_n (delay_fwd e1 - delay_fwd e2) (drop_tl_n (delay_fwd e2) (coright xs))).
    * now apply drop_nest_add_cong.
    * apply oneway_sync_drop_rewrite.
      now auto.
Qed.




Theorem cofwd_sync_colist :
 forall {X1 X2 Y1 Y2 : Type} (e1 : IIST X1 Y1) (e2 : IIST X2 Y2)
        (l1 : PartialColist X1) (l2 : PartialColist X2),
  strict_sync_colist l1 l2
  -> sync_colist (drop_tl_n (delay_fwd e2 - delay_fwd e1) (cofwd e1 l1))
                 (drop_tl_n (delay_fwd e1 - delay_fwd e2) (cofwd e2 l2)).
intros X1 X2 Y1 Y2 e1 e2 l1 l2 Hss.
apply strict_sync_drop_rewrite with (n := max (delay_fwd e1) (delay_fwd e2)) in Hss.
apply (strict_oneway_sync _ _ _ _ Hss).
+ rewrite max_minus_plus2.
  apply cong_oneway_sync_rewrite_l
   with (l1 := drop_tl_n (delay_fwd e2 - delay_fwd e1) (drop_tl_n (delay_fwd e1) l1)).
  - now apply drop_nest_add_cong.
  - apply oneway_sync_drop_rewrite.
    now apply cofwd_drop_oneway_sync.
+ rewrite max_minus_plus1.
  apply cong_oneway_sync_rewrite_l
   with (l1 := drop_tl_n (delay_fwd e1 - delay_fwd e2) (drop_tl_n (delay_fwd e2) l2)).
  - now apply drop_nest_add_cong.
  - apply oneway_sync_drop_rewrite.
    now apply cofwd_drop_oneway_sync.
Qed.



Theorem cofwd_failless_input :
 forall {X Y : Type} (e : IIST X Y) xs,
  failless_colist (cofwd e xs) -> failless_colist xs.
intros X Y e.
induction e as [A X Y a f g | X x e' | X x e' | X Y Z exy IHexy eyz IHeyz | X1 X2 Y1 Y2 e1 IHe1 e2 IHe2];
 simpl.
+ revert a.
  cofix cf.
  intros a xs Hfl.
  cl_red_in (cofwd_mapfold f g a xs) Hfl.
  destruct xs; simpl in *; try constructor.
  - destruct (forward X Y (f a) x); simpl in Hfl; inversion Hfl; subst.
    now eauto.
  - now inversion Hfl.
+ intro xs; apply failless_coslide_iff.
+ intros xs Hfl.
  destruct xs as [ | x' xs | ].
  - now constructor.
  - destruct (equiv_one_dec x').
    * constructor; now auto.
    * now inversion Hfl.
  - now inversion Hfl.
+ now eauto.
+ intros xs Hfl.
  apply failless_coleft_iff.
  apply IHe1.
  assert (Hss := coleft_right_strict_sync_colist xs).
  apply cofwd_sync_colist with (e1 := e1) (e2 := e2) in Hss.
  apply sync_colist_zip_failless_left in Hfl; auto.
  apply failless_drop in Hfl.
  now auto.
Qed.




Lemma failless_oneway_strict_sync :
 forall {A B : Type} (l1 : PartialColist A) (l2 : PartialColist B),
  failless_colist l2 -> oneway_sync_colist l1 l2 -> strict_sync_colist l1 l2.
intros A B.
cofix cf.
intros l1 l2 Hfl How.
inversion Hfl; subst; inversion How; subst; constructor.
apply cf; now auto.
Qed.


Lemma cofwd_failless_drop_strict_sync :
 forall {X Y : Type} (e : IIST X Y) (xs : PartialColist X),
  failless_colist (cofwd e xs)
  -> strict_sync_colist (drop_tl_n (delay_fwd e) xs) (cofwd e xs).
intros X Y e xs Hfl.
apply failless_oneway_strict_sync; auto.
now apply cofwd_drop_oneway_sync.
Qed.


(*
(* xs'がfaillessなのは保証される（上の定理による）が、prefixかはわからない。 *)
(* induction eで多くのケースは解けそうな気がする *)
(* mapfoldのとき証明できるか...？ysの長さ（？）がわからないと示せないぞ...？ *)
Theorem cofwd_failless_inverse :
 forall {X Y : Type} (e : IIST X Y) xs ys,
  failless_coprefix ys (cofwd e xs)
  -> exists xs', cofwd e xs' ~=~ ys /\ failless_coprefix xs' xs.
Abort.



Theorem cofwd_bwd :
 forall {X Y : Type} (e : IIST X Y) xs ys,
  failless_coprefix ys (cofwd e xs)
  -> failless_coprefix (cobwd e ys) xs.
Admitted.


Lemma cong_is_prefix_and_strict_sync :
 forall {A : Type} (l1 l2 : PartialColist A),
  coprefix l1 l2 -> strict_sync_colist l1 l2 -> l1 ~=~ l2.
intro A.
cofix cf.
intros l1 l2 Hpre Hss.
inversion Hpre; subst;
 inversion Hss; subst; constructor.
now auto.
Qed.


(* ある種の長さ制約 *)
Theorem cofwd_bwd_length :
 forall {X Y : Type} (e : IIST X Y) xs,
  failless_colist (cofwd e xs) ->
   cobwd e (cofwd e xs) ~=~ drop_tl_n (delay_bwd e + delay_fwd e) xs.
intros X Y e xs Hfl.
apply cong_is_prefix_and_strict_sync.
+ apply failless_coprefix_prefix.
  apply cofwd_bwd.
  admit.
+ apply strict_sync_transitive with (l2 := (drop_tl_n (delay_bwd e) (cofwd e xs))).
  - admit.
  - apply cofwd_failless_drop_strict_sync.
*)
