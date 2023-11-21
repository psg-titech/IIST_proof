Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Coq.Classes.EquivDec.
(* 最初は試しに有限長のリストで処理をするが、無限長にしたいならCoInductiveなList-likeな型を定義しないといけない *)

Section slide.

Context {A : Type}.

Fixpoint slide (a : A) (al : list A) : list A :=
match al with
| nil => nil
| a' :: al' => cons a (slide a' al')
end.

Theorem slide_length :
 forall a al, length al = length (slide a al).
intros a al; revert a; induction al; intros; simpl in *; auto.
Qed.

End slide.

Section prefix.

Context {A : Type}.

Inductive prefix : list A -> list A -> Prop :=
| pre_nil : forall l, prefix nil l
| pre_cons : forall a l1 l2, prefix l1 l2 -> prefix (a :: l1) (a :: l2)
.

Theorem prefix_reflexive : 
 forall l, prefix l l.
induction l; intros; constructor; now auto.
Qed.

Theorem prefix_length :
 forall l1 l2, prefix l1 l2 -> length l1 <= length l2.
intros l1 l2 H; induction H; simpl in *; now lia.
Qed.

Theorem prefix_app :
 forall l1 l2, prefix l1 l2 -> exists l3, l1 ++ l3 = l2.
intros l1 l2 H; induction H; simpl in *.
+ exists l; now auto.
+ destruct IHprefix as [l3 IH]; exists l3; rewrite IH; now auto.
Qed.

Theorem app_prefix :
 forall l1 l2 l3, l1 ++ l3 = l2 -> prefix l1 l2.
induction l1; intros; simpl in *; subst; try constructor; now eauto.
Qed.


Theorem prefix_transitive :
 forall l1 l2 l3,
  prefix l1 l2 -> prefix l2 l3 -> prefix l1 l3.
induction l1; intros; try constructor.
inversion H; subst.
inversion H0; subst.
constructor; now eauto.
Qed.

(* ちょっと特殊ケース過ぎるか？ *)
Theorem slide_prefix :
 forall a al,
  prefix (slide a al) (a :: al).
intros a al; revert a; induction al; intros; simpl; constructor; now auto.
Qed.

Theorem prefix_slide :
 forall a al1 al2,
  prefix al1 al2 -> prefix (slide a al1) (slide a al2).
intros a al1 al2 H; revert a; induction H; intros; simpl in *; constructor; now auto.
Qed.


End prefix.


Section prefix2.


Theorem split_prefix :
 forall {A B} (abl abl' : list (A * B)) al bl al' bl',
  prefix abl' abl ->
   (al, bl) = split abl ->
   (al', bl') = split abl' ->
    prefix al' al /\ prefix bl' bl.
intros A B abl abl' al bl al' bl' H; revert al bl al' bl'.
induction H; intros; simpl in *.
- inversion H0; subst.
  split; now constructor.
- destruct (split l2).
  destruct (split l1).
  destruct a.
  destruct (IHprefix l l0 l3 l4 eq_refl eq_refl).
  inversion H0; inversion H1; subst; split; constructor; now auto.
Qed.

Theorem combine_prefix :
 forall {A B : Type} (al : list A) (bl : list B) al' bl',
  prefix al' al -> prefix bl' bl -> prefix (combine al' bl') (combine al bl).
intros A B al bl al' bl' H; revert bl bl'; induction H as [ | a al' al H]; intros; simpl in *; try constructor.
inversion H0; subst; constructor.
apply IHH; now auto.
Qed.


Theorem split_combine_prefix :
 forall {A B : Type} (al : list A) (bl : list B) al' bl',
  split (combine al bl) = (al', bl') ->
   prefix al' al /\ prefix bl' bl.
induction al; intros; simpl in H.
- inversion H; subst.
  split; now constructor.
- destruct bl as [ | b bl]; simpl in H. 
  * inversion H; subst. split; now constructor.
  * destruct (split (combine al bl)) as [al'' bl''] eqn: Heq.
    apply IHal in Heq; destruct Heq as [H1 H2].
    inversion H; subst.
    split; constructor; now auto.
Qed.


End prefix2.


Section option_bind.

Definition option_bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
match a with
| Some a => f a
| None => None
end.

End option_bind.




Section pinv_fun.


Record partial_invertible_function (A : Type) (B : Type) : Type := {
  forward : A -> option B;
  backward : B -> option A;
  invertible : forall (a : A) (b : B), forward a = Some b <-> backward b = Some a
}.

End pinv_fun.


Section list_tail.

Theorem list_nil_tail_app :
 forall {A : Type} (l : list A),
  l = [] \/ exists a l', l = l' ++ [a].
induction l; auto; right.
destruct IHl as [IHl | [a' [l' IHl]]]; subst.
+ exists a, []; simpl; now auto.
+ exists a', (a :: l'); simpl; now auto.
Qed.

Theorem list_inv_ind :
  forall (A : Type) (P : list A -> Prop),
   P [] -> (forall (a : A) (l : list A), P l -> P (l ++ [a])) -> forall l : list A, P l.
intros.
remember (length l).
revert l Heqn.
induction n.
+ intros l Heqn.
  destruct l; simpl in Heqn; inversion Heqn; now auto.
+ intros l Heqn.
  destruct (list_nil_tail_app l) as [Hl | [a [l' Hl]]]; subst.
  - simpl in Heqn; inversion Heqn.
  - rewrite app_length in Heqn. rewrite PeanoNat.Nat.add_comm in Heqn.
    simpl in Heqn.
    inversion Heqn.
    apply H0; now auto.
Qed.


Fixpoint last_elem {A : Type} (a : A) (l : list A) : A :=
match l with
| [] => a
| a' :: l' => last_elem a' l'
end.

Lemma last_elem_correct :
 forall A (l : list A) a a',
  last_elem a (l ++ [a']) = a'.
induction l; intros; simpl in *; auto.
Qed.

Lemma last_elem_correct' :
 forall A (l : list A) a a',
  last_elem a l = a'
  -> l = [] /\ a = a' \/ exists l', l = l' ++ [a'].
intros A l; induction l; [left | right]; simpl in *; auto.
destruct (IHl _ _ H) as [[? ?] | [l' Hl']].
+ exists []; subst; simpl; now auto.
+ exists (a :: l'); rewrite Hl'; simpl; now auto.
Qed.


Definition last {A : Type} (l : list A) : option A :=
match l with
| [] => None
| a :: l' => Some (last_elem a l')
end.


Lemma last_correct :
 forall A (l : list A) a,
  last (l ++ [a]) = Some a.
destruct l; intros; simpl in *; auto.
rewrite last_elem_correct; now auto.
Qed.


Lemma last_Some :
 forall A (l : list A),
  length l > 0 -> exists a, last l = Some a.
intros; destruct l; simpl in *.
+ unfold gt, lt in H; now contradict H.
+ clear H; revert a.
  induction l; intros; simpl in *.
  - exists a; now auto.
  - destruct IHl with a; eexists; now eauto.
Qed.


Lemma last_correct' :
 forall A (l : list A) a,
  last l = Some a -> exists l', l = l' ++ [a].
intros; destruct l; inversion H.
destruct (last_elem_correct' _ _ _ _ H1) as [[? ?] | [? ?]].
+ exists []; subst; now auto.
+ exists (a0 :: x); rewrite H1; rewrite H0; now auto.
Qed.



End list_tail.



Section EqOneDec.

Class EqOneDec {A} (a : A) :=
  equiv_one_dec : forall b : A, { a = b } + { a <> b }.


Definition eqdec_one {A} `{EqDec A eq} a : EqOneDec a :=
   fun b => equiv_dec a b.


#[global]
Program Instance option_None_eqdec {A} : @EqOneDec (option A) None.
Next Obligation.
destruct b.
+ right; intro H; now inversion H.
+ left; now auto.
Defined.


#[global]
Program Instance list_nil_eqdec {A} : @EqOneDec (list A) [].
Next Obligation.
destruct b.
+ left; now auto.
+ right; intro H; now inversion H.
Defined.



#[global]
Program Instance option_Some_None_eqdec {A} : @EqOneDec (option (option A)) (Some None).
Next Obligation.
destruct b as [[ a | ] | ].
+ right; intro H; now inversion H.
+ left; now auto.
+ right; intro H; now inversion H.
Defined.


Definition eqdec_Some_eqdec {A} (a : A) `{EqOneDec A a} : @EqOneDec (option A) (Some a).
intro b.
destruct b.
+ destruct H with a0.
  - left; subst; now auto.
  - right; intro H'; apply n; inversion H'; now auto.
+ right; intro H'; now inversion H'.
Defined.


End EqOneDec.



Section IIST.


Notation "A <~~> B" := (partial_invertible_function A B) (at level 95, no associativity).



Inductive IIST : Type -> Type -> Type :=
| IIST_mapfold : forall {A X Y : Type},
   A -> (A -> X <~~> Y) -> (A -> X -> A) -> IIST X Y
| IIST_delay : forall {X : Type} (x : X) `{e : EqOneDec X x}, IIST X X
| IIST_hasten : forall {X : Type} (x : X) `{e : EqOneDec X x}, IIST X X
| IIST_seqcomp : forall {X Y Z : Type}, IIST X Y -> IIST Y Z -> IIST X Z
| IIST_parcomp : forall {X1 X2 Y1 Y2 : Type}, IIST X1 Y1 -> IIST X2 Y2 -> IIST (X1 * X2) (Y1 * Y2)
.


Fixpoint fwd_mapfold {A X Y : Type} (f : A -> X <~~> Y) (g : A -> X -> A) (a : A) xs : option (list Y) :=
match xs with
| nil => Some nil
| x :: xs' =>
   option_bind ((forward _ _ (f a)) x) (fun y => option_bind (fwd_mapfold f g (g a x) xs') (fun ys => Some (cons y ys)))
end.

Fixpoint fwd {X Y : Type} (e : IIST X Y) : list X -> option (list Y) :=
match e with
| IIST_mapfold a f g => fwd_mapfold f g a
| IIST_delay x => fun xs => Some (slide x xs)
| IIST_hasten x => fun xs =>
   match xs with
   | nil => Some nil
   | x' :: xs' => if equiv_one_dec x' then Some xs' else None
   end
| IIST_seqcomp xz zy => fun xs => option_bind (fwd xz xs) (fwd zy)
| IIST_parcomp xy1 xy2 => fun x12s =>
   let (x1s, x2s) := split x12s in
   option_bind (fwd xy1 x1s)
               (fun y1s => option_bind (fwd xy2 x2s)
                                       (fun y2s => Some (combine y1s y2s)))
end.

Fixpoint bwd_mapfold {A X Y : Type} (f : A -> X <~~> Y) (g : A -> X -> A) (a : A) ys : option (list X) :=
match ys with
| nil => Some nil
| y :: ys' =>
   option_bind ((backward _ _ (f a)) y) (fun x => option_bind (bwd_mapfold f g (g a x) ys') (fun xs => Some (cons x xs)))
end.


Fixpoint bwd {X Y : Type} (e : IIST X Y) : list Y -> option (list X) :=
match e with
| IIST_mapfold a f g => bwd_mapfold f g a
| IIST_delay x => fun ys =>
   match ys with
   | nil => Some nil
   | y' :: ys' => if equiv_one_dec y' then Some ys' else None
   end
| IIST_hasten x => fun ys => Some (slide x ys)
| IIST_seqcomp xz zy => fun ys => option_bind (bwd zy ys) (bwd xz)
| IIST_parcomp xy1 xy2 => fun y12s =>
   let (y1s, y2s) := split y12s in
   option_bind (bwd xy1 y1s)
               (fun x1s => option_bind (bwd xy2 y2s)
                                       (fun x2s => Some (combine x1s x2s)))
end.



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


Lemma fwd_length_delay : forall {X Y : Type} (e : IIST X Y) (xs : list X) (ys : list Y),
  fwd e xs = Some ys -> length xs - delay_fwd e = length ys.
induction e; simpl.
- intros xs ys H; rewrite PeanoNat.Nat.sub_0_r.
  revert a ys H; induction xs; simpl in *.
  + intros a ys H; inversion H; simpl; now lia.
  + intros a1 ys H. destruct (forward X Y (p a1) a); simpl in *; try now inversion H.
    destruct (fwd_mapfold p a0 (a0 a1 a) xs) as [l | ] eqn: H1; simpl in H; try inversion H.
    simpl; rewrite IHxs with (a0 a1 a) l; now auto.
- intros xs ys H; rewrite PeanoNat.Nat.sub_0_r.
  inversion H.
  now apply slide_length.
- intros xs ys H.
  destruct xs.
  + inversion H; simpl; now auto.
  + destruct (equiv_one_dec x0); inversion H; simpl; lia.
- intros xs zs H.
  destruct (fwd e1 xs) as [ys | ] eqn: H1; simpl in H; inversion H; subst.
  rewrite PeanoNat.Nat.sub_add_distr.
  rewrite (IHe1 xs ys H1); now auto.
- intros x12s y12s H.
  destruct (split x12s) as [x1s x2s] eqn: Hx12.
  destruct (fwd e1 x1s) as [y1s | ] eqn: H1s; simpl in H; try now inversion H.
  destruct (fwd e2 x2s) as [y2s | ] eqn: H2s; simpl in H; inversion H.
  assert (Hx1l := split_length_l x12s).
  assert (Hx2l := split_length_r x12s).
  rewrite Hx12 in *; simpl in *.
  rewrite combine_length.
  apply IHe1 in H1s.
  apply IHe2 in H2s.
  lia.
Qed.


Lemma bwd_length_delay : forall {X Y : Type} (e : IIST X Y) (ys : list Y) (xs : list X),
  bwd e ys = Some xs -> length ys - delay_bwd e = length xs.
induction e; simpl.
- intros ys xs H; rewrite PeanoNat.Nat.sub_0_r.
  revert a xs H; induction ys; simpl in *.
  + intros a xs H; inversion H; simpl; now lia.
  + intros a1 xs H. destruct (backward X Y (p a1) a); simpl in *; try now inversion H.
    destruct (bwd_mapfold p a0 (a0 a1 x) ys) as [l | ] eqn: H1; simpl in H; try inversion H.
    simpl; rewrite IHys with (a0 a1 x) l; now auto.
- intros ys xs H.
  destruct ys; simpl in *.
  + inversion H; simpl; now auto.
  + destruct (equiv_one_dec x0); inversion H; lia.
- intros ys xs H; rewrite PeanoNat.Nat.sub_0_r.
  inversion H.
  now apply slide_length.
- intros zs xs H.
  destruct (bwd e2 zs) as [ys | ] eqn: H1; simpl in H; inversion H; subst.
  rewrite PeanoNat.Nat.add_comm; rewrite PeanoNat.Nat.sub_add_distr.
  rewrite (IHe2 zs ys H1); now auto.
- intros y12s x12s H.
  destruct (split y12s) as [y1s y2s] eqn: Hy12.
  destruct (bwd e1 y1s) as [x1s | ] eqn: H1s; simpl in H; try now inversion H.
  destruct (bwd e2 y2s) as [x2s | ] eqn: H2s; simpl in H; inversion H.
  assert (Hy1l := split_length_l y12s).
  assert (Hy2l := split_length_r y12s).
  rewrite Hy12 in *; simpl in *.
  rewrite combine_length.
  apply IHe1 in H1s.
  apply IHe2 in H2s.
  lia.
Qed.


Lemma fwd_prefix : forall {X Y : Type} (e : IIST X Y) (xs xs' : list X) (ys : list Y),
  prefix xs' xs -> fwd e xs = Some ys -> exists ys', fwd e xs' = Some ys' /\ prefix ys' ys.
induction e; simpl.
- intro xs; revert a; induction xs; intros; simpl in *; inversion H; subst; simpl.
  + exists nil; split; auto; now constructor.
  + exists nil; split; auto; now constructor.
  + destruct (forward X Y (p a1) a); simpl in *; try now inversion H0.
    destruct (fwd_mapfold p a0 (a0 a1 a) xs) as [l | ] eqn: H4; try now inversion H0.
    destruct IHxs with (a := a0 a1 a) (xs' := l1) (ys := l); auto.
    destruct H1.
    exists (y :: x).
    split.
    * rewrite H1; reflexivity.
    * inversion H0; subst.
      constructor; now auto.
- intros.
  exists (slide x xs'); split; auto.
  inversion H0; subst.
  apply prefix_slide; now auto.
- intros; inversion H; subst; simpl.
  + exists nil; split; auto; now constructor.
  + destruct (equiv_one_dec a); inversion H0; subst.
    exists l1; split; now auto.
- intros.
  assert (He1 := IHe1 xs xs'); clear IHe1.
  destruct (fwd e1 xs) as [zs | ]; simpl in *; try now inversion H0.
  destruct (He1 zs) as [zs' [H1 H2]]; auto; clear He1.
  destruct (IHe2 zs zs' ys) as [ys' [H3 H4]]; auto; clear IHe2.
  exists ys'; split; auto.
  rewrite H1; simpl; rewrite H3; reflexivity.
- intros.
  destruct (split xs) as [x1s x2s] eqn: Hx12s.
  destruct (split xs') as [x1s' x2s'] eqn: Hx12s'.
  destruct (fwd e1 x1s) as [y1s | ] eqn: H1; simpl in H0; try now inversion H0.
  destruct (fwd e2 x2s) as [y2s | ] eqn: H2; simpl in H0; inversion H0; subst.
  destruct (split_prefix _ _ x1s x2s x1s' x2s' H).
  * rewrite Hx12s; now auto.
  * rewrite Hx12s'; now auto.
  * destruct (IHe1 _ _ _ H3 H1) as [ y1s' [He1 He1p]]; clear IHe1.
    destruct (IHe2 _ _ _ H4 H2) as [ y2s' [He2 He2p]]; clear IHe2.
    exists (combine y1s' y2s').
    rewrite He1, He2; simpl.
    split; auto.
    apply combine_prefix; now auto.
Qed.


Lemma bwd_prefix : forall {X Y : Type} (e : IIST X Y) (ys ys' : list Y) (xs : list X),
  prefix ys' ys -> bwd e ys = Some xs -> exists xs', bwd e ys' = Some xs' /\ prefix xs' xs.
induction e; simpl.
- intro ys; revert a; induction ys; intros; simpl in *; inversion H; subst; simpl.
  + exists nil; split; auto; now constructor.
  + exists nil; split; auto; now constructor.
  + destruct (backward X Y (p a1) a); simpl in *; try now inversion H0.
    destruct (bwd_mapfold p a0 (a0 a1 x) ys) as [l | ] eqn: H4; try now inversion H0.
    destruct IHys with (a := a0 a1 x) (ys' := l1) (xs := l); auto.
    destruct H1.
    exists (x :: x0).
    split.
    * rewrite H1; reflexivity.
    * inversion H0; subst.
      constructor; now auto.
- intros; inversion H; subst; simpl.
  + exists nil; split; auto; now constructor.
  + destruct (equiv_one_dec a); inversion H0; subst.
    exists l1; split; now auto.
- intros.
  exists (slide x ys'); split; auto.
  inversion H0; subst.
  apply prefix_slide; now auto.
- intros.
  assert (He2 := IHe2 ys ys'); clear IHe2.
  destruct (bwd e2 ys) as [zs | ]; simpl in *; try now inversion H0.
  destruct (He2 zs) as [zs' [H1 H2]]; auto; clear He2.
  destruct (IHe1 zs zs' xs) as [xs' [H3 H4]]; auto; clear IHe1.
  exists xs'; split; auto.
  rewrite H1; simpl; rewrite H3; reflexivity.
- intros.
  destruct (split ys) as [y1s y2s] eqn: Hy12s.
  destruct (split ys') as [y1s' y2s'] eqn: Hy12s'.
  destruct (bwd e1 y1s) as [x1s | ] eqn: H1; simpl in H0; try now inversion H0.
  destruct (bwd e2 y2s) as [x2s | ] eqn: H2; simpl in H0; inversion H0; subst.
  destruct (split_prefix _ _ y1s y2s y1s' y2s' H).
  * rewrite Hy12s; now auto.
  * rewrite Hy12s'; now auto.
  * destruct (IHe1 _ _ _ H3 H1) as [ x1s' [He1 He1p]]; clear IHe1.
    destruct (IHe2 _ _ _ H4 H2) as [ x2s' [He2 He2p]]; clear IHe2.
    exists (combine x1s' x2s').
    rewrite He1, He2; simpl.
    split; auto.
    apply combine_prefix; now auto.
Qed.


Theorem fwd_bwd : forall {X Y : Type} (e : IIST X Y) (xs : list X) (ys : list Y),
  fwd e xs = Some ys ->
    exists xs', bwd e ys = Some xs' /\ prefix xs' xs.
induction e; intros; simpl in *.
- revert a ys H.
  induction xs as [ | x xs ]; intros a ys Hfwd; simpl in *.
  + inversion Hfwd; subst; simpl.
    exists nil. split; now constructor.
  + destruct (forward X Y (p a) x) as [y | ] eqn: Hy; simpl in Hfwd; try now inversion Hfwd.
    destruct (fwd_mapfold p a0 (a0 a x) xs) as [ys' | ] eqn: Hys'; simpl in Hfwd; try now inversion Hfwd.
    destruct (IHxs (a0 a x) ys' Hys') as [xs' [ Hxs' Hxsp ]].
    exists (x :: xs').
    split.
    * inversion Hfwd; subst.
      simpl.
      assert (backward X Y (p a) y = Some x) as Hb.
      {
        apply (invertible _ _ (p a)).
        now auto.
      }
      rewrite Hb; simpl.
      rewrite Hxs'; reflexivity.
    * constructor; now auto.
- inversion H; subst; clear H.
  destruct xs as [ | x' xs ]; simpl.
  + exists nil. split; now constructor.
  + destruct (equiv_one_dec x) as [ e1 | e1 ].
    * exists (slide x' xs). split; auto.
      now apply slide_prefix.
    * elim e1; now auto.
- destruct xs as [ | x' xs ]; simpl in H.
  + inversion H; subst; simpl.
    exists nil. split; now constructor.
  + destruct (equiv_one_dec x') as [ e1 | e1 ]; inversion H; subst.
    exists (slide x' ys).
    split; auto.
    now apply slide_prefix.
- destruct (fwd e1 xs) as [zs | ] eqn: H0; simpl in H; try now inversion H.
  destruct (IHe2 zs ys H) as [ zs' [ H1 H2 ]]; clear IHe2.
  rewrite H1; simpl.
  destruct (IHe1 xs zs H0) as [ xs'' [ H3 H4 ]]; clear IHe1.
  destruct (bwd_prefix e1 zs zs' xs'' H2 H3) as [ xs' [ H5 H6 ]].
  exists xs'.
  split; auto.
  apply prefix_transitive with (l2 := xs''); now auto.
- destruct (split xs) as [x1s x2s] eqn: Hx12s.
  destruct (split ys) as [y1s y2s] eqn: Hy12s.
  destruct (fwd e1 x1s) as [y1s' | ] eqn: H0; simpl in H; try now inversion H.
  destruct (IHe1 x1s y1s' H0) as [ x1s' [ H1 H2 ]]; clear IHe1.
  destruct (fwd e2 x2s) as [y2s' | ] eqn: H3; simpl in H; try now inversion H.
  destruct (IHe2 x2s y2s' H3) as [ x2s' [ H4 H5 ]]; clear IHe2.
  inversion H; subst; clear H.
  destruct (split_combine_prefix _ _ _ _ Hy12s) as [ H6 H7 ].
  destruct (bwd_prefix _ _ _ _ H6 H1) as [ x1s'' [ H8 H9 ]].
  rewrite H8; simpl.
  destruct (bwd_prefix _ _ _ _ H7 H4) as [ x2s'' [ H10 H11 ]].
  rewrite H10; simpl.
  exists (combine x1s'' x2s'').
  split; auto.
  apply prefix_transitive with (combine x1s' x2s').
  + apply combine_prefix; now auto.
  + apply prefix_transitive with (combine x1s x2s).
    * apply combine_prefix; now auto.
    * rewrite (split_combine xs Hx12s).
      now apply prefix_reflexive.
Qed.



Theorem bwd_fwd : forall {X Y : Type} (e : IIST X Y) (ys : list Y) (xs : list X),
  bwd e ys = Some xs ->
    exists ys', fwd e xs = Some ys' /\ prefix ys' ys.
induction e; intros; simpl in *.
- revert a xs H.
  induction ys as [ | y ys ]; intros a xs Hbwd; simpl in *.
  + inversion Hbwd; subst; simpl.
    exists nil. split; now constructor.
  + destruct (backward X Y (p a) y) as [x | ] eqn: Hx; simpl in Hbwd; try now inversion Hbwd.
    destruct (bwd_mapfold p a0 (a0 a x) ys) as [xs' | ] eqn: Hxs'; simpl in Hbwd; try now inversion Hbwd.
    destruct (IHys (a0 a x) xs' Hxs') as [ys' [ Hys' Hysp ]].
    exists (y :: ys').
    split.
    * inversion Hbwd; subst.
      simpl.
      assert (forward X Y (p a) x = Some y) as Ha.
      {
        apply (invertible _ _ (p a)).
        now auto.
      }
      rewrite Ha; simpl.
      rewrite Hys'; reflexivity.
    * constructor; now auto.
- destruct ys as [ | y' ys ]; simpl in H.
  + inversion H; subst; simpl.
    exists nil. split; now constructor.
  + destruct (equiv_one_dec y') as [ e1 | e1 ]; inversion H; subst.
    exists (slide y' xs).
    split; auto.
    now apply slide_prefix.
- inversion H; subst; clear H.
  destruct ys as [ | y' ys ]; simpl.
  + exists nil. split; now constructor.
  + destruct (equiv_one_dec x) as [ e1 | e1 ].
    * exists (slide y' ys). split; auto.
      now apply slide_prefix.
    * elim e1; now auto.
- destruct (bwd e2 ys) as [zs | ] eqn: H0; simpl in H; try now inversion H.
  destruct (IHe1 zs xs H) as [ zs' [ H1 H2 ]]; clear IHe1.
  rewrite H1; simpl.
  destruct (IHe2 ys zs H0) as [ ys'' [ H3 H4 ]]; clear IHe2.
  destruct (fwd_prefix e2 zs zs' ys'' H2 H3) as [ ys' [ H5 H6 ]].
  exists ys'.
  split; auto.
  apply prefix_transitive with (l2 := ys''); now auto.
- destruct (split ys) as [y1s y2s] eqn: Hy12s.
  destruct (split xs) as [x1s x2s] eqn: Hx12s.
  destruct (bwd e1 y1s) as [x1s' | ] eqn: H0; simpl in H; try now inversion H.
  destruct (IHe1 y1s x1s' H0) as [ y1s' [ H1 H2 ]]; clear IHe1.
  destruct (bwd e2 y2s) as [x2s' | ] eqn: H3; simpl in H; try now inversion H.
  destruct (IHe2 y2s x2s' H3) as [ y2s' [ H4 H5 ]]; clear IHe2.
  inversion H; subst; clear H.
  destruct (split_combine_prefix _ _ _ _ Hx12s) as [ H6 H7 ].
  destruct (fwd_prefix _ _ _ _ H6 H1) as [ y1s'' [ H8 H9 ]].
  rewrite H8; simpl.
  destruct (fwd_prefix _ _ _ _ H7 H4) as [ y2s'' [ H10 H11 ]].
  rewrite H10; simpl.
  exists (combine y1s'' y2s'').
  split; auto.
  apply prefix_transitive with (combine y1s' y2s').
  + apply combine_prefix; now auto.
  + apply prefix_transitive with (combine y1s y2s).
    * apply combine_prefix; now auto.
    * rewrite (split_combine ys Hy12s).
      now apply prefix_reflexive.
Qed.




End IIST.



Section Math_IIST.
(* IISTの数学的定義について *)

Definition MST X Y := list X -> option (list Y).

Definition MIST {X Y} (mst : MST X Y) :=
 forall xs xs' ys,
  prefix xs' xs
  -> mst xs = Some ys
  -> exists ys', mst xs' = Some ys' /\ prefix ys' ys.


Definition d_MST {X Y} (mst : MST X Y) d :=
 forall xs ys,
  mst xs = Some ys
  -> length xs - d = length ys.


Definition d_MIST {X Y} (mst : MST X Y) d :=
 MIST mst /\ d_MST mst d.


Definition MInv {X Y} (mst : MST X Y) (inv : MST Y X) := 
 forall xs ys, mst xs = Some ys
 -> exists xs', inv ys = Some xs' /\ prefix xs' xs.


Definition MIIST {X Y} (mst : MST X Y) (inv : MST Y X) :=
 MIST mst /\ MInv mst inv.


Definition d_MIIST {X Y} (mst : MST X Y) (inv : MST Y X) d' :=
 MIIST mst inv /\ d_MIST inv d'.


Definition d_d'_MIIST_pair {X Y} (mst : MST X Y) (inv : MST Y X) d d' :=
 d_MIST mst d /\ d_MIIST mst inv d'.


Lemma d_d'_MIIST_pair_min :
 forall X Y (mst : MST X Y) inv d d',
  d_d'_MIIST_pair mst inv d d'
  <-> MIST mst /\ d_MST mst d /\ MInv mst inv /\ MIST inv /\ d_MST inv d'.
unfold d_d'_MIIST_pair, d_MIIST, d_MIST, MIIST, MIST, MInv.
intuition.
Qed.



End Math_IIST.




Section IIST_Math.

Lemma IIST_MIST :
 forall X Y (e : IIST X Y),
  MIST (fwd e).
unfold MIST.
intros; eapply fwd_prefix; eauto.
Qed.

Lemma IIST_d_MST :
 forall X Y (e : IIST X Y),
  d_MST (fwd e) (delay_fwd e).
unfold d_MST.
intros; apply fwd_length_delay; now auto.
Qed.

Lemma IIST_MInv :
 forall X Y (e : IIST X Y),
  MInv (fwd e) (bwd e).
unfold MInv.
intros; apply fwd_bwd; now auto.
Qed.

Lemma IIST_bwd_MInv :
 forall X Y (e : IIST X Y),
  MInv (bwd e) (fwd e).
unfold MInv.
intros; apply bwd_fwd; now auto.
Qed.

Lemma IIST_bwd_MIST :
 forall X Y (e : IIST X Y),
  MIST (bwd e).
unfold MIST.
intros; eapply bwd_prefix; eauto.
Qed.

Lemma IIST_bwd_d_MST :
 forall X Y (e : IIST X Y),
  d_MST (bwd e) (delay_bwd e).
unfold d_MST.
intros; apply bwd_length_delay; now auto.
Qed.



Theorem IIST_is_d_d'_MIIST_pair :
 forall X Y (e : IIST X Y),
  d_d'_MIIST_pair (fwd e) (bwd e) (delay_fwd e) (delay_bwd e).
intros X Y e.
apply d_d'_MIIST_pair_min.
split; [ now apply IIST_MIST
| split; [ now apply IIST_d_MST
| split; [ now apply IIST_MInv
| split; [ now apply IIST_bwd_MIST
         | now apply IIST_bwd_d_MST]]]].
Qed.

Theorem inv_IIST_is_d_d'_MIIST_pair :
 forall X Y (e : IIST X Y),
  d_d'_MIIST_pair (bwd e) (fwd e) (delay_bwd e) (delay_fwd e).
intros X Y e.
apply d_d'_MIIST_pair_min.
split; [ now apply IIST_bwd_MIST
| split; [ now apply IIST_bwd_d_MST
| split; [ now apply IIST_bwd_MInv
| split; [ now apply IIST_MIST
         | now apply IIST_d_MST]]]].
Qed.



End IIST_Math.



Section IIST_descriptive.


Definition option_wrap {A} (a : option A) : option (option A) :=
match a with
| None => None
| Some a => Some (Some a)
end.

Search ({_ <= _} + {_ > _}).


Definition IIST_f1 {X Y}
                   (mst : MST X Y) d (xs : list X) x : option (option Y * option X) :=
 if Compare_dec.le_gt_dec d (length xs) then
   option_bind (mst (xs ++ [x]))
    (fun ys =>
      option_bind (last ys)
       (fun y => Some (Some y, Some x))) (* このペアのせいでyのdecidable equalityがいる？ *)
 else Some (None, Some x).


Definition IIST_f1' {X Y} `{EqDec Y eq} (* f1と違いこちらはequalityの判定が必要 *)
                    (mst : MST X Y) d (xs : list X) oy_ox : option X :=
 if Compare_dec.le_gt_dec d (length xs) then
   match oy_ox with
   | (None, _) => None (* 十分な長さがあるので値があるはず *)
   | (_, None) => None (* これ自体がxとしてNoneを出すことはない *)
   | (Some y, Some x) =>
       option_bind (mst (xs ++ [x])) (* 逆行に失敗したときにNoneを返さなければならないので計算が必要 *)
        (fun ys =>
          option_bind (last ys)
           (fun y' => if equiv_dec y y' then Some x else None))
   end
 else match oy_ox with
      | (None, Some x) => Some x
      | (Some _, _) => None
      | (_, None) => None
      end.


Program Definition IIST_inv_f1 {X Y} `{E : EqDec Y eq}
                               (mst : MST X Y) d (Hd : d_MST mst d) xs : partial_invertible_function X (option Y * option X) :=
{| forward := IIST_f1 mst d xs;
   backward := IIST_f1' mst d xs
|}.
Next Obligation.
unfold IIST_f1, IIST_f1', equiv_dec.
destruct (Compare_dec.le_gt_dec d (length xs)) as [Hlen | Hlen]; simpl.
2: {
  split; intro Hsome.
  + inversion Hsome; now auto.
  + destruct o, o0; inversion Hsome.
    now auto.
}
destruct o as [y | ].
2: {
  destruct (mst (xs ++ [a])); simpl.
  + destruct (last l); simpl; split; intro Hcon; now inversion Hcon.
  + split; intro Hcon; now inversion Hcon.
}
destruct o0 as [x | ].
2: {
  destruct (mst (xs ++ [a])); simpl.
  + destruct (last l); simpl; split; intro Hcon; now inversion Hcon.
  + split; intro Hcon; now inversion Hcon.
}
destruct (mst (xs ++ [a])) as [ys | ] eqn: Hmst; simpl.
2: {
  split; intro Hcon.
  + now inversion Hcon.
  + destruct (mst (xs ++ [x])) as [ys | ] eqn: Hmst1; simpl in Hcon.
    - destruct (last ys); simpl in Hcon; try now inversion Hcon.
      destruct (E y y0); simpl in Hcon; inversion Hcon.
      subst.
      rewrite Hmst in Hmst1; now inversion Hmst1.
    - now inversion Hcon.
}
assert (length ys > 0) as Hylen.
{
  unfold d_MST in Hd.
  apply Hd in Hmst.
  rewrite app_length in Hmst.
  simpl in Hmst.
  lia.
}
apply last_Some in Hylen.
destruct Hylen as [y' Hlast].
rewrite Hlast; simpl.
split; intro Hxy.
+ inversion Hxy; subst.
  rewrite Hmst; simpl.
  rewrite Hlast; simpl.
  destruct (E y y) as [Hy | Hy]; auto.
  elim Hy; now auto.
+ destruct (mst (xs ++ [x])) as [ys' |] eqn: Hys'; simpl in Hxy; try now inversion Hxy.
  destruct (last ys') as [y'' | ] eqn: Hy''; simpl in Hxy; try now inversion Hxy.
  destruct (E y y'') as[e | e]; simpl in Hxy; inversion Hxy; unfold equiv in e; subst.
  rewrite Hmst in Hys'; inversion Hys'; subst.
  rewrite Hlast in Hy''; inversion Hy''.
  now auto.
Qed.


Definition IIST_g1 {X} (xs : list X) x : list X := xs ++ [x].


Definition IIST_e1 {X Y} `{E : EqDec Y eq}
                               (mst : MST X Y) d (Hd : d_MST mst d) :=
 IIST_mapfold [] (IIST_inv_f1 mst d Hd) IIST_g1.




Theorem d_d'_MIIST_IIST :
 forall X Y (mst : MST X Y) d d',
  (exists inv, d_d'_MIIST_pair mst inv d d')
  -> exists e,
      forall xs, mst xs = fwd e xs
      /\ delay_fwd e = d
      /\ delay_bwd e = d'.
Admitted.
(* XやYに関するdecidable equalityがいるかも（fold_mapに使う可逆関数の定義に） *)









Definition MIST_coord {X Y} (mst : MST X Y) (xs : list X) : option Y :=
option_bind (mst xs) last.


Definition inc_coord_elem {X Y} (mst : MST X Y) coord :=
 forall xs x y,
  (exists ys, mst (xs ++ [x]) = Some (ys ++ [y]))
  <-> coord (xs ++ [x]) = Some y.


Definition inc_coord_none {X Y} (mst : MST X Y) (coord : list X -> option Y) d :=
 forall xs,
  mst xs = None \/ length xs <= d
  <-> coord xs = None.


Theorem d_MIST_coord_correct :
 forall X Y (mst : MST X Y) d,
  d_MIST mst d
  ->
    let coord := MIST_coord mst in
     inc_coord_elem mst coord
     /\
     inc_coord_none mst coord d.
unfold inc_coord_elem, inc_coord_none, MIST_coord.
intros X Y mst d [Hmist Hd_mst]; split; intros; split; intro.
+ destruct H as [ys H]; rewrite H; simpl. now apply last_correct.
+ destruct (mst (xs ++ [x])); simpl in H; try now inversion H.
  apply last_correct' in H.
  destruct H as [l' H]; exists l'; rewrite H; now auto.
+ destruct H.
  - rewrite H; simpl; now auto.
  - destruct (mst xs) as [ys | ] eqn: H0; simpl; auto.
    assert (H1 := Hd_mst xs ys H0).
    destruct ys; auto.
    simpl in H1; lia.
+ destruct (mst xs) as [ys | ] eqn: H0; auto.
  right.
  simpl in H.
  assert (H1 := Hd_mst _ _ H0).
  destruct ys; simpl in *; inversion H.
  lia.
Qed.



Fixpoint coord_MIST {X Y} (coord : list X -> option Y) (xt : list X) (xs : list X) : option (list Y) :=
 match xs with
 | [] => Some []
 | x :: xs' =>
    option_bind (coord (xt ++ [x]))
      (fun y => option_bind (coord_MIST coord (xt ++ [x]) xs')
         (fun ys => Some (y :: ys)))
end.

(* これって正しい？d_MIST（の一部）になってる？ヘッダとしてxtを持っている列変換になると思うのだけど *)


Fixpoint coord_d_MIST {X Y} d (coord : list X -> option Y) (xt : list X) : MST X Y :=
 fun xs =>
   match d with
   | O => coord_MIST coord xt xs (* 先頭dをxtにしてリストを計算 *)
   | S d' =>
      match xs with
      | [] => Some []
      | x :: xs' => coord_d_MIST d' coord (xt ++ [x]) xs'
      end
   end.




End IIST_descriptive.

