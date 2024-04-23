Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Coq.Classes.EquivDec.

Require Import IIST.OptionBind.
Require Import IIST.PartInvFun.
Require Import IIST.EqOneDec.


Section app_length_destruct.

Context {A : Type}.

Theorem app_length_destruct :
 forall (l : list A) n,
  n <= length l
  -> exists l1 l2, l = l1 ++ l2 /\ length l1 = n.
intro l; induction l as [ | a l Hl]; simpl; intros n Hlen.
+ exists [], []; simpl; split; auto; lia.
+ destruct n.
  - exists [], (a :: l); simpl; split; now auto.
  - destruct (Hl n) as [l1 [l2 [Heq Hl1]]].
    * lia.
    * exists (a :: l1), l2; subst; simpl; split; now auto.
Qed.


End app_length_destruct.

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
 forall l1 l2, prefix l1 (l1 ++ l2).
induction l1; intros; simpl in *; subst; try constructor; now auto.
Qed.

Theorem app_prefix' :
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


Theorem prefix_nil_r :
 forall l,
  prefix l [] -> l = [].
intros l H; now inversion H.
Qed.


Theorem prefix_inv_head :
 forall l l1 l2,
  prefix (l ++ l1) (l ++ l2)
  -> prefix l1 l2.
intros l l1 l2 H.
induction l; simpl in H; auto.
inversion H; subst.
now auto.
Qed.



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


Theorem prefix_length_det :
 forall al1 al2 al3,
  prefix al1 al3 ->
   prefix al2 al3 ->
   length al1 = length al2 ->
   al1 = al2.
intro al1.
induction al1 as [ | a al1 IHal]; intros al2 al3 H1 H2 Hl.
+ simpl in Hl.
  destruct al2; [now auto | simpl in Hl; now inversion Hl].
+ simpl in Hl.
  inversion H1; subst.
  inversion H2; subst; simpl in Hl; inversion Hl; subst.
  erewrite IHal; eauto.
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


Section combine.

Theorem combine_app_length_ge :
 forall A B (l1 l2 : list A) (l3 : list B),
  length l1 >= length l3 -> combine (l1 ++ l2) l3 = combine l1 l3.
intros A B l1; induction l1 as [ | a l1 IHl1]; intros l2 l3 Hlen; destruct l3; simpl; auto.
+ destruct l2; now auto.
+ simpl in Hlen; lia.
+ simpl in Hlen.
  rewrite IHl1; auto.
  lia.
Qed.


Theorem combine_app_length_le :
 forall A B (l1 : list A) (l2 l3 : list B),
  length l1 <= length l2 -> combine l1 (l2 ++ l3) = combine l1 l2.
intros A B l1; induction l1 as [ | a l1 IHl1]; intros l2 l3 Hlen; destruct l2; simpl; auto.
+ destruct l3; auto.
  simpl in Hlen; lia.
+ simpl in Hlen.
  rewrite IHl1; auto.
  lia.
Qed.



Theorem combine_app_app :
 forall A B (l1 l2 : list A) (l3 l4 : list B),
  length l1 = length l3
  -> combine (l1 ++ l2) (l3 ++ l4) = combine l1 l3 ++ combine l2 l4.
intros A B l1; induction l1 as [ | a l1 IHl1]; intros l2 l3 l4 Hlen; destruct l3; simpl in *; auto; inversion Hlen; subst.
rewrite IHl1; now auto.
Qed.


End combine.





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

Open Scope part_inv_fun_scope.
Require Import IIST.IISTData.

Section IIST.




Fixpoint fwd_mapfold {A X Y : Type} (f : A -> X <~~> Y) (g : A -> X -> A) (a : A) xs : option (list Y) :=
match xs with
| nil => Some nil
| x :: xs' =>
   option_bind ((forward _ _ (f a)) x) (fun y => option_bind (fwd_mapfold f g (g a x) xs') (fun ys => Some (cons y ys)))
end.



Lemma fwd_mapfold_app :
 forall A X Y (f : A -> X <~~> Y) g a xs1 xs2,
  fwd_mapfold f g a (xs1 ++ xs2) =
    option_bind (fwd_mapfold f g a xs1)
     (fun ys1 =>
       option_bind (fwd_mapfold f g (fold_left g xs1 a) xs2)
        (fun ys2 => Some (ys1 ++ ys2))).
intros A X Y f g a xs1 xs2.
revert a.
induction xs1 as [ | x xs1 Hxs1]; intros a; simpl.
+ destruct (fwd_mapfold f g a xs2); simpl; now auto.
+ destruct (forward X Y (f a) x) as [y | ]; simpl; auto.
  rewrite Hxs1.
  destruct (fwd_mapfold f g (g a x) xs1) as [ys1 | ]; simpl; auto.
  destruct (fwd_mapfold f g (fold_left g xs1 (g a x)) xs2) as [ys2 | ]; simpl; now auto.
Qed.


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

Definition MIST_nil {X Y} (mst : MST X Y) :=
 ~(mst [] = None).

Definition MIST {X Y} (mst : MST X Y) :=
 MIST_nil mst /\
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



Lemma d_MST_nil :
 forall X Y (mst : MST X Y) d xs ys,
  d_MST mst d
  -> length xs <= d
  -> mst xs = Some ys
  -> ys = nil.
intros X Y mst d xs ys Hd Hlen Hmst.
apply length_zero_iff_nil.
apply Hd in Hmst.
lia.
Qed.



Lemma MIST_None_ind :
 forall X Y (mst : MST X Y) xs xs',
  MIST mst
  -> mst xs = None
  -> mst (xs ++ xs') = None.
intros X Y mst xs xs' Hist H.
destruct Hist as [_ Hist].
destruct (mst (xs ++ xs')) as [ys | ] eqn: Hys; auto.
destruct Hist with (xs ++ xs') xs ys as [ys' [Hys' _]]; auto.
+ now apply app_prefix.
+ rewrite H in Hys'; now inversion Hys'.
Qed.


Lemma d_MIST_length_case :
 forall X Y (mst : MST X Y) d xs ys x,
  MIST mst
  -> d_MST mst d
  -> length xs >= d
  -> mst xs = Some ys
  -> mst (xs ++ [x]) = None
  \/ exists y, mst (xs ++ [x]) = Some (ys ++ [y]).
intros X Y mst d xs ys x Hist Hd Hlen Hsome.
destruct (mst (xs ++ [x])) as [ys' | ] eqn: Hys'; auto.
right.
destruct Hist as [_ Hist].
destruct Hist with (xs ++ [x]) xs ys' as [ys'' [Hys'' Hpre]]; auto.
+ now apply app_prefix.
+ destruct (prefix_app _ _ Hpre) as [y0 Hy0].
  subst.
  rewrite Hys'' in Hsome; inversion Hsome; subst.
  assert (length y0 = 1) as Hy0l.
  {
    unfold d_MST in Hd.
    assert (Hlys := Hd _ _ Hys'').
    assert (Hlys' := Hd _ _ Hys').
    repeat rewrite app_length in Hlys'; simpl in Hlys'.
    lia.
  }
  destruct y0 as [ | y]; simpl in Hy0l; inversion Hy0l.
  destruct y0 as [ | y']; simpl in H0; inversion H0.
  exists y; now auto.
Qed.


Lemma d_MIST_oneapp :
 forall X Y (mst : MST X Y) d xs ys x,
  MIST mst
  -> d_MST mst d
  -> length xs >= d
  -> mst (xs ++ [x]) = Some ys
  -> exists y ys', ys = ys' ++ [y] /\ mst xs = Some ys'.
intros X Y mst d xs ys x Hist Hd Hlen Hxs.
destruct Hist as [_ Hist].
assert (H := app_prefix xs [x]).
induction ys as [ | y ys _] using list_inv_ind.
+ apply Hd in Hxs.
  rewrite app_length in Hxs; simpl in Hxs.
  lia.
+ exists y, ys.
  split; auto.
  assert (Hl := Hd _ _ Hxs).
  repeat rewrite app_length in Hl; simpl in Hl.
  apply Hist with (xs' := xs) in Hxs.
  - destruct Hxs as [ys' [H' Hpre]].
    rewrite H'.
    rewrite (prefix_length_det _ ys _ Hpre); auto.
    * now apply app_prefix.
    * apply Hd in H'.
      lia.
  - now apply app_prefix.
Qed.



End Math_IIST.




Section IIST_Math.

Lemma IIST_fwd_MIST_nil :
 forall X Y (e : IIST X Y),
  fwd e [] = Some [].
induction e; eauto; simpl.
+ rewrite IHe1; simpl; now auto.
+ rewrite IHe1; simpl.
  rewrite IHe2; simpl; now auto.
Qed.

Lemma IIST_bwd_MIST_nil :
 forall X Y (e : IIST X Y),
  bwd e [] = Some [].
induction e; eauto; simpl.
+ rewrite IHe2; simpl; now auto.
+ rewrite IHe1; simpl.
  rewrite IHe2; simpl; now auto.
Qed.


Lemma IIST_MIST :
 forall X Y (e : IIST X Y),
  MIST (fwd e).
unfold MIST.
intros; split.
+ intro H.
  rewrite IIST_fwd_MIST_nil with X Y e in H.
  now inversion H.
+ eapply fwd_prefix; now eauto.
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
intros; split.
+ intro H.
  rewrite IIST_bwd_MIST_nil with X Y e in H.
  now inversion H.
+ eapply bwd_prefix; now eauto.
Qed.

Lemma IIST_bwd_d_MST :
 forall X Y (e : IIST X Y),
  d_MST (bwd e) (delay_bwd e).
unfold d_MST.
intros; apply bwd_length_delay; now auto.
Qed.


Lemma IIST_fwd_None_app :
 forall X Y (e : IIST X Y) xs xs',
  fwd e xs = None -> fwd e (xs ++ xs') = None.
intros X Y e xs xs'.
apply MIST_None_ind.
now apply IIST_MIST.
Qed.


(** First theorem:
    for any FIRSD e,
     a pair of its forward-semantics and backward-semantics is
     a (d, d')-FIRST pair,
     and a pair of backward-semantics and forward-semantics is
     a (d', d)-FIRST pair.
**)
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

Theorem inv_IIST_is_d'_d_MIIST_pair :
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

(* 計算可能性のoptionと見分けるためにmaybeを定義して、データの余計な要素はこちらで表現 *)
#[universes(template)]
Inductive maybe (A : Type) : Type :=
| Just : A -> maybe A
| Nothing : maybe A.

Arguments Just {A} a.
Arguments Nothing {A}.


Definition option_wrap {A} (a : option A) : option (maybe A) :=
match a with
| None => None
| Some a => Some (Just a)
end.


Definition maybe_option {A} (m : maybe A) : option A :=
 match m with
 | Just a => Some a
 | Nothing => None
 end.


#[global]
Program Instance maybe_Nothing_eqdec {A} : @EqOneDec (maybe A) Nothing.
Next Obligation.
destruct b as [ a | ].
+ right; intro H; now inversion H.
+ left; now auto.
Defined.


#[global]
Instance option_Some_None_eqdec {A} : @EqOneDec (option (maybe A)) (Some Nothing) :=
 eqdec_Some_eqdec Nothing.



Fixpoint nothing_list {A} len : list (maybe A) :=
match len with
| O => nil
| S len => Nothing :: nothing_list len
end.


Lemma nothing_list_len :
 forall A n, length (@nothing_list A n) = n.
induction n; intros; simpl in *; auto.
Qed.

Lemma nothing_list_app :
 forall A m n, @nothing_list A (m + n) = nothing_list m ++ nothing_list n.
intros A m n; induction m as [ | m IHm]; simpl; try rewrite IHm; now auto.
Qed.


Lemma combine_nothing_list_l :
 forall A B n (xs : list (maybe A)) (ys : list B),
  length ys <= n
  -> combine (nothing_list n ++ xs) ys = combine (nothing_list (length ys)) ys.
intros A B n xs ys Hlen.
rewrite combine_app_length_ge.
+ assert (n = length ys + (n - length ys)) as Hn by lia.
  rewrite Hn.
  rewrite (nothing_list_app _ (length ys) (n - length ys)).
  rewrite combine_app_length_ge; auto.
  rewrite nothing_list_len; now auto.
+ rewrite nothing_list_len; lia.
Qed.

Lemma combine_nothing_list_r :
 forall A B n (xs : list A) (ys : list (maybe B)),
  length xs <= n
  -> combine xs (nothing_list n ++ ys) = combine xs (nothing_list (length xs)).
intros A B n xs ys Hlen.
rewrite combine_app_length_le.
+ assert (n = length xs + (n - length xs)) as Hn by lia.
  rewrite Hn.
  rewrite (nothing_list_app _ (length xs) (n - length xs)).
  rewrite combine_app_length_le; auto.
  rewrite nothing_list_len; now auto.
+ rewrite nothing_list_len; lia.
Qed.


Definition IIST_f1 {X Y}
                   (mst : MST X Y) d (xs : list X) x : option (maybe Y * X) :=
 option_bind (mst (xs ++ [x]))
  (fun ys =>
    if Compare_dec.le_gt_dec d (length xs) then
      option_bind (last ys)
       (fun y => Some (Just y, x)) (* このペアのせいでyのdecidable equalityがいる？ *)
    else Some (Nothing, x)).


Definition IIST_f1' {X Y} `{EqDec Y eq} (* f1と違いこちらはequalityの判定が必要 *)
                    (mst : MST X Y) d (xs : list X) (my_x : maybe Y * X) : option X :=
 let (my, x) := my_x in
 option_bind (mst (xs ++ [x])) (* 逆行に失敗したときにNoneを返すのでmyを使わずこちらで対処 *)
  (fun ys =>
    if Compare_dec.le_gt_dec d (length xs) then
      match my with
      | Just y =>
         option_bind (last ys)
          (fun y' => if equiv_dec y y' then Some x else None)
      | Nothing => None
      end
    else
      match my with  (* 短いのでyはNothingのはず *)
      | Just _ => None
      | Nothing => Some x
      end).


Program Definition IIST_pinv_f1 {X Y} `{E : EqDec Y eq}
                               (mst : MST X Y) d (Hd : d_MST mst d) xs : partial_invertible_function X (maybe Y * X) :=
{| forward := IIST_f1 mst d xs;
   backward := IIST_f1' mst d xs
|}.
Next Obligation.
unfold IIST_f1, IIST_f1', equiv_dec.
split; intro Hsome.
+ destruct (mst (xs ++ [a])) as [ys | ] eqn: Hmst; simpl in Hsome; try now inversion Hsome.
  destruct (Compare_dec.le_gt_dec d (length xs)) as [e | e]; simpl in *.
  - destruct (last ys) as [y | ] eqn: Hlast; simpl in Hsome; inversion Hsome; subst.
    rewrite Hmst; simpl; rewrite Hlast; simpl.
    destruct (E y y) as [e' | e']; auto; elim e'; now auto.
  - inversion Hsome; subst.
    rewrite Hmst; simpl; now auto.
+ assert (x = a).
  {
    destruct (mst (xs ++ [x])) as [ys | ]; simpl in Hsome; try now inversion Hsome.
    destruct (Compare_dec.le_gt_dec d (length xs)); simpl in Hsome.
    + destruct m as [y | ]; try now inversion Hsome.
      destruct (last ys) as [y' | ]; simpl in Hsome; try now inversion Hsome.
      destruct (E y y') as [e | e]; simpl in Hsome; inversion Hsome; now auto.
    + destruct m as [y | ]; now inversion Hsome.
  }
  subst.
  destruct (mst (xs ++ [a])) as [ys | ]; simpl in *; try now inversion Hsome.
  destruct (Compare_dec.le_gt_dec d (length xs)) as [e | e].
  - destruct m; try now inversion Hsome.
    destruct (last ys) as [y' | ]; try now inversion Hsome.
    simpl in *.
    destruct (E y y') as [e' | e']; simpl in Hsome; try now inversion Hsome.
    unfold equiv in e'; subst; auto.
  - destruct m; now inversion Hsome.
Qed.


Definition IIST_g1 {X} (xs : list X) x : list X := xs ++ [x].


Definition IIST_e1 {X Y} `{E : EqDec Y eq}
                          (mst : MST X Y) d (Hd : d_MST mst d) : IIST X (maybe Y * X) :=
 IIST_mapfold [] (IIST_pinv_f1 mst d Hd) IIST_g1.



Lemma fold_left_IIST_g1_app :
 forall X (xs1 xs2: list X), fold_left IIST_g1 xs1 xs2 = xs2 ++ xs1.
intros X xs1.
induction xs1 as [ | x xs1 Hxs1]; intro xs2; simpl.
+ rewrite app_nil_r; now auto.
+ rewrite Hxs1.
  unfold IIST_g1.
  rewrite <- app_assoc.
  simpl; now auto.
Qed.


Lemma IIST_e1_fwd_None :
 forall X Y `{E : EqDec Y eq} (mst : MST X Y) d Hd (Hist : MIST mst) xs,
  mst xs = None -> fwd (IIST_e1 mst d Hd) xs = None.
intros X Y E E' mst d Hd Hist xs.
unfold fwd; simpl.
induction xs as [ | x xs Hxs] using list_inv_ind; intro H; simpl.
+ destruct Hist as [Hist _].
  destruct Hist; now auto.
+ rewrite fwd_mapfold_app.
  rewrite fold_left_IIST_g1_app; simpl.
  unfold IIST_f1.
  rewrite H; simpl.
  destruct (fwd_mapfold (IIST_pinv_f1 mst d Hd) IIST_g1 [] xs); simpl; now auto.
Qed.


Lemma IIST_e1_fwd_Some :
 forall X Y `{E : EqDec Y eq} (mst : MST X Y) d Hd (Hist : MIST mst) xs ys,
  mst xs = Some ys ->
   fwd (IIST_e1 mst d Hd) xs = Some (combine (nothing_list d ++ map Just ys) xs).
intros X Y E E' mst d Hd Hist xs.
unfold fwd; simpl.
induction xs as [ | x xs Hxs] using list_inv_ind; simpl; intros ys H.
+ destruct (nothing_list d ++ map Just ys); simpl; now auto.
+ rewrite fwd_mapfold_app.
  unfold fwd_mapfold at 2; simpl.
  unfold IIST_f1; simpl.
  rewrite fold_left_IIST_g1_app; simpl.
  rewrite H; simpl.
  destruct (Compare_dec.le_gt_dec d (length xs)) as [e | e]; simpl.
  - destruct (d_MIST_oneapp _ _ mst d xs ys x) as [y [ys' [Heq Hx]]]; auto.
    subst.
    rewrite (Hxs _ Hx); simpl.
    rewrite last_correct; simpl.
    rewrite map_app.
    rewrite app_assoc.
    rewrite combine_app_app; simpl; auto.
    rewrite app_length.
    rewrite nothing_list_len.
    rewrite map_length.
    apply Hd in Hx.
    lia.
  - assert (ys = nil).
    {
      eapply d_MST_nil; eauto.
      rewrite app_length; simpl.
      lia.
    }
    subst; simpl.
    assert (mst xs = Some nil).
    {
      unfold MIST in Hist.
      destruct Hist as [_ Hist].
      destruct (Hist (xs ++ [x]) xs nil) as [ys [Hxs' Hpre]]; auto.
      + now apply app_prefix.
      + apply prefix_nil_r in Hpre.
        subst; now auto.
    }
    rewrite Hxs with (ys := nil); auto; simpl.
    assert (length (xs ++ [x]) = length xs + 1) as Hll by (now rewrite app_length).
    rewrite combine_nothing_list_l; try lia.
    rewrite combine_nothing_list_l; try lia.
    rewrite Hll.
    rewrite nothing_list_app; simpl.
    rewrite combine_app_app; simpl; auto.
    now apply nothing_list_len.
Qed.




(* e2のyはNothingが外に出ないのでここで処理 *)
Program Definition IIST_e2_1last {Y} : IIST (maybe Y) Y :=
 IIST_mapfold tt (fun u => {| forward := maybe_option; backward := fun y => Some (Just y); |}) (fun _ _ => tt).
Next Obligation.
unfold maybe_option.
destruct a; simpl; split; intro H; inversion H; now auto.
Qed.


Fixpoint IIST_e2_1 {Y} d : IIST (maybe Y) Y :=
 match d with
 | O => IIST_e2_1last
 | S d' => IIST_seqcomp (IIST_hasten Nothing) (IIST_e2_1 d')
 end.


Program Definition IIST_e2_2last {X} : IIST X (maybe X) :=
 IIST_mapfold tt (fun u => {| forward := fun x => Some (Just x); backward := maybe_option; |}) (fun _ _ => tt).
Next Obligation.
unfold maybe_option.
destruct b; simpl; split; intro H; inversion H; now auto.
Qed.


Fixpoint IIST_e2_2 {X} d' : IIST X (maybe X) :=
 match d' with
 | O => IIST_e2_2last
 | S d => IIST_seqcomp (IIST_e2_2 d) (IIST_delay Nothing)
 end.


Definition IIST_e2 {X Y} d d' : IIST (maybe Y * X) (Y * maybe X):=
 IIST_parcomp (IIST_e2_1 d) (IIST_e2_2 d').


Lemma IIST_e2_1_fwd_le :
 forall X d d',
  d' <= d
  -> fwd (IIST_e2_1 d) (@nothing_list X d') = Some [].
intros X d; induction d as [ | d Hd]; intros d' Hle; destruct d' as [ | d']; simpl.
+ now auto.
+ lia.
+ inversion Hle; subst.
  apply Hd in H0; simpl in H0.
  now auto.
+ apply Hd.
  lia.
Qed.

Lemma IIST_e2_1_fwd_ge :
 forall X d xs,
  fwd (IIST_e2_1 d) (@nothing_list X d ++ map Just xs) = Some xs.
intros X d; induction d as [ | d Hd]; intros xs; simpl.
+ induction xs as [ | x xs Hxs]; simpl; auto.
  rewrite Hxs; simpl; now auto.
+ now auto.
Qed.



Fixpoint nth_nothing_slide {X} (n : nat) (xs : list (maybe X)) : list (maybe X) :=
 match n with
 | O => xs
 | S n => slide Nothing (nth_nothing_slide n xs)
 end.

Lemma IIST_e2_2_fwd_nth_nothing :
 forall X d (xs : list X),
  fwd (IIST_e2_2 d) xs = Some (nth_nothing_slide d (map Just xs)).
intros X d; induction d as [ | d Hd]; intro xs; simpl.
+ induction xs as [ | x xs Hxs]; simpl; auto.
  rewrite Hxs; simpl.
  now auto.
+ rewrite Hd.
  simpl.
  now auto.
Qed.



Lemma nth_nothing_slide_prefix :
 forall X d (xs : list (maybe X)),
  prefix (nth_nothing_slide d xs) (nothing_list d ++ xs).
intros X d xs; induction d as [ | d Hd]; simpl.
+ now apply prefix_reflexive.
+ apply prefix_transitive with (l2 := Nothing :: (nth_nothing_slide d xs)).
  - now apply slide_prefix.
  - constructor.
    now auto.
Qed.


Lemma nth_nothing_slide_length :
 forall X d (xs : list (maybe X)),
  length (nth_nothing_slide d xs) = length xs.
intros X d xs; induction d as [ | d Hd]; simpl; auto.
rewrite <- slide_length.
now auto.
Qed.


Lemma IIST_e2_2_fwd :
 forall X d (xs : list X),
  exists mxs,
   fwd (IIST_e2_2 d) xs = Some mxs
   /\ prefix mxs (nothing_list d ++ map Just xs)
   /\ length mxs = length xs.
intros X d xs.
exists (nth_nothing_slide d (map Just xs)).
split; [ | split].
+ now apply IIST_e2_2_fwd_nth_nothing.
+ now apply nth_nothing_slide_prefix.
+ rewrite nth_nothing_slide_length.
  now apply map_length.
Qed.




Lemma IIST_e2_fwd :
 forall X Y (mst : MST X Y) d d' (Hd : d_MST mst d) (Hist : MIST mst) xs ys,
  mst xs = Some ys ->
   fwd (IIST_e2 d d') (combine (nothing_list d ++ map Just ys) xs)
    = Some (combine ys (nothing_list d' ++ map Just xs)).
intros X Y mst d d' Hd Hist xs ys H.
destruct (IIST_e2_2_fwd _ d' xs) as [mxs [Hfwd_2 [Hpre_2 Hlen_2]]].
destruct (Compare_dec.le_gt_dec (length xs) d).
+ rewrite combine_nothing_list_l; auto.
  simpl.
  rewrite combine_split.
  - rewrite IIST_e2_1_fwd_le; auto; simpl.
    assert (ys = nil).
    {
      apply length_zero_iff_nil.
      apply Hd in H.
      lia.
    }
    subst.
    assert (@combine Y _ [] (nothing_list d' ++ map Just xs) = nil) as Hl.
    {
      destruct (nothing_list d' ++ map Just xs); simpl; now auto.
    }
    rewrite Hl.
    rewrite Hfwd_2; simpl.
    now auto.
  - rewrite nothing_list_len; now auto.
+ assert (length (nothing_list d ++ map Just ys) = length xs) as Hlen.
  {
    rewrite app_length.
    rewrite nothing_list_len.
    rewrite map_length.
    apply Hd in H.
    lia.
  }
  simpl.
  rewrite combine_split; auto.
  rewrite IIST_e2_1_fwd_ge; simpl.
  rewrite Hfwd_2; simpl.
  destruct (app_length_destruct (nothing_list d' ++ map Just xs) (length xs)) as [mxs1 [mxs2 [Heq Hlen12]]].
  - rewrite app_length.
    rewrite map_length.
    lia.
  - rewrite Heq.
    assert (prefix mxs1 (nothing_list d' ++ map Just xs)) as Hpre.
    {
      rewrite Heq.
      now apply app_prefix.
    }
    assert (mxs = mxs1).
    {
      apply prefix_length_det with (nothing_list d' ++ map Just xs); auto.
      lia.
    }
    subst.
    rewrite combine_app_length_le; auto.
    apply Hd in H.
    lia.
Qed.





(* originalではf2/g2だったが、項の番号と合わせるためにf3に変更 *)
Definition IIST_f3 {X Y} `{EqDec X eq}
                   (inv : MST Y X) d' (ys : list Y) (y_mx : Y * maybe X) : option Y :=
 let (y, mx) := y_mx in
 option_bind (inv (ys ++ [y]))
  (fun xs =>
    if Compare_dec.le_gt_dec d' (length ys) then
      match mx with
      | Just x =>
         option_bind (last xs)
          (fun x' => if equiv_dec x x' then Some y else None)
      | Nothing => None (* xにNothingが来るのはd'まで *)
      end
    else
      match mx with
      | Just _ => None
      | Nothing => Some y
      end).


Definition IIST_f3' {X Y}
                    (inv : MST Y X) d' (ys : list Y) y : option (Y * maybe X) :=
 option_bind (inv (ys ++ [y]))
  (fun xs =>
    if Compare_dec.le_gt_dec d' (length ys) then
      option_bind (last xs)
       (fun x => Some (y, Just x))
    else Some (y, Nothing)).


Program Definition IIST_pinv_f3 {X Y} `{E : EqDec X eq}
                               (inv : MST Y X) d' (Hd' : d_MST inv d') ys : partial_invertible_function (Y * maybe X) Y :=
{| forward := IIST_f3 inv d' ys;
   backward := IIST_f3' inv d' ys
|}.
Next Obligation.
unfold IIST_f3, IIST_f3', equiv_dec.
split; intro Hsome.
+ assert (y = b).
  {
    destruct (inv (ys ++ [y])) as [xs | ]; simpl in Hsome; try now inversion Hsome.
    destruct (Compare_dec.le_gt_dec d' (length ys)); simpl in Hsome.
    + destruct m as [x | ]; try now inversion Hsome.
      destruct (last xs) as [x' | ]; simpl in Hsome; try now inversion Hsome.
      destruct (E x x') as [e | e]; simpl in Hsome; inversion Hsome; now auto.
    + destruct m as [x | ]; now inversion Hsome.
  }
  subst.
  destruct (inv (ys ++ [b])) as [xs | ]; simpl in *; try now inversion Hsome.
  destruct (Compare_dec.le_gt_dec d' (length ys)) as [e | e].
  - destruct m; try now inversion Hsome.
    destruct (last xs) as [x' | ]; try now inversion Hsome.
    simpl in *.
    destruct (E x x') as [e' | e']; simpl in Hsome; try now inversion Hsome.
    unfold equiv in e'; subst; auto.
  - destruct m; now inversion Hsome.
+ destruct (inv (ys ++ [b])) as [xs | ] eqn: Hmst; simpl in Hsome; try now inversion Hsome.
  destruct (Compare_dec.le_gt_dec d' (length ys)) as [e | e]; simpl in *.
  - destruct (last xs) as [x | ] eqn: Hlast; simpl in Hsome; inversion Hsome; subst.
    rewrite Hmst; simpl; rewrite Hlast; simpl.
    destruct (E x x) as [e' | e']; auto; elim e'; now auto.
  - inversion Hsome; subst.
    rewrite Hmst; simpl; now auto.
Qed.


Definition IIST_g3 {X Y} (ys : list Y) (y_mx : Y * maybe X) : list Y :=
 let (y, _) := y_mx in ys ++ [y].


Definition IIST_e3 {X Y} `{E : EqDec X eq}
                          (inv : MST Y X) d' (Hd' : d_MST inv d') :=
 IIST_mapfold [] (IIST_pinv_f3 inv d' Hd') IIST_g3.


Lemma fold_left_IIST_g3_app :
 forall X Y (xs1 xs2: list X) (ys : list (maybe Y)),
  length xs1 <= length ys
  -> fold_left IIST_g3 (combine xs1 ys) xs2 = xs2 ++ xs1.
intros X Y xs1.
induction xs1 as [ | x xs1 Hxs1]; intros xs2 ys Hl; simpl.
+ rewrite app_nil_r; now auto.
+ destruct ys; simpl in *.
  - lia.
  - rewrite Hxs1.
    * rewrite <- app_assoc; simpl; now auto.
    * lia.
Qed.



Lemma IIST_e3_fwd :
 forall X Y `{E : EqDec X eq} (mst : MST X Y) (inv : MST Y X) d (Hd : d_MST mst d) d' (Hd' : d_MST inv d') (Hist : MIST mst) (Hinv : MInv mst inv) (Hiist : MIST inv) xs ys,
  mst xs = Some ys ->
   fwd (IIST_e3 inv d' Hd') (combine ys (nothing_list d' ++ map Just xs))
    = Some ys.
intros X Y eq0 E mst inv d Hd d' Hd' Hist Hinv Hiist xs.
unfold fwd; simpl.
induction xs as [ | x xs Hxs] using list_inv_ind; intros ys H; simpl.
+ assert (ys = nil).
  - apply length_zero_iff_nil.
    apply Hd in H.
    simpl in H.
    auto.
  - subst; simpl.
    now auto.
+ assert (length (xs ++ [x]) = length xs + 1) as Hlenxs by (now apply app_length).
  destruct (Compare_dec.le_gt_dec d (length xs)) as [e | e].
  2: {
    assert (ys = nil).
    {
      apply length_zero_iff_nil.
      apply Hd in H.
      lia.
    }
    subst.
    destruct (nothing_list d' ++ map Just (xs ++ [x])); simpl; now auto.
  }
  destruct (d_MIST_oneapp _ _ mst d xs ys x) as [y [ys' [Heq Hx]]]; auto.
  subst.
  assert (length (ys' ++ [y]) = length ys' + 1) as Hlenys by (now apply app_length).
  assert (Hx' := Hxs ys' Hx).
  clear Hxs.
  destruct (Hinv _ _ H) as [xs' [H' H'pre]].
  destruct (Compare_dec.le_gt_dec d' (length ys')) as [e' | e'] eqn:He'.
  - destruct (app_length_destruct xs (length ys' - d')) as [xs1 [xs2 [Hxseq Hxs1len]]].
    * apply Hd in Hx.
      lia.
    * rewrite Hxseq in *; clear xs Hxseq.
      rewrite <- app_assoc in *.
      rewrite map_app in *.
      assert (length (map Just xs1) = length xs1) as Hmap by (now apply map_length).
      rewrite app_assoc.
      rewrite app_assoc in Hx'.
      assert (length (nothing_list d' ++ map Just xs1) = length ys') as Hnxs1.
      {
        rewrite app_length.
        rewrite nothing_list_len.
        lia.
      }
      rewrite combine_app_length_le in Hx'; try lia.
      rewrite combine_app_app; auto.
      rewrite fwd_mapfold_app.
      rewrite fold_left_IIST_g3_app; try lia.
      rewrite Hx'; simpl.
      destruct (d_MIST_oneapp _ _ inv d' ys' xs' y) as [x' [xs'1 [? H'1]]]; auto.
      subst.
      assert (xs'1 = xs1).
      {
        eapply prefix_length_det.
        + eapply prefix_transitive.
          - now apply app_prefix.
          - exact H'pre.
        + now apply app_prefix.
        + rewrite Hxs1len.
          symmetry.
          apply Hd'.
          now auto.
      }
      subst.
      apply prefix_inv_head in H'pre.
      apply prefix_app in H'pre.
      destruct H'pre as [xs3 Hpre].
      rewrite <- Hpre in *; simpl.
      rewrite H'; rewrite He'; simpl.
      rewrite last_correct; simpl.
      destruct (x' == x') as [ex | ex]; simpl; auto.
      elim ex.
      now constructor.
  - rewrite combine_nothing_list_r; try lia.
    rewrite combine_nothing_list_r in Hx'; try lia.
    rewrite Hlenys.
    rewrite nothing_list_app.
    assert (Hnll := nothing_list_len X (length ys')).
    rewrite combine_app_app; try lia.
    rewrite fwd_mapfold_app.
    rewrite Hx'.
    rewrite fold_left_IIST_g3_app; try lia; simpl.
    rewrite He'; simpl.
    rewrite H'; simpl.
    now auto.
Qed.




Definition IIST_e {X Y} `{EX : EqDec X eq} `{EY : EqDec Y eq}
                         (mst : MST X Y) d (inv : MST Y X) d'
                         (Hd : d_MST mst d) (Hd' : d_MST inv d') : IIST X Y :=
 IIST_seqcomp (IIST_e1 mst d Hd) (IIST_seqcomp (IIST_e2 d d') (IIST_e3 inv d' Hd')).


Lemma IIST_e_delay_fwd :
 forall X Y `{EqDec X eq} `{EqDec Y eq}
             (mst : MST X Y) d inv d' Hd Hd',
 delay_fwd (IIST_e mst d inv d' Hd Hd') = d.
intros X Y ? ? ? ? ? d ? d' ? ?.
unfold IIST_e, IIST_e1, IIST_e2, IIST_e3; simpl.
clear.
rewrite PeanoNat.Nat.add_0_r.
assert (delay_fwd (@IIST_e2_2 X d') = 0) as H.
{
  induction d'; simpl; auto.
  rewrite IHd'; now auto.
}
rewrite H; clear.
induction d; simpl; auto.
destruct (delay_fwd (IIST_e2_1 d)); simpl in IHd; now auto.
Qed.


Lemma IIST_e_delay_bwd :
 forall X Y `{EqDec X eq} `{EqDec Y eq}
             (mst : MST X Y) d inv d' Hd Hd',
 delay_bwd (IIST_e mst d inv d' Hd Hd') = d'.
intros X Y ? ? ? ? ? d ? d' ? ?.
unfold IIST_e, IIST_e1, IIST_e2, IIST_e3; simpl.
clear.
rewrite PeanoNat.Nat.add_0_r.
assert (delay_bwd (@IIST_e2_1 Y d) = 0) as H.
{
  induction d; simpl; auto.
}
rewrite H; clear; simpl.
induction d'; simpl; auto.
rewrite IHd'; lia.
Qed.



Lemma IIST_e_mst :
 forall X Y `{EqDec X eq} `{EqDec Y eq}
            (mst : MST X Y) d inv d' Hd Hd',
 MIST mst
 -> MInv mst inv
 -> MIST inv
 -> forall xs,
     mst xs = fwd (IIST_e mst d inv d' Hd Hd') xs.
intros X Y eqX EX eqY EY mst d inv d' Hd Hd' Hist Hinv Hiist xs.
unfold IIST_e; simpl.
destruct (mst xs) as [ys | ] eqn:Heq.
+ assert (He1 := IIST_e1_fwd_Some X Y mst d Hd Hist xs ys).
  unfold fwd in He1; simpl in He1.
  rewrite (He1 Heq); simpl.
  assert (He2 := IIST_e2_fwd X Y mst d d' Hd Hist xs ys Heq).
  simpl in He2.
  rewrite He2; simpl.
  symmetry.
  eapply IIST_e3_fwd with (d := d); now eauto.
+ assert (He1 := IIST_e1_fwd_None X Y mst d Hd Hist xs Heq).
  unfold fwd in He1; simpl in He1.
  rewrite He1; simpl.
  now auto.
Qed.


(** Second theorem:
     for any (d, d')-FIRST pair (mst, inv),
     there exists FIRSD e such that
     forward semantics of it behaves the same as mst,
     and its forward(backward)-delay is d (d'). **)
Theorem d_d'_MIIST_IIST :
 forall X Y `{EqDec X eq} `{EqDec Y eq} (mst : MST X Y) d d',
  (exists inv, d_d'_MIIST_pair mst inv d d')
  -> exists e,
      forall xs, mst xs = fwd e xs
      /\ delay_fwd e = d
      /\ delay_bwd e = d'.
intros X Y eq1 EX eq2 EY mst d d' H.
destruct H as [inv Hpair].
apply d_d'_MIIST_pair_min in Hpair.
destruct Hpair as [Hist [Hd [Hinv [Hiist Hd']]]].
exists (IIST_e mst d inv d' Hd Hd').
intro xs; intuition.
+ apply IIST_e_mst; now auto.
+ now apply IIST_e_delay_fwd.
+ now apply IIST_e_delay_bwd.
Qed.



Lemma IIST_e_inv :
 forall X Y `{EqDec X eq} `{EqDec Y eq}
            (mst : MST X Y) d inv d' Hd Hd',
 MIST mst
 -> MInv mst inv
 -> MIST inv
 -> forall xs ys,
     mst xs = Some ys ->
     inv ys = bwd (IIST_e mst d inv d' Hd Hd') ys.
intros X Y EQ0 EX EQ1 EY mst d inv d' Hd Hd' Hist Hinv Hiist xs ys Hxs.
destruct (Hinv _ _ Hxs) as [xs' [Hxs' Hpre']].
rewrite Hxs'.
assert (Hlen' := Hd' _ _ Hxs').
assert (Hinv' := IIST_MInv _ _ (IIST_e mst d inv d' Hd Hd')).
erewrite IIST_e_mst in Hxs; eauto.
destruct (Hinv' _ _ Hxs) as [xs'' [Hxs'' Hpre'']].
rewrite Hxs''.
assert (Hd'' := IIST_bwd_d_MST _ _ (IIST_e mst d inv d' Hd Hd')).
rewrite IIST_e_delay_bwd in Hd''.
assert (Hlen'' := Hd'' _ _ Hxs'').
rewrite (prefix_length_det xs' xs'' xs); auto.
lia.
Qed.



(** Third theorem:
     for any (d, d')-FIRST pair (mst, inv),
     there exists d'-FIRST inv' such that
     (mst, inv') is a (d, d')-FIRST pair and
     (inv', mst) is a (d', d)-FIRST pair. **)
Theorem d_d'_MIIST_representative_inv :
 forall X Y `{EqDec X eq} `{EqDec Y eq} (mst : MST X Y) d d',
  (exists inv, d_d'_MIIST_pair mst inv d d')
  -> exists inv',
      d_d'_MIIST_pair mst inv' d d' /\
      d_d'_MIIST_pair inv' mst d' d.
intros X Y eq1 EX eq2 EY mst d d' [inv Hpair].
apply d_d'_MIIST_pair_min in Hpair.
destruct Hpair as [Hist [Hd [Hinv [Hiist Hd']]]].
exists (bwd (IIST_e mst d inv d' Hd Hd')).
assert (Hfwd := IIST_e_mst _ _ mst d inv d' Hd Hd' Hist Hinv Hiist).
assert (Hd'_mst := IIST_bwd_d_MST _ _ (IIST_e mst d inv d' Hd Hd')).
rewrite (IIST_e_delay_bwd X Y mst d inv d' Hd Hd') in Hd'_mst.
split; apply d_d'_MIIST_pair_min; intuition; try apply IIST_bwd_MIST.
+ unfold MInv in *.
  intros xs ys Hfwd'.
  destruct (Hinv _ _ Hfwd') as [xs' [Hbwd Hpre]].
  exists xs'; intuition.
  rewrite <- Hbwd.
  symmetry.
  apply IIST_e_inv with xs; now auto.
+ assert (Hiinv := IIST_bwd_MInv _ _ (IIST_e mst d inv d' Hd Hd')).
  unfold MInv in *.
  intros ys xs Hbwd.
  destruct (Hiinv _ _ Hbwd) as [ys' [Hfwd' Hpre]].
  exists ys'; intuition.
  rewrite <- Hfwd'.
  now apply IIST_e_mst.
Qed.



End IIST_descriptive.

