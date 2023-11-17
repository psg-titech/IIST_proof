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
  * case_eq (split (combine al bl)).
    intros al'' bl'' Heq.
    rewrite Heq in H.
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
  + intros a1 ys H. destruct (forward X Y (p a1) a); simpl in *; try (inversion H; fail).
    case_eq (fwd_mapfold p a0 (a0 a1 a) xs); [intros l H1 | intro H1]; rewrite H1 in H; simpl in H; try inversion H.
    simpl; rewrite IHxs with (a0 a1 a) l; now auto.
- intros xs ys H; rewrite PeanoNat.Nat.sub_0_r.
  inversion H.
  now apply slide_length.
- intros xs ys H.
  destruct xs.
  + inversion H; simpl; now auto.
  + destruct (equiv_one_dec x0); inversion H; simpl; lia.
- intros xs zs H.
  case_eq (fwd e1 xs); [intros ys H1 | intro H1]; rewrite H1 in H; simpl in H; inversion H; subst.
  rewrite PeanoNat.Nat.sub_add_distr.
  rewrite (IHe1 xs ys H1); now auto.
- intros x12s y12s H.
  case_eq (split x12s); intros x1s x2s Hx12.
  rewrite Hx12 in H.
  case_eq (fwd e1 x1s); [intros y1s H1s | intro H1s]; rewrite H1s in H; simpl in H; try (inversion H; fail).
  case_eq (fwd e2 x2s); [intros y2s H2s | intro H2s]; rewrite H2s in H; simpl in H; inversion H.
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
  + intros a1 xs H. destruct (backward X Y (p a1) a); simpl in *; try (inversion H; fail).
    case_eq (bwd_mapfold p a0 (a0 a1 x) ys); [intros l H1 | intro H1]; rewrite H1 in H; simpl in H; try inversion H.
    simpl; rewrite IHys with (a0 a1 x) l; now auto.
- intros ys xs H.
  destruct ys; simpl in *.
  + inversion H; simpl; now auto.
  + destruct (equiv_one_dec x0); inversion H; lia.
- intros ys xs H; rewrite PeanoNat.Nat.sub_0_r.
  inversion H.
  now apply slide_length.
- intros zs xs H.
  case_eq (bwd e2 zs); [intros ys H1 | intro H1]; rewrite H1 in H; simpl in H; inversion H; subst.
  rewrite PeanoNat.Nat.add_comm; rewrite PeanoNat.Nat.sub_add_distr.
  rewrite (IHe2 zs ys H1); now auto.
- intros y12s x12s H.
  case_eq (split y12s); intros y1s y2s Hy12.
  rewrite Hy12 in H.
  case_eq (bwd e1 y1s); [intros x1s H1s | intro H1s]; rewrite H1s in H; simpl in H; try (inversion H; fail).
  case_eq (bwd e2 y2s); [intros x2s H2s | intro H2s]; rewrite H2s in H; simpl in H; inversion H.
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
  + destruct (forward X Y (p a1) a); simpl in *; try (inversion H0; fail).
    case_eq (fwd_mapfold p a0 (a0 a1 a) xs); [intros l H4 | intro H4]; rewrite H4 in H0; try (inversion H0; fail).
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
  destruct (fwd e1 xs) as [zs | ]; simpl in *; try (inversion H0; fail).
  destruct (He1 zs) as [zs' [H1 H2]]; auto; clear He1.
  destruct (IHe2 zs zs' ys) as [ys' [H3 H4]]; auto; clear IHe2.
  exists ys'; split; auto.
  rewrite H1; simpl; rewrite H3; reflexivity.
- intros.
  case_eq (split xs). intros x1s x2s Hx12s.
  rewrite Hx12s in H0; simpl in H0.
  case_eq (split xs'). intros x1s' x2s' Hx12s'.
  case_eq (fwd e1 x1s); [intros y1s H1 | intro H1]; rewrite H1 in H0; simpl in H0; try (inversion H0; fail).
  case_eq (fwd e2 x2s); [intros y2s H2 | intro H2]; rewrite H2 in H0; simpl in H0; inversion H0; subst.
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
  + destruct (backward X Y (p a1) a); simpl in *; try (inversion H0; fail).
    case_eq (bwd_mapfold p a0 (a0 a1 x) ys); [intros l H4 | intro H4]; rewrite H4 in H0; try (inversion H0; fail).
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
  destruct (bwd e2 ys) as [zs | ]; simpl in *; try (inversion H0; fail).
  destruct (He2 zs) as [zs' [H1 H2]]; auto; clear He2.
  destruct (IHe1 zs zs' xs) as [xs' [H3 H4]]; auto; clear IHe1.
  exists xs'; split; auto.
  rewrite H1; simpl; rewrite H3; reflexivity.
- intros.
  case_eq (split ys). intros y1s y2s Hy12s.
  rewrite Hy12s in H0; simpl in H0.
  case_eq (split ys'). intros y1s' y2s' Hy12s'.
  case_eq (bwd e1 y1s); [intros x1s H1 | intro H1]; rewrite H1 in H0; simpl in H0; try (inversion H0; fail).
  case_eq (bwd e2 y2s); [intros x2s H2 | intro H2]; rewrite H2 in H0; simpl in H0; inversion H0; subst.
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
  + case_eq (forward X Y (p a) x);
     [ intros y Hy | intro Hy ]; rewrite Hy in Hfwd; simpl in Hfwd;
     try (inversion Hfwd; fail).
    case_eq (fwd_mapfold p a0 (a0 a x) xs);
     [ intros ys' Hys' | intro Hys' ]; rewrite Hys' in Hfwd; simpl in Hfwd;
     try (inversion Hfwd; fail).
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
- case_eq (fwd e1 xs); [intros zs H0 | intro H0]; rewrite H0 in H; simpl in H; try (inversion H; fail).
  destruct (IHe2 zs ys H) as [ zs' [ H1 H2 ]]; clear IHe2.
  rewrite H1; simpl.
  destruct (IHe1 xs zs H0) as [ xs'' [ H3 H4 ]]; clear IHe1.
  destruct (bwd_prefix e1 zs zs' xs'' H2 H3) as [ xs' [ H5 H6 ]].
  exists xs'.
  split; auto.
  apply prefix_transitive with (l2 := xs''); now auto.
- case_eq (split xs). intros x1s x2s Hx12s.
  rewrite Hx12s in H; simpl in H.
  case_eq (split ys). intros y1s y2s Hy12s.
  case_eq (fwd e1 x1s); [ intros y1s' H0 | intro H0 ]; rewrite H0 in H; simpl in H; try (inversion H; fail).
  destruct (IHe1 x1s y1s' H0) as [ x1s' [ H1 H2 ]]; clear IHe1.
  case_eq (fwd e2 x2s); [ intros y2s' H3 | intro H3 ]; rewrite H3 in H; simpl in H; try (inversion H; fail).
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
  + case_eq (backward X Y (p a) y);
     [ intros x Hx | intro Hx ]; rewrite Hx in Hbwd; simpl in Hbwd;
     try (inversion Hbwd; fail).
    case_eq (bwd_mapfold p a0 (a0 a x) ys);
     [ intros xs' Hxs' | intro Hxs' ]; rewrite Hxs' in Hbwd; simpl in Hbwd;
     try (inversion Hbwd; fail).
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
- case_eq (bwd e2 ys); [intros zs H0 | intro H0]; rewrite H0 in H; simpl in H; try (inversion H; fail).
  destruct (IHe1 zs xs H) as [ zs' [ H1 H2 ]]; clear IHe1.
  rewrite H1; simpl.
  destruct (IHe2 ys zs H0) as [ ys'' [ H3 H4 ]]; clear IHe2.
  destruct (fwd_prefix e2 zs zs' ys'' H2 H3) as [ ys' [ H5 H6 ]].
  exists ys'.
  split; auto.
  apply prefix_transitive with (l2 := ys''); now auto.
- case_eq (split ys). intros y1s y2s Hy12s.
  rewrite Hy12s in H; simpl in H.
  case_eq (split xs). intros x1s x2s Hx12s.
  case_eq (bwd e1 y1s); [ intros x1s' H0 | intro H0 ]; rewrite H0 in H; simpl in H; try (inversion H; fail).
  destruct (IHe1 y1s x1s' H0) as [ y1s' [ H1 H2 ]]; clear IHe1.
  case_eq (bwd e2 y2s); [ intros x2s' H3 | intro H3 ]; rewrite H3 in H; simpl in H; try (inversion H; fail).
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


Definition MIST_coord {X Y} (mst : MST X Y) (xs : list X) : option Y :=
option_bind (mst xs) last.


Theorem d_MIST_coord_correct :
 forall X Y (mst : MST X Y) d,
  d_MIST mst d
  ->
    let coord := MIST_coord mst in
     (forall xs x y,
       (exists ys, mst (xs ++ [x]) = Some (ys ++ [y]))
       <-> coord (xs ++ [x]) = Some y)
     /\
     (forall xs,
      mst xs = None \/ length xs <= d <-> coord xs = None).
unfold MIST_coord; intros X Y mst d [Hmist Hd_mst]; split; intros; split; intro.
+ destruct H as [ys H]; rewrite H; simpl. now apply last_correct.
+ destruct (mst (xs ++ [x])); simpl in H; try (inversion H; fail).
  apply last_correct' in H.
  destruct H as [l' H]; exists l'; rewrite H; now auto.
+ destruct H.
  - rewrite H; simpl; now auto.
  - case_eq (mst xs); simpl; auto.
    intros ys H0.
    assert (H1 := Hd_mst xs ys H0).
    destruct ys; auto.
    simpl in H1; lia.
+ case_eq (mst xs); auto.
  intros ys H0; right.
  rewrite H0 in H; simpl in H.
  assert (H1 := Hd_mst _ _ H0).
  destruct ys; simpl in *; inversion H.
  lia.
Qed.


Definition MInv {X Y} (mst : MST X Y) (inv : MST Y X) := 
 forall xs ys, mst xs = Some ys
 -> exists xs', inv ys = Some xs' /\ prefix xs' xs.


Definition MIIST {X Y} (mst : MST X Y) (inv : MST Y X) :=
 MIST mst /\ MInv mst inv.


Definition d_MIIST {X Y} (mst : MST X Y) (inv : MST Y X) d' :=
 MIIST mst inv /\ d_MIST inv d'.


Definition d_d'_MIIST {X Y} (mst : MST X Y) d d' :=
 d_MIST mst d /\ exists inv, d_MIIST mst inv d'.





End Math_IIST.
