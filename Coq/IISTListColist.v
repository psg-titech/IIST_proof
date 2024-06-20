Require Import IIST.IISTData.
Require Import IIST.IIST.
Require Import IIST.PartialColist.
Require Import IIST.FinPartColist.

Require Import Lia.


Lemma FailColist_cofwd :
 forall {X Y : Type} (e : IIST X Y) l,
  FailColist l -> FailColist (cofwd e l).
intros X Y e.
induction e as [A X Y a f g | X x e' | X x e' | X Y Z exy IHexy eyz IHeyz | X1 X2 Y1 Y2 e1 IHe1 e2 IHe2]; intros l Hf; simpl.
+ revert a.
  induction Hf as [x l Hf IH | ]; intro a.
  - cl_red (cofwd_mapfold f g a (x :: l)).
    simpl.
    destruct (PartInvFun.forward X Y (f a) x) as [y | ]; simpl.
    * constructor.
      now auto.
    * now constructor.
  - cl_red (cofwd_mapfold f g a -*-).
    simpl.
    now constructor.
+ apply FailColist_coslide.
  now auto.
+ inversion Hf; subst.
  - destruct (EqOneDec.equiv_one_dec a).
    * now auto.
    * now constructor.
  - now constructor.
+ now auto.
+ apply FailColist_cozip_l.
  - apply cofwd_sync_colist.
    now apply coleft_right_strict_sync_colist.
  - apply FailColist_drop.
    apply IHe1.
    apply FailColist_coleft.
    now auto.
Qed.



Theorem fwd_cofwd_correspond :
 forall {X Y : Type} (l : list X) cl,
  CorrListColist (Some l) cl
   -> forall (e : IIST X Y), CorrListColist (fwd e l) (cofwd e cl).
intros X Y l cl H e.
revert l cl H.
induction e as [A X Y a f g | X x e' | X x e' | X Y Z exy IHexy eyz IHeyz | X1 X2 Y1 Y2 e1 IHe1 e2 IHe2]; simpl.
+ intro l.
  revert a.
  induction l as [ | x l IHl]; intros a cl Hcorr; cl_red (cofwd_mapfold f g a cl).
  - inversion Hcorr.
    simpl.
    now constructor.
  - inversion Hcorr; subst; simpl.
    destruct (PartInvFun.forward X Y (f a) x); simpl.
    * apply IHl with (a := g a x) in H2.
      destruct (fwd_mapfold f g (g a x) l) as [ l' | ]; simpl; now constructor.
    * now constructor.
+ intros l cl.
  now apply CorrListColist_slide.
+ intros l cl Hcorr.
  inversion Hcorr; subst.
  - now constructor.
  - destruct (EqOneDec.equiv_one_dec a).
    * now auto.
    * now constructor.
+ intros l cl Hcorr.
  apply IHexy in Hcorr.
  destruct (fwd exy l) as [ l' | ]; simpl.
  - now auto.
  - apply CorrListColist_fail.
    apply CorrListColist_none_fail in Hcorr.
    apply FailColist_cofwd.
    now auto.
+ intros l cl Hcorr.
  assert (He1 := CorrListColist_left _ _ Hcorr).
  assert (He2 := CorrListColist_right _ _ Hcorr).
  destruct (List.split l) as [l1 l2] eqn: Heql.
  simpl in He1, He2.
  apply IHe1 in He1.
  apply IHe2 in He2.
  clear Hcorr IHe1 IHe2.
  assert (Hsyn : sync_colist (drop_tl_n (delay_fwd e2 - delay_fwd e1) (cofwd e1 (coleft cl)))
                             (drop_tl_n (delay_fwd e1 - delay_fwd e2) (cofwd e2 (coright cl)))).
  {
    apply cofwd_sync_colist.
    now apply coleft_right_strict_sync_colist.
  }
  destruct (fwd e1 l1) as [[ | y1 l1'] | ] eqn:Heq1; simpl.
  - inversion He1.
    rewrite drop_n_cnil.
    destruct (fwd e2 l2) as [l2' | ] eqn:Heq2; simpl.
    * rewrite SuccColist_zip_nil_l; [now constructor | ].
      apply SuccColist_drop.
      apply CorrListColist_list_succ with l2'.
      now auto.
    * rewrite <- H in Hsyn.
      rewrite drop_n_cnil in Hsyn.
      apply CorrListColist_fail.
      apply FailColist_cozip_r; auto.
      apply FailColist_drop.
      apply CorrListColist_none_fail.
      now auto.
  - assert (Hl1' := fwd_length_delay _ _ _ Heq1).
    simpl in Hl1'.
    destruct (fwd e2 l2) as [[ | y2 l2'] | ] eqn:Heq2; simpl.
    * inversion He2.
      rewrite drop_n_cnil.
      rewrite SuccColist_zip_nil_r; [now constructor | ].
      apply SuccColist_drop.
      apply CorrListColist_list_succ with (y1 :: l1')%list.
      now auto.
    * assert (Hl2' := fwd_length_delay _ _ _ Heq2).
      simpl in Hl2'.
      assert (Hlen : length l1 = length l2).
      {
        assert (Hl1 := List.split_length_l l).
        assert (Hl2 := List.split_length_r l).
        rewrite Heql in *; simpl in *.
        rewrite Hl2.
        now auto.
      }
      assert (Hlen1 : length l1' - length l2' = delay_fwd e2 - delay_fwd e1) by lia.
      assert (Hlen2 : length l2' - length l1' = delay_fwd e1 - delay_fwd e2) by lia.
      assert (Htemp : ((y1, y2) :: List.combine l1' l2' = List.combine (y1 :: l1') (y2 :: l2'))%list) by reflexivity.
      rewrite Htemp; clear Htemp.
      rewrite combine_drop_length.
      simpl length.
      simpl minus.
      rewrite Hlen1.
      rewrite Hlen2.
      apply CorrListColist_zip; apply CorrListColist_drop; now auto.
    * apply CorrListColist_fail.
      apply FailColist_cozip_r; auto.
      apply FailColist_drop.
      apply CorrListColist_none_fail.
      now auto.
  - apply CorrListColist_fail.
    apply FailColist_cozip_l; auto.
    apply FailColist_drop.
    apply CorrListColist_none_fail.
    now auto.
Qed.
