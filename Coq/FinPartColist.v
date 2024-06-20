Require Import IIST.IISTData.
Require Import IIST.PartialColist.


Inductive FinitePartialColist {A : Type} : PartialColist A -> Prop :=
| fcnil : FinitePartialColist []
| fccons : forall a l, FinitePartialColist l -> FinitePartialColist (a :: l)
| fcfail : FinitePartialColist -*-.

Inductive FailColist {A : Type} : PartialColist A -> Prop :=
| failcons : forall a l, FailColist l -> FailColist (a :: l)
| failfail : FailColist -*-.

Inductive SuccColist {A : Type} : PartialColist A -> Prop :=
| succcnil : SuccColist []
| succcons : forall a l, SuccColist l -> SuccColist (a :: l).



Lemma FinitePartialColist_fail_dec :
 forall {A : Type} (l : PartialColist A),
  FinitePartialColist l -> FailColist l \/ SuccColist l.
intros A l H.
induction H as [ | a l H IHl | ].
+ right.
  now constructor.
+ destruct IHl as [IHl | IHl].
  - left.
    constructor.
    now auto.
  - right.
    constructor.
    now auto.
+ left.
  now constructor.
Qed.


Lemma FailColist_coslide :
 forall {A : Type} (a : A) l,
  FailColist l -> FailColist (coslide a l).
intros A a l Hf.
revert a.
induction Hf as [a' l Hf IH | ]; intro a.
+ cl_red (coslide a (a' :: l)).
  simpl.
  constructor.
  now auto.
+ cl_red (@coslide A a -*-).
  simpl.
  now constructor.
Qed.


Lemma FailColist_coleft :
 forall {A B : Type} (l : PartialColist (A * B)),
  FailColist l -> FailColist (coleft l).
intros A B l H.
induction H as [ [a b] l H IHl | ].
+ cl_red (coleft ((a, b) :: l)).
  simpl.
  constructor.
  now auto.
+ cl_red (@coleft A B -*-).
  simpl.
  now constructor.
Qed.

Lemma FailColist_coright :
 forall {A B : Type} (l : PartialColist (A * B)),
  FailColist l -> FailColist (coright l).
intros A B l H.
induction H as [ [a b] l H IHl | ].
+ cl_red (coright ((a, b) :: l)).
  simpl.
  constructor.
  now auto.
+ cl_red (@coright A B -*-).
  simpl.
  now constructor.
Qed.


Lemma FailColist_cozip_l :
 forall {A B : Type} (la : PartialColist A) (lb : PartialColist B),
  sync_colist la lb -> FailColist la -> FailColist (cozip la lb).
intros A B la lb Hsyn Ha.
revert lb Hsyn.
induction Ha as [a la Ha IHa | ]; intros lb Hsyn; inversion Hsyn; subst.
+ cl_red (cozip (a :: la) (b :: l2)).
  simpl.
  constructor.
  apply IHa; now auto.
+ cl_red (@cozip A B (a :: la) -*-).
  simpl.
  now constructor.
+ cl_red (@cozip A B -*- lb).
  simpl.
  now constructor.
+ cl_red (@cozip A B -*- -*-).
  simpl.
  now constructor.
Qed.


Lemma FailColist_cozip_r :
 forall {A B : Type} (la : PartialColist A) (lb : PartialColist B),
  sync_colist la lb -> FailColist lb -> FailColist (cozip la lb).
intros A B la lb Hsyn Hb.
revert la Hsyn.
induction Hb as [b lb Hb IHb | ]; intros la Hsyn; inversion Hsyn; subst.
+ cl_red (cozip (a :: l1) (b :: lb)).
  simpl.
  constructor.
  apply IHb; now auto.
+ cl_red (@cozip A B -*- (b :: lb)).
  simpl.
  now constructor.
+ cl_red (@cozip A B -*- -*-).
  simpl.
  now constructor.
+ cl_red (@cozip A B la -*-).
  simpl.
  destruct la; now constructor.
Qed.


Lemma FailColist_drop :
 forall {A : Type} (n : nat) (l : PartialColist A),
  FailColist l -> FailColist (drop_tl_n n l).
intros A n l H.
induction H as [a l H IH | ].
+ cl_red (drop_tl_n n (a :: l)).
  simpl.
  destruct (n_look_ahead n l) eqn: Heq.
  - destruct l as [ | a' l | ].
    * now inversion H.
    * cl_red_in (drop_tl_n n (a' :: l)) IH.
      simpl in IH.
      apply look_ahead_tail_lt in Heq.
      rewrite Heq in IH.
      now inversion IH.
    * destruct n; simpl in Heq; discriminate.
  - now constructor.
  - constructor.
    now auto.
+ cl_red (@drop_tl_n A n -*-).
  simpl.
  now constructor.
Qed.


Lemma SuccColist_look_ahead :
 forall {A : Type} (n : nat) (l : PartialColist A),
  SuccColist l -> n_look_ahead n l = lt_n \/ n_look_ahead n l = more_n.
intros A n.
induction n as [ | n IHn]; intros l Hsucc; simpl; auto.
inversion Hsucc; subst; auto.
Qed.


Lemma SuccColist_drop :
 forall {A : Type} (n : nat) (l : PartialColist A),
  SuccColist l -> SuccColist (drop_tl_n n l).
intros A n l Hsucc.
induction Hsucc as [ | a l Hsucc IH].
+ cl_red (@drop_tl_n A n []).
  simpl.
  now constructor.
+ cl_red (drop_tl_n n (a :: l)).
  simpl.
  destruct (SuccColist_look_ahead n l Hsucc) as [Heq | Heq];
   rewrite Heq; constructor.
  now auto.
Qed.


Lemma SuccColist_zip_nil_l :
 forall {A B : Type} (lb : PartialColist B),
  SuccColist lb -> @cozip A B [] lb = [].
intros A B lb Hsucc.
cl_red (@cozip A B [] lb).
inversion Hsucc; simpl; now auto.
Qed.


Lemma SuccColist_zip_nil_r :
 forall {A B : Type} (la : PartialColist A),
  SuccColist la -> @cozip A B la [] = [].
intros A B la Hsucc.
cl_red (@cozip A B la []).
inversion Hsucc; simpl; now auto.
Qed.




Inductive CorrListColist {A : Type} : option (list A) -> PartialColist A -> Prop :=
| clcsnil : CorrListColist (Some nil) []
| clcscons : forall a l cl, CorrListColist (Some l) cl -> CorrListColist (Some (cons a l)) (a :: cl)
| clcnfail : CorrListColist None -*-
| clcncons : forall a cl, CorrListColist None cl -> CorrListColist None (a :: cl)
.


Section ListToColist.

Lemma CorrListColist_list_exists :
 forall {A : Type} (l : list A),
  exists cl, CorrListColist (Some l) cl.
intros A l.
induction l as [ | a l IHl].
+ exists [].
  now constructor.
+ destruct IHl as [cl IHl].
  exists (a :: cl).
  constructor.
  now auto.
Qed.

Lemma CorrListColist_list_unique :
 forall {A : Type} (l : list A) cl1 cl2,
  CorrListColist (Some l) cl1
   -> CorrListColist (Some l) cl2
   -> cl1 = cl2.
intros A l.
induction l as [ | a l IHl];
 intros cl1 cl2 Hl1 Hl2;
 inversion Hl1; subst;
 inversion Hl2; subst.
+ now auto.
+ rewrite (IHl cl cl0); now auto.
Qed.

Lemma CorrListColist_list_succ :
 forall {A : Type} (l : list A) cl,
  CorrListColist (Some l) cl -> SuccColist cl.
intros A l.
induction l as [ | a l IHl];
 intros cl Hl;
 inversion Hl; subst; constructor.
apply IHl; now auto.
Qed.


Lemma CorrListColist_eqnone_fail :
 forall {A : Type} (s : option (list A)) cl,
  CorrListColist s cl -> s = None -> FailColist cl.
intros A s cl Hc Heq.
induction Hc; inversion Heq; subst.
+ now constructor.
+ constructor.
  now auto.
Qed.

Lemma CorrListColist_none_fail :
 forall {A : Type} (cl : PartialColist A),
  CorrListColist None cl -> FailColist cl.
intros A cl Hc.
apply CorrListColist_eqnone_fail with (s := None); now auto.
Qed.



End ListToColist.


Section ColistToList.

Lemma CorrListColist_fin_exists :
 forall {A : Type} (cl : PartialColist A),
  FinitePartialColist cl -> exists s, CorrListColist s cl.
intros A cl H.
induction H as [ | a cl H IHcl | ].
+ exists (Some nil).
  now constructor.
+ destruct IHcl as [s IHcl].
  destruct s as [ l | ].
  - exists (Some (cons a l)).
    constructor.
    now auto.
  - exists None.
    constructor.
    now auto.
+ exists None.
  now constructor.
Qed.


Lemma CorrListColist_unique :
 forall {A : Type} (cl : PartialColist A) s1 s2,
  CorrListColist s1 cl
   -> CorrListColist s2 cl
   -> s1 = s2.
intros A cl s1 s2 Hs1.
revert s2.
induction Hs1 as [ | a l cl Hs1 IHs1 | | a cl Hs1 IHs1]; intros s2 Hs2; inversion Hs2; subst.
+ now auto.
+ apply IHs1 in H1.
  inversion H1; subst.
  now auto.
+ apply IHs1 in H1.
  now inversion H1.
+ now auto.
+ apply IHs1 in H1.
  now inversion H1.
+ now auto.
Qed.


Lemma CorrListColist_fail :
 forall {A : Type} (cl : PartialColist A),
  FailColist cl -> CorrListColist None cl.
intros A cl Hcl.
induction Hcl as [a cl Hcl IHcl | ]; constructor.
now auto.
Qed.

Lemma CorrListColist_succ :
 forall {A : Type} (cl : PartialColist A),
  SuccColist cl -> exists l, CorrListColist (Some l) cl.
intros A cl Hcl.
induction Hcl as [ | a cl Hcl IHcl].
+ exists nil.
  now constructor.
+ destruct IHcl as [l IHcl].
  exists (cons a l).
  constructor.
  now auto.
Qed.


End ColistToList.


Require Import IIST.IIST.

Lemma CorrListColist_slide :
 forall {A : Type} (a : A) l cl,
  CorrListColist (Some l) cl -> CorrListColist (Some (slide a l)) (coslide a cl).
intros A a l.
revert a.
induction l as [ | a' l IHl]; intros a cl Hcorr; cl_red (coslide a cl);
 inversion Hcorr; subst; simpl; constructor.
now auto.
Qed.


Inductive list_status : Set :=
| lt_l | more_l.


Fixpoint look_ahead {A : Type} (n : nat) (l : list A) : list_status :=
 match n, l with
 | O, _ => more_l
 | _, nil => lt_l
 | S n, cons _ l => look_ahead n l
 end.


Require Import Lia.

Lemma look_ahead_length :
 forall {A : Type} (n : nat) (l : list A),
  look_ahead n l = lt_l <-> length l < n.
intros A n.
induction n as [ | n IHn]; intros [ | a l]; split; intro Has; simpl in *.
+ discriminate.
+ lia.
+ discriminate.
+ lia.
+ lia.
+ now auto.
+ apply IHn in Has.
  lia.
+ apply IHn.
  lia.
Qed.



Fixpoint drop_tl {A : Type} (n : nat) (l : list A) : list A :=
 match l with
 | nil => nil
 | cons a l =>
   match look_ahead n l with
   | lt_l => nil
   | more_l => a :: drop_tl n l
   end
 end.


(* general lemma: maybe unused in this proof *)
Lemma drop_length_nil :
 forall {A : Type} (n : nat) (l : list A),
  length l <= n -> drop_tl n l = nil.
intros A n l.
induction l as [ | a l IHl]; intro H; simpl in *; auto.
apply look_ahead_length in H.
rewrite H.
now auto.
Qed.

Lemma drop_length_app :
 forall {A : Type} (n : nat) (l : list A),
  n <= length l ->
   exists l1 l2, l = (l1 ++ l2)%list /\ length l2 = n.
intros A n l H.
induction l as [ | a l IHl]; simpl in H.
+ destruct n as [ | n].
  - exists nil.
    exists nil.
    simpl.
    now auto.
  - lia.
+ inversion H; subst.
  - exists nil.
    exists (a :: l)%list.
    simpl.
    now auto.
  - apply IHl in H1.
    destruct H1 as [l1 [l2 [Hl Hl2]]].
    exists (a :: l1)%list.
    exists l2.
    rewrite Hl.
    simpl; now auto.
Qed.



Lemma combine_drop_length :
 forall {A B : Type} (la : list A) (lb : list B),
  List.combine la lb = List.combine (drop_tl (length la - length lb) la) (drop_tl (length lb - length la) lb).
intros A B la.
induction la as [ | a la IHla]; intro lb; simpl; auto.
destruct lb as [ | b lb]; simpl.
+ rewrite List.combine_nil.
  now auto.
+ destruct (look_ahead (length la - length lb) la) eqn: Hla.
  - apply look_ahead_length in Hla.
    lia.
  - destruct (look_ahead (length lb - length la) lb) eqn: Hlb.
    * apply look_ahead_length in Hlb.
      lia.
    * simpl.
      rewrite IHla.
      now auto.
Qed.



Lemma CorrListColist_look_ahead :
 forall {A : Type} (l : list A) cl n,
  CorrListColist (Some l) cl ->
   look_ahead n l = lt_l /\ n_look_ahead n cl = lt_n
   \/ look_ahead n l = more_l /\ n_look_ahead n cl = more_n.
intros A l.
induction l as [ | a l IHl]; intros cl n Hcorr; inversion Hcorr; subst; simpl.
+ destruct n; simpl; now auto.
+ destruct n; simpl; now auto.
Qed.


Lemma CorrListColist_drop :
 forall {A : Type} (l : list A) cl n,
  CorrListColist (Some l) cl -> CorrListColist (Some (drop_tl n l)) (drop_tl_n n cl).
intros A l.
induction l as [ | a l IHl]; intros cl n Hcorr; simpl; inversion Hcorr; subst.
+ cl_red (@drop_tl_n A n []); simpl.
  now constructor.
+ cl_red (drop_tl_n n (a :: cl0)); simpl.
  destruct (CorrListColist_look_ahead _ _ n H2) as [[Hl Hcl] | [Hl Hcl]]; rewrite Hl; rewrite Hcl.
  - now constructor.
  - constructor.
    now auto.
Qed.


Lemma cons_split_fst :
 forall {A B : Type} (ab : A * B) l,
  fst (List.split (ab :: l)%list) = (fst ab :: fst (List.split l))%list.
intros A B [a b] l.
simpl.
destruct (List.split l).
simpl.
now auto.
Qed.


Lemma CorrListColist_left :
 forall {A B : Type} (l : list (A * B)) cl,
  CorrListColist (Some l) cl -> CorrListColist (Some (fst (List.split l))) (coleft cl).
intros A B l.
induction l as [ | [a b] l IHl]; intros cl Hcorr; inversion Hcorr; subst.
+ cl_red (@coleft A B []).
  simpl.
  now constructor.
+ rewrite cons_split_fst.
  cl_red (coleft ((a, b) :: cl0)).
  simpl.
  constructor.
  apply IHl.
  now auto.
Qed.


Lemma cons_split_snd :
 forall {A B : Type} (ab : A * B) l,
  snd (List.split (ab :: l)%list) = (snd ab :: snd (List.split l))%list.
intros A B [a b] l.
simpl.
destruct (List.split l).
simpl.
now auto.
Qed.


Lemma CorrListColist_right :
 forall {A B : Type} (l : list (A * B)) cl,
  CorrListColist (Some l) cl -> CorrListColist (Some (snd (List.split l))) (coright cl).
intros A B l.
induction l as [ | [a b] l IHl]; intros cl Hcorr; inversion Hcorr; subst.
+ cl_red (@coright A B []).
  simpl.
  now constructor.
+ rewrite cons_split_snd.
  cl_red (coright ((a, b) :: cl0)).
  simpl.
  constructor.
  apply IHl.
  now auto.
Qed.


Lemma CorrListColist_zip :
 forall {A B : Type} (la : list A) (lb : list B) cla clb,
  CorrListColist (Some la) cla
  -> CorrListColist (Some lb) clb
  -> CorrListColist (Some (List.combine la lb)) (cozip cla clb).
intros A B la.
induction la as [ | a la IHla]; intros lb cla clb Hcorra Hcorrb;
 cl_red (cozip cla clb);
 inversion Hcorra; inversion Hcorrb; subst; simpl in *; constructor.
now eauto.
Qed.

