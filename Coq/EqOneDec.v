Require Import Coq.Classes.EquivDec.
Require Import List.
Import ListNotations.

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



Definition eqdec_Some_eqdec {A} (a : A) `{EqOneDec A a} : @EqOneDec (option A) (Some a).
intro b.
destruct b.
+ destruct H with a0.
  - left; subst; now auto.
  - right; intro H'; apply n; inversion H'; now auto.
+ right; intro H'; now inversion H'.
Defined.


End EqOneDec.
