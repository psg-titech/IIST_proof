Require Import IIST.OptionBind.



Record partial_invertible_function (A : Type) (B : Type) : Type := {
  forward : A -> option B;
  backward : B -> option A;
  invertible : forall (a : A) (b : B), forward a = Some b <-> backward b = Some a
}.


Declare Scope part_inv_fun_scope.

Bind Scope part_inv_fun_scope with partial_invertible_function.

Notation "A <~~> B" := (partial_invertible_function A B) (at level 95, no associativity) : part_inv_fun_scope.


