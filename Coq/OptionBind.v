Section option_bind.

Definition option_bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
match a with
| Some a => f a
| None => None
end.

End option_bind.
