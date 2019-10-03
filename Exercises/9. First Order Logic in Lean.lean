section
  variable A : Type
  variable f : A → A
  variable P : A → Prop
  variable h : ∀ x, P x → P (f x)

  -- Show the following:
  example : ∀ y, P y → P (f (f y)) :=
  assume y,
  have h1 : P y → P (f y), from h y,
  have h2 : P (f y) → P (f (f y)), from h (f y),
  show P y → P (f (f y)), from 
    assume h4 : P y,
    have h5 : P (f y), from h1 h4,
    show P (f (f y)), from h2 h5
end

section
  variable U : Type
  variables A B : U → Prop

  example : (∀ x, A x ∧ B x) → ∀ x, A x :=
  assume h1 : ∀ x, A x ∧ B x,
  assume y,
  have h2 : A y ∧ B y, from h1 y,
  show A y, from h2.left
end

section
  variable U : Type
  variables A B C : U → Prop

  variable h1 : ∀ x, A x ∨ B x
  variable h2 : ∀ x, A x → C x
  variable h3 : ∀ x, B x → C x

  example : ∀ x, C x :=
  assume y,
  show C y, from
    have h4 : A y ∨ B y, from h1 y,
    or.elim h4
      (assume h5 : A y,
      have h6 : A y → C y, from h2 y,
      show C y, from h6 h5)
      (assume h5 : B y,
      have h6 : B y → C y, from h3 y,
      show C y, from h6 h5)
end

open classical   -- not needed, but you can use it

-- This is an exercise from Chapter 4. Use it as an axiom here.
axiom not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P)

example (Q : Prop) : ¬ (Q ↔ ¬ Q) :=
not_iff_not_self Q

section
  variable Person : Type
  variable shaves : Person → Person → Prop
  variable barber : Person
  variable h : ∀ x, shaves barber x ↔ ¬ shaves x x

  -- Show the following:
  example : false :=
  have h3 : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
  have h2 : ¬ shaves barber barber, from
    assume h4 : shaves barber barber,
    have h5 : ¬ shaves barber barber, from iff.elim_left h3 h4,
    show false, from h5 h4,
  have h1 : shaves barber barber, from iff.elim_right h3 h2,
  show false, from h2 h1
end

section
  variable U : Type
  variables A B : U → Prop

  example : (∃ x, A x) → ∃ x, A x ∨ B x :=
  assume h1 : ∃ x, A x,
  show ∃ x, A x ∨ B x, from exists.elim h1
    (assume y (h2 : A y),
    have h3 : A y ∨ B y, from or.inl h2,
    show ∃ x, A x ∨ B x, from exists.intro y h3)
end

section
  variable U : Type
  variables A B : U → Prop

  variable h1 : ∀ x, A x → B x
  variable h2 : ∃ x, A x

  example : ∃ x, B x :=  
  show ∃ x, B x, from exists.elim h2
    (assume y (h3 : A y),
    have h4 : A y → B y, from h1 y,
    have h5 : B y, from h4 h3,
    show ∃ x, B x, from exists.intro y h5)
end

section
  variable  U : Type
  variables A B C : U → Prop

  example (h1 : ∃ x, A x ∧ B x) (h2 : ∀ x, B x → C x) :
  ∃ x, A x ∧ C x :=
    exists.elim h1
      (assume y (h3 : A y ∧ B y),
      have h4 : A y, from h3.left,
      have h5 : B y, from h3.right,
      have h6 : B y → C y, from h2 y,
      have h7 : C y, from h6 h5,
      have h8 : A y ∧ C y, from and.intro h4 h7,
      exists.intro y h8)
end
