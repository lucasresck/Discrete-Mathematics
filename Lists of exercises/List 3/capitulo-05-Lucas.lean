variables A B C P Q R: Prop

open classical

theorem exercise_1 (h1 : ¬ A → false) (h2 : A ∨ ¬ A) : A :=
  or.elim h2
    (assume h3 : A,
    show A, from h3)
    (assume h4 : ¬ A,
    have h5 : false, from h1 h4,
    show A, from false.elim h5)

theorem exercise_2 (h1 : ¬ A ∨ ¬ B) : ¬ (A ∧ B) :=
  assume h2 : A ∧ B,
  have h3 : A, from and.left h2,
  have h4 : B, from and.right h2,
  show false, from or.elim h1
    (assume h5 : ¬ A,
    show false, from h5 h3)
    (assume h6 : ¬ B,
    show false, from h6 h4)

theorem exercise_3 (h1 : ¬ (A ∧ B)) : ¬ A ∨ ¬ B :=
  by_contradiction
  (assume h2 : ¬ (¬ A ∨ ¬ B),
  have h4 : A, from
    (by_contradiction
    (assume h6 : ¬ A,
    have h7 : ¬ A ∨ ¬ B, from or.inl h6,
    show false, from h2 h7)),
  have h5 : B, from
    (by_contradiction
    (assume h6 : ¬ B,
    have h7 : ¬ A ∨ ¬ B, from or.inr h6,
    show false, from h2 h7)),
  have h3 : A ∧ B, from and.intro h4 h5,
  show false, from h1 h3)

theorem exercise_4 (h1 : ¬ P → (Q ∨ R)) (h2 : ¬ Q) (h3 : ¬ R) : P :=
  by_contradiction
  (assume h4 : ¬ P,
  have h5 : Q ∨ R, from h1 h4,
  show false, from or.elim h5
    (assume h6 : Q,
    show false, from h2 h6)
    (assume h6 : R,
    show false, from h3 h6))

theorem exercise_5 (h1 : A → B) : ¬ A ∨ B :=
  by_contradiction
  (assume h2 : ¬ (¬ A ∨ B),
  have h4 : ¬ A, from
    (assume h5 : A,
    have h7 : B, from h1 h5,
    have h6 : ¬ A ∨ B, from or.inr h7,
    show false, from h2 h6),
  have h3 : ¬ A ∨ B, from or.inl h4,
  show false, from h2 h3)

theorem exercise_6 : A → ((A ∧ B) ∨ (A ∧ ¬ B)) :=
  (assume h1 : A,
  show ((A ∧ B) ∨ (A ∧ ¬ B)), from
    by_contradiction
    (assume h2 : ¬ (((A ∧ B) ∨ (A ∧ ¬ B))),
    have h5 : ¬ B, from
      (assume h6 : B,
      have h8 : A ∧ B, from and.intro h1 h6,
      have h7 : (A ∧ B) ∨ (A ∧ ¬ B), from or.inl h8,
      show false, from h2 h7),
    have h4 : A ∧ ¬ B, from and.intro h1 h5,
    have h3 : (A ∧ B) ∨ (A ∧ ¬ B), from or.inr h4,
    show false, from h2 h3))

--Exercise 8

-- Prove ¬ (A ∧ B) → ¬ A ∨ ¬ B by replacing the sorry's below
-- by proofs.

lemma step1 {A B : Prop} (h₁ : ¬ (A ∧ B)) (h₂ : A) : ¬ A ∨ ¬ B :=
have ¬ B, from 
  (assume h₃ : B,
  show false, from h₁ (and.intro h₂ h₃)),
show ¬ A ∨ ¬ B, from or.inr this

lemma step2 {A B : Prop} (h₁ : ¬ (A ∧ B)) (h₂ : ¬ (¬ A ∨ ¬ B)) : false :=
have ¬ A, from
  assume : A,
  have ¬ A ∨ ¬ B, from step1 h₁ ‹A›,
  show false, from h₂ this,
show false, from h₂ (or.inl this)

theorem step3 (h : ¬ (A ∧ B)) : ¬ A ∨ ¬ B :=
by_contradiction
  (assume h' : ¬ (¬ A ∨ ¬ B),
    show false, from step2 h h')

--Exercise 9

example (h : ¬ B → ¬ A) : A → B :=
  assume h1 : A,
  show B, from
    by_contradiction
    (assume h2 : ¬ B,
    show false, from (h h2) h1)

example (h : A → B) : ¬ A ∨ B :=
  by_contradiction
  (assume h1 : ¬ (¬ A ∨ B),
  have h3 : ¬ A, from
    assume h4 : A,
    have h6 : B, from h h4,
    have h5 : ¬ A ∨ B, from or.inr h6,
    show false, from h1 h5,
  have h2 : ¬ A ∨ B, from or.inl h3,
  show false, from h1 h2)
