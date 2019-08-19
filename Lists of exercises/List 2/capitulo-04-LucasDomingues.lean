variables A B C D : Prop

example : A ∧ (A → B) → B :=
    assume h : A ∧ (A → B),
    show B, from (and.right h) (and.left h)

example : A → ¬ (¬ A ∧ B) :=
    assume h1 : A,
    show ¬ (¬ A ∧ B), from
        assume h2 : ¬ A ∧ B,
        have h3 : ¬ A, from and.left h2,
        show false, from h3 h1

example : ¬ (A ∧ B) → (A → ¬ B) :=
    assume h1 : ¬ (A ∧ B),
    show A → ¬ B, from
        assume h2 : A,
        show ¬ B, from
            assume h3 : B,
            show false, from h1 (and.intro h2 h3)

example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
    or.elim h₁
        (assume h₄ : A,
        have h₆ : C, from h₂ h₄,
        show C ∨ D, from or.inl h₆)
        (assume h₅ : B,
        have h₇ : D, from h₃ h₅,
        show C ∨ D, from or.inr h₇)

example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
    assume h1 : A ∨ B,
    show false, from
        or.elim h1
        (assume h2: A,
        show false, from h.left h2)
        (assume h2: B,
        show false, from h.right h2)


example : ¬ (A ↔ ¬ A) :=
    assume h1 : A ↔ ¬ A,
    show false, from
        have h4: ¬ A, from 
            (assume h2 : A,
            have h3 : ¬ A, from iff.elim_left h1 h2,
            show false, from h3 h2),
        h4
        (show A, from
        iff.elim_right h1 h4)
