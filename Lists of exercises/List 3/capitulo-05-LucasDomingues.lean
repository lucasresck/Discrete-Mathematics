variables A B C D E F P Q R: Prop

open classical

theorem exercise_1 (h1 : ¬ A → false) (h2 : A ∨ ¬ A) : A :=
  or.elim h2
    (assume h3 : A, h3)
    (assume h4 : ¬ A,
    have h5 : false, from h1 h4,
    show A, from false.elim h5)

theorem exercise_2 (h1 : ¬ A ∨ ¬ B) : ¬ (A ∧ B) :=
  assume h2 : A ∧ B,
  have h3 : A, from and.left h2,
  have h4 : B, from and.right h2,
  show false, from or.elim h1
    (assume h5 : ¬ A, h5 h3)
    (assume h6 : ¬ B, h6 h4)

theorem exercise_3 (h1 : ¬ (A ∧ B)) : ¬ A ∨ ¬ B :=
  by_contradiction
  (assume h2 : ¬ (¬ A ∨ ¬ B),
  have h4 : A, from
    by_contradiction
    (assume h6 : ¬ A,
    have h7 : ¬ A ∨ ¬ B, from or.inl h6,
    show false, from h2 h7),
  have h5 : B, from
    by_contradiction
    (assume h6 : ¬ B,
    have h7 : ¬ A ∨ ¬ B, from or.inr h6,
    show false, from h2 h7),
  have h3 : A ∧ B, from and.intro h4 h5,
  show false, from h1 h3)

theorem exercise_4 (h1 : ¬ P → (Q ∨ R)) (h2 : ¬ Q) (h3 : ¬ R) : P :=
  by_contradiction
  (assume h4 : ¬ P,
  have h5 : Q ∨ R, from h1 h4,
  show false, from or.elim h5
    (assume h6 : Q, h2 h6)
    (assume h6 : R, h3 h6))

theorem exercise_5 (h1 : A → B) : ¬ A ∨ B :=
  by_contradiction
  (assume h2 : ¬ (¬ A ∨ B),
  have h4 : ¬ A, from
    assume h5 : A,
    have h7 : B, from h1 h5,
    have h6 : ¬ A ∨ B, from or.inr h7,
    show false, from h2 h6,
  have h3 : ¬ A ∨ B, from or.inl h4,
  show false, from h2 h3)

theorem exercise_6 : A → ((A ∧ B) ∨ (A ∧ ¬ B)) :=
  assume h1 : A,
    by_contradiction
    (assume h2 : ¬ (((A ∧ B) ∨ (A ∧ ¬ B))),
    have h5 : ¬ B, from
      assume h6 : B,
      have h8 : A ∧ B, from and.intro h1 h6,
      have h7 : (A ∧ B) ∨ (A ∧ ¬ B), from or.inl h8,
      show false, from h2 h7,
    have h4 : A ∧ ¬ B, from and.intro h1 h5,
    have h3 : (A ∧ B) ∨ (A ∧ ¬ B), from or.inr h4,
    show false, from h2 h3)

-- Exercise 7

lemma fourth {A B C D E F : Prop} (h1 : A ∨ B) (h2 : C ∨ D) (h3 : E ∨ F) :
(((A ∧ (C ∧ E)) ∨ (A ∧ (C ∧ F))) ∨ ((A ∧ (D ∧ E)) ∨ (A ∧ (D ∧ F)))) ∨
(((B ∧ (C ∧ E)) ∨ (B ∧ (C ∧ F))) ∨ ((B ∧ (D ∧ E)) ∨ (B ∧ (D ∧ F)))) :=
-- I will now suppose very each case above, and include the other terms of conjunction
    or.elim h1
    (assume h4 : A,
        or.elim h2
        (assume h5 : C,
            or.elim h3
            (assume h6 : E,
            -- I have now A ∧ C ∧ E, so I can have all the proposition, like bellow
            or.inl (or.inl (or.inl (and.intro h4 (and.intro h5 h6)))))
            (assume h6 : F,
            or.inl (or.inl (or.inr (and.intro h4 (and.intro h5 h6))))))
        (assume h5 : D,
            or.elim h3
            (assume h6 : E,
            or.inl (or.inr (or.inl (and.intro h4 (and.intro h5 h6)))))
            (assume h6 : F,
            or.inl (or.inr (or.inr (and.intro h4 (and.intro h5 h6)))))))
    (assume h4 : B,
        or.elim h2
        (assume h5 : C,
            or.elim h3
            (assume h6 : E,
            or.inr (or.inl (or.inl (and.intro h4 (and.intro h5 h6)))))
            (assume h6 : F,
            or.inr (or.inl (or.inr (and.intro h4 (and.intro h5 h6))))))
        (assume h5 : D,
            or.elim h3
            (assume h6 : E,
            or.inr (or.inr (or.inl (and.intro h4 (and.intro h5 h6)))))
            (assume h6 : F,
            or.inr (or.inr (or.inr (and.intro h4 (and.intro h5 h6)))))))

lemma third {A B C D E F : Prop} (h1 : (A ∧ (C ∧ E)) ∨ (A ∧ (C ∧ F))): (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F) :=
    or.elim h1
    (assume h2 : A ∧ (C ∧ E),
    have h3 : A ∨ B, from or.inl (and.left h2),
    have h4 : C ∧ E, from and.right h2,
    have h5 : C ∨ D, from or.inl (and.left h4),
    have h6 : E ∨ F, from or.inl (and.right h4),
    and.intro h3 (and.intro h5 h6))
    (assume h2 : A ∧ (C ∧ F),
    have h3 : A ∨ B, from or.inl (and.left h2),
    have h4 : C ∧ F, from and.right h2,
    have h5 : C ∨ D, from or.inl (and.left h4),
    have h6 : E ∨ F, from or.inr (and.right h4),
    and.intro h3 (and.intro h5 h6))

lemma switch {A B : Prop} (h1 : A ∨ B) : B ∨ A :=
    or.elim h1
    (assume h2 : A, or.inr h2)
    (assume h2 : B, or.inl h2)

lemma second {A B C D E F : Prop}
(h1 : ((A ∧ (C ∧ E)) ∨ (A ∧ (C ∧ F))) ∨ ((A ∧ (D ∧ E)) ∨ (A ∧ (D ∧ F)))): (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F) :=
    or.elim h1
    (assume h2 : (A ∧ (C ∧ E)) ∨ (A ∧ (C ∧ F)),
    third h2)
    (assume h2 : (A ∧ (D ∧ E)) ∨ (A ∧ (D ∧ F)),
    -- Now I can use third lemma again, but later I will have to switch C and D
    have h3 : (A ∨ B) ∧ (D ∨ C) ∧ (E ∨ F), from third h2,
    have h4 : A ∨ B, from and.left h3,
    have h5 : D ∨ C, from and.left (and.right h3),
    have h6 : C ∨ D, from switch h5,
    have h7 : E ∨ F, from and.right (and.right h3),
    and.intro h4 (and.intro h6 h7))

lemma first {A B C D E F : Prop}
(h1 : (((A ∧ (C ∧ E)) ∨ (A ∧ (C ∧ F))) ∨ ((A ∧ (D ∧ E)) ∨ (A ∧ (D ∧ F)))) ∨
(((B ∧ (C ∧ E)) ∨ (B ∧ (C ∧ F))) ∨ ((B ∧ (D ∧ E)) ∨ (B ∧ (D ∧ F))))): (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F) :=
    or.elim h1
    (assume h2 : ((A ∧ (C ∧ E)) ∨ (A ∧ (C ∧ F))) ∨ ((A ∧ (D ∧ E)) ∨ (A ∧ (D ∧ F))),
    second h2)
    (assume h2 : ((B ∧ (C ∧ E)) ∨ (B ∧ (C ∧ F))) ∨ ((B ∧ (D ∧ E)) ∨ (B ∧ (D ∧ F))),
    have h3 : (B ∨ A) ∧ (C ∨ D) ∧ (E ∨ F), from second h2,
    have h4 : B ∨ A, from and.left h3,
    have h5 : A ∨ B, from switch h4,
    have h6 : (C ∨ D) ∧ (E ∨ F), from and.right h3,
    and.intro h5 h6)

theorem exercise_7 : (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F) ↔
(((A ∧ (C ∧ E)) ∨ (A ∧ (C ∧ F))) ∨ ((A ∧ (D ∧ E)) ∨ (A ∧ (D ∧ F)))) ∨
(((B ∧ (C ∧ E)) ∨ (B ∧ (C ∧ F))) ∨ ((B ∧ (D ∧ E)) ∨ (B ∧ (D ∧ F)))) :=
    iff.intro
    (assume h1 : (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F),
    have h2 : A ∨ B, from h1.left,
    have h3 : C ∨ D, from (h1.right).left,
    have h4 : E ∨ F, from (h1.right).right,
    fourth h2 h3 h4)
    (assume h1 : (((A ∧ (C ∧ E)) ∨ (A ∧ (C ∧ F))) ∨ ((A ∧ (D ∧ E)) ∨ (A ∧ (D ∧ F)))) ∨
    (((B ∧ (C ∧ E)) ∨ (B ∧ (C ∧ F))) ∨ ((B ∧ (D ∧ E)) ∨ (B ∧ (D ∧ F)))),
    first h1)

-- Exercise 8

-- Prove ¬ (A ∧ B) → ¬ A ∨ ¬ B by replacing the sorry's below
-- by proofs.

lemma step1 {A B : Prop} (h₁ : ¬ (A ∧ B)) (h₂ : A) : ¬ A ∨ ¬ B :=
    have ¬ B, from 
        assume h₃ : B,
        show false, from h₁ (and.intro h₂ h₃),
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

-- Exercise 9

example (h : ¬ B → ¬ A) : A → B :=
  assume h1 : A,
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
