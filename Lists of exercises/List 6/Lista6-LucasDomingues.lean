-- Estudante: Lucas Emanuel Resck Domingues

open set

variable U : Type
variables A B : set U

lemma eq_of_subset_of_subset {U : Type} {A B : set U} (h1 : A ⊆ B) (h2 : B ⊆ A): A = B := sorry 

lemma first {U : Type} {A B : set U}: powerset (A ∩ B) ⊆ powerset A ∩ powerset B :=
    assume X,
    show X ∈ powerset (A ∩ B) → X ∈ powerset A ∩ powerset B, from
        assume h1 : X ∈ powerset (A ∩ B),
            have h2 : ∀ x, x ∈ X → x ∈ A ∩ B, from h1,
            have h3 : ∀ x, x ∈ X → x ∈ A, from
                (assume x,
                    assume h4 : x ∈ X,
                    show x ∈ A, from (h2 x h4).left),
            have h4 : X ∈ powerset A, from h3,
            have h5 : ∀ x, x ∈ X → x ∈ B, from
                (assume x,
                    assume h6 : x ∈ X,
                    show x ∈ B, from (h2 x h6).right),
            have h6 : X ∈ powerset B, from h5,
        show X ∈ powerset A ∩ powerset B, from and.intro h4 h6

lemma second {U : Type} {A B : set U}: powerset A ∩ powerset B ⊆ powerset (A ∩ B) :=
    assume X,
        assume h1 : X ∈ powerset A ∩ powerset B,
            have h2 : ∀ x, x ∈ X → x ∈ A, from h1.left,
            have h3 : ∀ x, x ∈ X → x ∈ B, from h1.right,
            have h4 : ∀ x, x ∈ X → x ∈ A ∩ B, from
                (assume x,
                    assume h5 : x ∈ X,
                        have h6 : x ∈ A, from h2 x h5,
                        have h7 : x ∈ B, from h3 x h5,
                    show x ∈ A ∩ B, from and.intro h6 h7),
        show X ∈ powerset (A ∩ B), from h4

theorem exercise : powerset (A ∩ B) = powerset A ∩ powerset B :=
    eq_of_subset_of_subset
        first
        second
