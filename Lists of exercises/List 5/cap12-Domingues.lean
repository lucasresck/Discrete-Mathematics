/-
aluno:
 - Lucas Emanuel Resck Domingues
 -/

open set


-- ex 1

section
    variable U : Type
    variables A B C : set U

    example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
        assume x,
        show x ∈ A ∩ C → x ∈ A ∪ B, from
            assume h1 : x ∈ A ∩ C,
            show x ∈ A ∪ B, from or.inl h1.left

    example : ∀ x, x ∈ -(A ∪ B) → x ∈ -A :=
        assume x,
        show x ∈ -(A ∪ B) → x ∈ -A, from
            assume h1 : x ∈ -(A ∪ B),
            show x ∈ -A, from
                assume h2 : x ∈ A,
                show false, from h1 $ or.inl h2
end


-- ex 2

section
    variable {U : Type}

    /- defining "disjoint" -/

    def disj (A B : set U) : Prop := ∀ ⦃x⦄, x ∈ A → x ∈ B → false

    example (A B : set U) (h : ∀ x, ¬ (x ∈ A ∧ x ∈ B)) :
    disj A B :=
        assume x,
            assume h1 : x ∈ A,
                assume h2 : x ∈ B,
                have h3 : x ∈ A ∧ x ∈ B, from and.intro h1 h2,
                show false, from h x h3

    -- notice that we do not have to mention x when applying
    --   h : disj A B
    example (A B : set U) (h1 : disj A B) (x : U)
        (h2 : x ∈ A) (h3 : x ∈ B) :
    false :=
        h1 h2 h3

    -- the same is true of ⊆
    example (A B : set U) (x : U) (h : A ⊆ B) (h1 : x ∈ A) :
    x ∈ B :=
        h h1

    example (A B C D : set U) (h1 : disj A B) (h2 : C ⊆ A)
        (h3 : D ⊆ B) :
    disj C D :=
        assume x,
        show x ∈ C → x ∈ D → false, from
            assume h4 : x ∈ C,
            show x ∈ D → false, from
                assume h5 : x ∈ D,
                show false, from h1 (h2 h4) (h3 h5)
end


-- ex 3

section
    variables {I U : Type}
    variables {A B : I → set U}

    def Union (A : I → set U) : set U := { x | ∃ i : I, x ∈ A i }
    def Inter (A : I → set U) : set U := { x | ∀ i : I, x ∈ A i }

    notation `⋃` binders `, ` r:(scoped f, Union f) := r
    notation `⋂` binders `, ` r:(scoped f, Inter f) := r

    theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i :=
    by simp; assumption

    @[elab_simple]
    theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i :=
    by simp at h; apply h

    theorem Union.intro {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i :=
    by {simp, existsi i, exact h}

    theorem Union.elim {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b :=
    by {simp at h₁, cases h₁ with i h, exact h₂ i h}
end

section
    variables {I U : Type}

    variables (A : I → set U) (B : I → set U) (C : set U)

    example : (⋂ i, A i) ∩ (⋂ i, B i) ⊆ (⋂ i, A i ∩ B i) :=
        assume x,
        show x ∈ (⋂ i, A i) ∩ (⋂ i, B i) → x ∈ (⋂ i, A i ∩ B i), from
            assume h1 : x ∈ (⋂ i, A i) ∩ (⋂ i, B i),
            have h2 : x ∈ (⋂ i, A i), from h1.left,
            have h3 : x ∈ (⋂ i, B i), from h1.right,
            show x ∈ (⋂ i, A i ∩ B i), from Inter.intro $
                assume i,
                have h4 : x ∈ A i, from Inter.elim h2 i,
                have h5 : x ∈ B i, from Inter.elim h3 i,
                show x ∈ A i ∩ B i, from and.intro h4 h5

    example : C ∩ (⋃i, A i) ⊆ ⋃i, C ∩ A i :=
        assume x,
        show x ∈ C ∩ (⋃i, A i) → x ∈ ⋃i, C ∩ A i, from
            assume h1 : x ∈ C ∩ (⋃i, A i),
            have h2 : x ∈ ⋃i, A i, from h1.right,
            have h5 : x ∈ C, from h1.left,
            show x ∈ ⋃i, C ∩ A i, from Union.elim h2 $
                assume i,
                show x ∈ A i →  x ∈ ⋃j, C ∩ A j, from
                    assume h3 : x ∈ A i,
                    have h4 : x ∈ C ∩ A i, from and.intro h5 h3,  
                    show x ∈ ⋃j, C ∩ A j, from Union.intro i h4
end


-- ex 4

section 
    variable  {U : Type}
    variables A B C : set U
    universes u v w x

    theorem subset.refl (A : set U) : A ⊆ A :=
        assume x,
        show x ∈ A → x ∈ A, from
            assume h : x ∈ A,
            show x ∈ A, from h

    theorem subset.trans {A B C : set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
        assume x,
        show x ∈ A → x ∈ C, from
            assume h3 : x ∈ A,
            have h4 : x ∈ B, from h1 h3,
            show x ∈ C, from h2 h4

    -- For this exercise these two facts are useful
    example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
    subset.trans h1 h2

    example : A ⊆ A :=
    subset.refl A

    example (h : A ⊆ B) : powerset A ⊆ powerset B :=
        assume X : set U,
        show X ∈ powerset A → X ∈ powerset B, from
            assume h1 : X ∈ powerset A,
            have h2 : X ⊆ A, from h1,
            have h3 : X ⊆ B, from subset.trans h2 h,
            show X ∈ powerset B, from h3

    example (h : powerset A ⊆ powerset B) : A ⊆ B :=
        assume x,
        show x ∈ A → x ∈ B, from
            assume h1 : x ∈ A,
            have h2 : ∀ X, X ⊆ A → X ⊆ B, from h,
            have h3 : A ⊆ A, from subset.refl A,
            have h4 : A ⊆ B, from h2 A h3,
            show x ∈ B, from h4 h1
end

