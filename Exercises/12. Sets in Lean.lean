import data.set
open set

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
sorry
end
