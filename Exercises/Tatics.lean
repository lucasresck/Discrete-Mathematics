theorem exercise {U : Type} {A B : set U} : (A \ B) ∪ (B \ A) ⊆  (A ∪ B) \ (A ∩ B):=
    begin
        intros x h1,
        cases h1 with h1 h2,
            cases h1 with h3 h4,
            apply and.intro,
                exact or.inl h3,
            intro h5,
            have h6, from h5.right,
            exact h4 h6,
        apply and.intro,
        have h3, from h2.left,
        exact or.inr h3,
        intro h3,
        have h4, from h2.right,
        have h5, from h3.left,
        exact h4 h5
    end