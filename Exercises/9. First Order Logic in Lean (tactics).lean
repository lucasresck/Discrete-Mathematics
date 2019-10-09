section
    variable A : Type
    variable f : A → A
    variable P : A → Prop
    variable h : ∀ x, P x → P (f x)

    include h

    -- Show the following:
    example : ∀ y, P y → P (f (f y)) :=
        begin
            intros,
            have h1 : P y → P (f y), from h y,
            have h2 : P (f y), from h1 a,
            have h3 : P (f y) → P (f (f y)), from h (f y),
            have h4 : P (f (f y)), from h3 h2,
            assumption
        end
end

section
    variable U : Type
    variables A B : U → Prop

    example : (∀ x, A x ∧ B x) → ∀ x, A x :=
        begin
            intro, 
            intro,
            exact (a x).left
        end
end

section
    variable U : Type
    variables A B C : U → Prop

    variable h1 : ∀ x, A x ∨ B x
    variable h2 : ∀ x, A x → C x
    variable h3 : ∀ x, B x → C x

    include h1 h2 h3

    example : ∀ x, C x :=
        begin
            intro x,
            have h4, from h1 x,
            cases h4,
                exact h2 x h4,
            exact h3 x h4
        end
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
    
    include Person shaves barber h

    -- Show the following:
    example : false :=
        begin
            have h1, from h barber,
            have h2, from iff.elim_left h1,
            have h3, from iff.elim_right h1,
            have h5, from
                assume h4 : shaves barber barber,
                show false, from (h2 h4) h4,            
            have h6, from
                by_contradiction
                (assume h4 : ¬ shaves barber barber,
                show false, from h4 (h3 h4)),
            exact h5 h6       
        end
end
