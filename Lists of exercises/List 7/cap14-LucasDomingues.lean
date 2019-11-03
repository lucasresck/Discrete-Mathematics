-- Estudante: Lucas Emanuel Resck Domingues

-- Exercise 1

section
    parameters {A : Type} {R : A → A → Prop}
    parameter (irreflR : irreflexive R)
    parameter (transR : transitive R)

    local infix < := R

    def R' (a b : A) : Prop := R a b ∨ a = b
    local infix ≤ := R'

    theorem reflR' (a : A) : a ≤ a :=
        show a < a ∨ a = a, from or.inr rfl

    theorem transR' {a b c : A} (h1 : a ≤ b) (h2 : b ≤ c):
        a ≤ c :=
                have h3 : a < b ∨ a = b, from h1,
                have h4 : b < c ∨ b = c, from h2,
            show a < c ∨ a = c, from or.elim h3
                (assume h5 : a < b,
                or.elim h4
                    (assume h6 : b < c,
                        have h7 : a < c, from transR h5 h6,
                    or.inl h7)
                    (assume h6 : b = c,
                        have h7 : a < c, from eq.subst h6 h5,
                    or.inl h7))
                (assume h5 : a = b,
                or.elim h4
                    (assume h6 : b < c,
                        have h7 : a < c, from eq.substr h5 h6,
                    or.inl h7)
                    (assume h6 : b = c,
                        have h7 : a = c, from eq.substr h5 h6,
                    or.inr h7))     

    include irreflR
    include transR

    theorem antisymmR' {a b : A} (h1 : a ≤ b) (h2 : b ≤ a) :
    a = b :=
        begin
            cases h1,
                cases h2,
                    have h3, from transR h1 h2,
                    have h4, from irreflR a,
                    contradiction,
                apply eq.symm,
                assumption,
            assumption
        end
end

-- Exercise 2

section
    parameters {A : Type} {R : A → A → Prop}
    parameter (reflR : reflexive R)
    parameter (transR : transitive R)

    def S (a b : A) : Prop := R a b ∧ R b a

    include transR

    example : transitive S :=
        begin
            intros a b c h1 h2,
            cases h1 with h3 h4,
            cases h2 with h5 h6,
            apply and.intro,
                have h7, from transR h3 h5,
                assumption,
            exact transR h6 h4
        end
end

--Exercise 3

section
    parameters {A : Type} {a b c : A} {R : A → A → Prop}
    parameter (Rab : R a b)
    parameter (Rbc : R b c)
    parameter (nRac : ¬ R a c)

    -- Prove one of the following two theorems:

    theorem R_is_strict_partial_order :
    irreflexive R ∧ transitive R :=
    sorry

    -- Because nRac, R is not transitive, that is, it's not strict partial order.

    include Rab
    include Rbc
    include nRac

    theorem R_is_not_strict_partial_order :
    ¬(irreflexive R ∧ transitive R) :=
        begin
            intro h1,
            cases h1 with h2 h3,
            have Rac, from h3 Rab Rbc,
            contradiction
        end
end

-- Exercise 4

section
    open nat

    example : 1 ≤ 4 :=
        calc
            1 ≤ 1 : le_refl 1
          ... ≤ 2 : le_succ 1
          ... ≤ 3 : le_succ 2
          ... ≤ 4 : le_succ 3
end