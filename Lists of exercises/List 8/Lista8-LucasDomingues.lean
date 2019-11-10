-- Estudante: Lucas Emanuel Resck Domingues

open nat

--1.a.
example : ∀ m n k : nat, m * (n + k) = m * n + m * k :=
    assume m n k,
        nat.rec_on k
            (show m * (n + 0) = m * n + m * 0, from calc
                m * (n + 0) = m * n         : by rw add_zero
                        ... = m * n + 0     : by rw add_zero
                        ... = m * n + m * 0 : by rw mul_zero)
            (assume p,
                assume ih: m * (n + p) = m * n + m * p,
                show m * (n + succ p) = m * n + m * (succ p), from
                    calc
                        m * (n + succ p) = m * (succ (n + p)) : by rw add_succ
                                     ... = m * (n + p) + m : by rw mul_succ
                                     ... = m * n + m * p + m : by rw ih
                                     ... = m * n + (m * p + m) : by rw add_assoc
                                     ... = m * n + m * (succ p) : by rw mul_succ)

--1.b.
example : ∀ n : nat, 0 * n = 0 :=
    assume n,
        nat.rec_on n
            (show 0 * 0 = 0, from rfl)
            (assume k,
                assume ih : 0 * k = 0,
                show 0 * (succ k) = 0, from
                    calc
                        0 * (succ k) = 0 * k + 0 : by rw mul_succ
                                ... = 0 * k : by rw add_zero
                                ... = 0 : by rw ih)


--1.c.
example : ∀ n : nat, 1 * n = n :=
    assume n,
        nat.rec_on n
            (show 1 * 0 = 0, by rw mul_zero)
            (assume k,
                assume ih : 1 * k = k,
                    calc
                        1 * (succ k) = 1 * k + 1 : by rw mul_succ
                                ... = k + 1 : by rw ih
                                ... = succ k : rfl)

--1.d.
example : ∀ m n k : nat, (m * n) * k = m * (n * k) :=
    assume m n k,
        nat.rec_on k
            (show (m * n) * 0 = m * (n * 0), from
                calc
                    (m * n) * 0 = 0 : by rw mul_zero
                            ... = m * 0 : by rw mul_zero
                            ... = 0 * m : by rw mul_comm
                            ... = (n * 0) * m : by rw mul_zero
                            ... = m * (n * 0) : by rw mul_comm)
            (assume i (ih : (m * n) * i = m * (n * i)),
            show (m * n) * succ i = m * (n * succ i), from
                begin
                    rw mul_succ,
                    rw ih,
                    rw ← left_distrib,
                    rw mul_succ
                end)

--1.e.
example : ∀ m n : nat, m * n = n * m :=
    assume m n,
        nat.rec_on n
            (begin
                rw mul_zero,
                apply eq.symm,                
                rw zero_mul
            end)
            (begin
                intros k ih,
                rw mul_succ,
                rw ih,
                rw succ_mul
            end)

--2.a.
example : ∀ m n k : nat, n ≤ m → n + k ≤ m + k :=
    assume m n k (h1 : n ≤ m),
    show n + k ≤ m + k, from nat.rec_on k
        h1
        (begin
            intros k' ih,
            have h2, from succ_le_succ ih,
            rw add_succ,
            rw add_succ,
            exact h2
        end)
            
--2.b.
example : ∀ m n k : nat, n + k ≤ m + k → n ≤ m :=
    begin
        intros m n k,
        apply nat.rec_on k,
            intro h1,
            exact h1,
        intros k' h1 h2,
        apply h1,
        apply le_of_succ_le_succ,
        rw ← add_succ,
        rw ← add_succ,
        exact h2
    end


--2.c.
example : ∀ m n k : nat, n ≤ m → n * k ≤ m * k :=
    assume m n k (h1 : n ≤ m),
    nat.rec_on k
        (le_refl 0)
        (assume k' (ih : n * k' ≤ m * k'),
        show n * succ k' ≤ m * succ k', from calc
            n * succ k' = n * k' + n : by rw mul_succ
                    ... ≤ m * k' + n : add_le_add_right ih n
                    ... ≤ m * k' + m : add_le_add_left h1 (m * k')
                    ... = m * succ k' : by rw mul_succ
        )

--2.d.
example : ∀ m n : nat, m ≥ n → m = n ∨ m ≥ n + 1 :=
    begin
        intros m n,
        apply nat.rec_on n,
            intro h1,
            apply classical.by_contradiction,
            intro h2,
            have h3 : ¬(m = 0) ∧ ¬(m ≥ 0 + 1), from
                begin
                    apply and.intro,
                        intro h4,
                        have h5 : m = 0 ∨ m ≥ 0 + 1, from or.inl h4,
                        exact h2 h5,
                    intro h3,
                    have h4 : m = 0 ∨ m ≥ 0 + 1, from or.inr h3,
                    exact h2 h4
                end,
            cases h3 with h4 h5,
            have h6 : m ≠ 0, from h4,
            have h7 : 0 ≤ m, from h1,
            apply h5,
            have h8 : 0 < m, from nat.lt_of_le_and_ne h7 h6.symm,
            apply le_of_lt_succ,
            apply succ_lt_succ,
            exact h8,
        intros k ih h1,
        apply classical.by_contradiction,
        intro h2,
        have h3 : ¬(m = succ k) ∧ ¬(m ≥ succ k + 1), from
            begin
                apply and.intro,
                    intro h4,
                    have h5 : m = succ k ∨ m ≥ succ k + 1, from or.inl h4,
                    exact h2 h5,
                intro h3,
                have h4 : m = succ k ∨ m ≥ succ k + 1, from or.inr h3,
                exact h2 h4
            end,
        cases h3 with h4 h5,
        have h6 : m ≠ succ k, from h4,
        have h7 : succ k ≤ m, from h1,
        apply h5,
        have h8 : succ k < m, from nat.lt_of_le_and_ne h7 h6.symm,
        apply le_of_lt_succ,
        apply succ_lt_succ,
        exact h8
    end
--2.e.
example : ∀ n : nat, 0 ≤ n :=
    begin
        intro n,
        apply nat.rec_on n,
            exact zero_le 0,
        intros k ih,
        have h1 : k ≤ succ k, from le_succ k,
        exact le_trans ih h1
    end
