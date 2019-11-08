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