variable U : Type
variables A B C : set U

example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
    begin
        assume x,
        intro,
        have h1, from a.left,
        exact or.inl h1,
    end

example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
    assume x,
    show x ∈ A ∩ C → x ∈ A ∪ B, from
        assume h1 : x ∈ A ∩ C,
        show x ∈ A ∪ B, from or.inl h1.left

example : ∀ x, x ∈ -(A ∪ B) → x ∈ -A :=
    begin
        intros x h1 h2,
        apply h1,
        exact or.inl h2
    end

example : ∀ x, x ∈ -(A ∪ B) → x ∈ -A :=
    assume x,
        assume h1 : x ∈ -(A ∪ B),
        show x ∈ -A, from
            assume h2 : x ∈ A,
            show false, from h1 $ or.inl h2