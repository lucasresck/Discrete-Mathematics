variables P11 P12 P21 P22 P31 P32 : Prop

lemma fifth_or_elim {P11 P12 P21 P22 P31 P32 : Prop}
(h3 : P12) (h5 : P21) (h6 : P31 ∨ P32) :
((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)) :=
    or.elim h6
        (assume h7 : P31,
        show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
        ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from or.inl (or.inr (or.inr (and.intro h5 h7))))
        (assume h7 : P32,
        show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
        ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from or.inr (or.inr (or.inl (and.intro h3 h7))))

lemma fourth_or_elim {P11 P12 P21 P22 P31 P32 : Prop}
(h1 : (P11 ∨ P12) ∧ (P21 ∨ P22) ∧ (P31 ∨ P32)) (h3 : P12) (h4 : P21 ∨ P22) :
((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)) :=
    or.elim h4
    (assume h5 : P21,
    have h6 : P31 ∨ P32, from and.right (and.right h1),
    show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
    ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from fifth_or_elim h3 h5 h6)
    (assume h5 : P22,
    show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
    ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from or.inr (or.inl (and.intro h3 h5)))

lemma third_or_elim {P11 P12 P21 P22 P31 P32 : Prop}
(h3 : P11) (h5 : P22) (h6 : P31 ∨ P32) :
((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)) :=
    or.elim h6
        (assume h7 : P31,
        show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
        ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from or.inl (or.inr (or.inl (and.intro h3 h7))))
        (assume h7 : P32,
        show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
        ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from or.inr (or.inr (or.inr (and.intro h5 h7))))

lemma second_or_elim {P11 P12 P21 P22 P31 P32 : Prop}
(h1 : (P11 ∨ P12) ∧ (P21 ∨ P22) ∧ (P31 ∨ P32)) (h3 : P11) (h4 : P21 ∨ P22) :
((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)) :=
    or.elim h4
    (assume h5 : P21,
    have h6 : P31 ∨ P32, from and.right (and.right h1),
    show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
    ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from or.inl (or.inl (and.intro h3 h5)))
    (assume h5 : P22,
    have h6 : P31 ∨ P32, from and.right (and.right h1),
    show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
    ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from third_or_elim h3 h5 h6)

lemma first_or_elim {P11 P12 P21 P22 P31 P32 : Prop}
(h1 : (P11 ∨ P12) ∧ (P21 ∨ P22) ∧ (P31 ∨ P32)) (h2 : P11 ∨ P12) :
((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)) :=
    or.elim h2
    (assume h3 : P11,
    have h4 : P21 ∨ P22, from and.left (and.right h1),
    show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
    ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from second_or_elim h1 h3 h4)
    (assume h3 : P12,
    have h4 : P21 ∨ P22, from and.left (and.right h1),
    show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
    ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from fourth_or_elim h1 h3 h4)

theorem PHP3 : (P11 ∨ P12) ∧ (P21 ∨ P22) ∧ (P31 ∨ P32) → 
((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)) :=
    assume h1 : (P11 ∨ P12) ∧ (P21 ∨ P22) ∧ (P31 ∨ P32),
    have h2 : P11 ∨ P12, from and.left h1,
    show ((P11 ∧ P21) ∨ (P11 ∧ P31) ∨ (P21 ∧ P31)) ∨
    ((P12 ∧ P22) ∨ (P12 ∧ P32) ∨ (P22 ∧ P32)), from first_or_elim h1 h2
