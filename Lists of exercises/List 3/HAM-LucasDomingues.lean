-- Reduction of Hamiltonian path to SAT problem

-- My graph is G = {(1, 2), (1, 3), (1, 4), (2, 3)}

-- x_ij means the ith position of Hamiltonian path is occupied by node j
variables   x11 x12 x13 x14
            x21 x22 x23 x24
            x31 x32 x33 x34
            x41 x42 x43 x44 : Prop

-- Any path:
variables path: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧
                x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
                ¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧
                ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44

-- Now I have to show that this path satisfies (or not) the conditions of a Hamiltonian path.

-- Every node needs to appear in the path:

theorem node_1_in_the_path (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) : x11 ∨ x21 ∨ x31 ∨ x41 :=
    or.inr (or.inl path.right.right.right.right.left)

theorem node_2_in_the_path (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) : x12 ∨ x22 ∨ x32 ∨ x42 :=
    or.inr (or.inr (or.inl path.right.right.right.right.right.right.right.right.right.left))

theorem node_3_in_the_path (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) : x13 ∨ x23 ∨ x33 ∨ x43 :=
    or.inr (or.inr (or.inr path.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left))

theorem node_4_in_the_path (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) : x14 ∨ x24 ∨ x34 ∨ x44 :=
    or.inl path.right.right.right.left

-- No node appears twice in the path:

theorem node_1_not_twice (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) :
(¬ x11 ∨ ¬ x21) ∧ (¬ x11 ∨ ¬ x31) ∧ (¬ x11 ∨ ¬ x41) ∧
(¬ x21 ∨ ¬ x31) ∧ (¬ x21 ∨ ¬ x41) ∧ (¬ x31 ∨ ¬ x41) :=
    have h₁ : ¬ x11, from path.left,
    have h₂ : ¬ x31, from path.right.right.right.right.right.right.right.right.left,
    have h₃ : ¬ x41, from path.right.right.right.right.right.right.right.right.right.right.right.right.left,
    and.intro (or.inl h₁) (and.intro (or.inl h₁) (and.intro (or.inl h₁)
    (and.intro (or.inr h₂) (and.intro (or.inr h₃) (or.inr h₃)))))

theorem node_2_not_twice (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) :
(¬ x12 ∨ ¬ x22) ∧ (¬ x12 ∨ ¬ x32) ∧ (¬ x12 ∨ ¬ x42) ∧
(¬ x22 ∨ ¬ x32) ∧ (¬ x22 ∨ ¬ x42) ∧ (¬ x32 ∨ ¬ x42) :=
    have h₁ : ¬ x12, from path.right.left,
    have h₂ : ¬ x22, from path.right.right.right.right.right.left,
    have h₃ : ¬ x42, from path.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
    and.intro (or.inl h₁) (and.intro (or.inl h₁) (and.intro (or.inl h₁)
    (and.intro (or.inl h₂) (and.intro (or.inr h₃) (or.inr h₃)))))

theorem node_3_not_twice (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) :
(¬ x13 ∨ ¬ x23) ∧ (¬ x13 ∨ ¬ x33) ∧ (¬ x13 ∨ ¬ x43) ∧
(¬ x23 ∨ ¬ x33) ∧ (¬ x23 ∨ ¬ x43) ∧ (¬ x33 ∨ ¬ x43) :=
    have h₁ : ¬ x13, from path.right.right.left,
    have h₂ : ¬ x23, from path.right.right.right.right.right.right.left,
    have h₃ : ¬ x33, from path.right.right.right.right.right.right.right.right.right.right.left,
    and.intro (or.inl h₁) (and.intro (or.inl h₁) (and.intro (or.inl h₁)
    (and.intro (or.inl h₂) (and.intro (or.inl h₂) (or.inl h₃)))))

theorem node_4_not_twice (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) :
(¬ x14 ∨ ¬ x24) ∧ (¬ x14 ∨ ¬ x34) ∧ (¬ x14 ∨ ¬ x44) ∧
(¬ x24 ∨ ¬ x34) ∧ (¬ x24 ∨ ¬ x44) ∧ (¬ x34 ∨ ¬ x44) :=
    have h₁ : ¬ x24, from path.right.right.right.right.right.right.right.left,
    have h₂ : ¬ x34, from path.right.right.right.right.right.right.right.right.right.right.right.left,
    have h₃ : ¬ x44, from path.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
    and.intro (or.inr h₁) (and.intro (or.inr h₂) (and.intro (or.inr h₃)
    (and.intro (or.inr h₂) (and.intro (or.inr h₃) (or.inr h₃)))))

-- Every position must be occupied:

theorem position_1_occupied (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) : x11 ∨ x12 ∨ x13 ∨ x14 :=
    or.inr (or.inr (or.inr path.right.right.right.left))

theorem position_2_occupied (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) : x21 ∨ x22 ∨ x23 ∨ x24 :=
    or.inl path.right.right.right.right.left

theorem position_3_occupied (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) : x31 ∨ x32 ∨ x33 ∨ x34 :=
    or.inr (or.inl path.right.right.right.right.right.right.right.right.right.left)

theorem position_4_occupied (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) : x41 ∨ x42 ∨ x43 ∨ x44 :=
    or.inr (or.inr (or.inl path.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left))

-- No two nodes can occupy the same position

theorem position_1_not_twice (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) :
(¬ x11 ∨ ¬ x12) ∧ (¬ x11 ∨ ¬ x13) ∧ (¬ x11 ∨ ¬ x14) ∧
(¬ x12 ∨ ¬ x13) ∧ (¬ x12 ∨ ¬ x14) ∧ (¬ x13 ∨ ¬ x14) :=
    have h₁ : ¬ x11, from path.left,
    have h₂ : ¬ x12, from path.right.left,
    have h₃ : ¬ x13, from path.right.right.left,
    and.intro (or.inr h₂) (and.intro (or.inr h₃) (and.intro (or.inl h₁)
    (and.intro (or.inr h₃) (and.intro (or.inl h₂) (or.inl h₃)))))

theorem position_2_not_twice (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) :
(¬ x21 ∨ ¬ x22) ∧ (¬ x21 ∨ ¬ x23) ∧ (¬ x21 ∨ ¬ x24) ∧
(¬ x22 ∨ ¬ x23) ∧ (¬ x22 ∨ ¬ x24) ∧ (¬ x23 ∨ ¬ x24) :=
    have h₁ : ¬ x22, from path.right.right.right.right.right.left,
    have h₂ : ¬ x23, from path.right.right.right.right.right.right.left,
    have h₃ : ¬ x24, from path.right.right.right.right.right.right.right.left,
    and.intro (or.inr h₁) (and.intro (or.inr h₂) (and.intro (or.inr h₃)
    (and.intro (or.inr h₂) (and.intro (or.inr h₃) (or.inr h₃)))))

theorem position_3_not_twice (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) :
(¬ x31 ∨ ¬ x32) ∧ (¬ x31 ∨ ¬ x33) ∧ (¬ x31 ∨ ¬ x34) ∧
(¬ x32 ∨ ¬ x33) ∧ (¬ x32 ∨ ¬ x34) ∧ (¬ x33 ∨ ¬ x34) :=
    have h₁ : ¬ x31, from path.right.right.right.right.right.right.right.right.left,
    have h₂ : ¬ x33, from path.right.right.right.right.right.right.right.right.right.right.left,
    have h₃ : ¬ x34, from path.right.right.right.right.right.right.right.right.right.right.right.left,
    and.intro (or.inl h₁) (and.intro (or.inr h₂) (and.intro (or.inr h₃)
    (and.intro (or.inr h₂) (and.intro (or.inr h₃) (or.inr h₃)))))

theorem position_4_not_twice (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) :
(¬ x41 ∨ ¬ x42) ∧ (¬ x41 ∨ ¬ x43) ∧ (¬ x41 ∨ ¬ x44) ∧
(¬ x42 ∨ ¬ x43) ∧ (¬ x42 ∨ ¬ x44) ∧ (¬ x43 ∨ ¬ x44) :=
    have h₁ : ¬ x41, from path.right.right.right.right.right.right.right.right.right.right.right.right.left,
    have h₂ : ¬ x42, from path.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
    have h₃ : ¬ x44, from path.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
    and.intro (or.inr h₂) (and.intro (or.inl h₁) (and.intro (or.inr h₃)
    (and.intro (or.inl h₂) (and.intro (or.inr h₃) (or.inr h₃)))))

-- Non adjacent nodes cannot be adjacent in the path.
-- My graph is G = {(1, 2), (1, 3), (1, 4), (2, 3)}, so (2, 4) and (3, 4) don't belong to G.

-- If (2, 4) doesn't belong to G, nodes 2 and 4 aren't adjacent, so they can't be adjacent in the path:

theorem first_non_adjacent (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) :
(¬ x12 ∨ ¬ x24) ∧ (¬ x22 ∨ ¬ x34) ∧ (¬ x32 ∨ ¬ x44) :=
    have h₁ : ¬ x12, from path.right.left,
    have h₂ : ¬ x22, from path.right.right.right.right.right.left,
    have h₃ : ¬ x44, from path.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
    and.intro (or.inl h₁) (and.intro (or.inl h₂) (or.inr h₃))

-- The same for (3, 4):

theorem second_non_adjacent (path : ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ x14 ∧ x21 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧
¬ x31 ∧ x32 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ x43 ∧ ¬ x44) :
(¬ x13 ∨ ¬ x24) ∧ (¬ x23 ∨ ¬ x34) ∧ (¬ x33 ∨ ¬ x44) :=
    have h₁ : ¬ x13, from path.right.right.left,
    have h₂ : ¬ x23, from path.right.right.right.right.right.right.left,
    have h₃ : ¬ x44, from path.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
    and.intro (or.inl h₁) (and.intro (or.inl h₂) (or.inr h₃))

-- We can conclude that my path for graph G is Hamiltonian.
