/-

Alunos:
 - Lucas Emanuel Resck Domingues
 - Lucas Machado Moschen

Considere uma fonte de água inesgotável e duas garrafas, uma de 5 e
outra de 7 litros, as quais não possuem quaisquer marcações que
possibilitem medidas de volumes intermediários às suas respectivas
capacidades. O formato das mesmas também impede o uso de aparelhos de
medição indireta, assim como não há uma balança disponível. 

Considerando essas condições, pergunta-se se é possível armazenar o
volume exato de 6 litros de água.

É possível que você já conheça a solução deste problema ou mesmo saiba
que, no caso geral de duas garrafas com capacidade que representem
números primos entre si, pode-se medir qualquer volume inteiro até a
capacidade da maior garrafa. De qq forma, pretende-se construir
primeiro um conjunto de sentenças que representem o problema e somente
depois, via o uso do conceito de consequência lógica, verificar se é
possível medir 6 litros nas condições estipuladas. Neste exercício,
pede-se apenas a formalização em FOL.

-/

/- How to represent something that changes in time? Now the bottles
are filled up, byt later they can be empty. We can represent time in
the domain, through states, that change in time. Let's represent first
state as z ("zero") in the domain. Each element of the domain will
have a "sucessor". This is analogous to the Piano axioms.-/

constant T : Type
constant z : T
constant s : T → T

/- Let's use G predicate to infer: G(t, x, y) means that exists a
possibility that, in state t, the big bottle (the one with 7L) will
have x liters and the little bottle (5L) will have y liters. That is,
there is a sequence of steps where we can reach x and y liters at step
t. For example (and for formalization), at step 0, we can state that
both bottles are empty: -/

constant G : T → ℕ → ℕ → Prop
constant start : G z 0 0

/- Given a step, which bottle can be filled up in next step,
independently of how many liters it has and which step it is. -/

constant fill1 : ∀ t : T, ∀ x : ℕ, ∀ y : ℕ, (G t x y) → (G (s t) 7 y)
constant fill2 : ∀ t : T, ∀ x : ℕ, ∀ y : ℕ, (G t x y) → (G (s t) x 5)

-- In the same way, they can be empty:

constant empty1 : ∀ t : T, ∀ x : ℕ, ∀ y : ℕ, (G t x y) → (G (s t) 0 y)
constant empty2 : ∀ t : T, ∀ x : ℕ, ∀ y : ℕ, (G t x y) → (G (s t) x 0)

/- But how to tranfer water between these bottles? We have to
condition in the volume of the bottles at step t, because one may be
filled up or the other may become empty: -/

constant transfer1 : ∀ t : T, ∀ x : ℕ, ∀ y : ℕ, (G t x y) ∧ (y ≥ 7 - x) → (G (s t) 7 (y - (7 - x)))
constant transfer2 : ∀ t : T, ∀ x : ℕ, ∀ y : ℕ, (G t x y) ∧ (y < 7 - x) → (G (s t) (x + y) 0)

constant transfer3 : ∀ t : T, ∀ x : ℕ, ∀ y : ℕ, (G t x y) ∧ (x ≥ 5 - y) → (G (s t) (x - (5 - y)) 5)
constant transfer4x : ∀ t : T, ∀ x : ℕ, ∀ y : ℕ, (G t x y) ∧ (x < 5 - y) → (G (s t) 0 (x + y))

/- What was asked to prove is if it's possible to reach 6L with this
process. -/

theorem sixLiters : ∃ t : T, (G t 6 0) := sorry
