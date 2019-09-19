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

/- How to represent something that varies in time? If the big bottle
now has 6L, it's because it had 1L in the past (the little bottle filled
it with 5L). But we can represent the time in the domain! -/

constant T : Type

/- Let's create the Big and the Little Bottles, that are predicates that
associates a natural number (volume, in liters) to a proposition, with
the meaning of the bottle is filled with this exactly number of liters.
-/

constants BB LB : ℕ → T → Prop

/- Both bottles start empty, that is, there's a instant of time when
they are empty: -/

constants beginBB : ∃ t : T, BB 0 t
constants beginLB : ∃ t : T, LB 0 t

/- We can fill up the bottles. For all volume that a bottle has in a
certain time, there's a time after it when the bottle can be filled
up. -/

constant after : T → T → Prop

variable fillBB : ∀ l : ℕ, ∀ t0 : T, ∃ t : T,
                    (after t t0) ∧ (BB l t0) → BB 7 t

variable fillLB : ∀ l : ℕ, ∀ t0 : T, ∃ t : T,
                    (after t t0) ∧ (LB l t0) → LB 5 t

-- In the same way, we can empty the bottles:

variable emptyBB : ∀ l : ℕ, ∀ t0 : T, ∃ t : T, (after t t0) ∧ (BB l t0) → BB 0 t
variable emptyLB : ∀ l : ℕ, ∀ t0 : T, ∃ t : T, (after t t0) ∧ (LB l t0) → LB 0 t

/- We can also transfer the water between the bottles. That is, for all
volumes that a bottle can have, for all instants of time, if the bottle
has this volume in this instant of time, there will be a time after it
when the water will be transfered: one of the bottles will become empty
or the other will be filled up. -/

variable BBtoLB : ∀ lBB, ∀ lLB, ∀ t0, ∃ t,
(after t t0) ∧ (BB lBB t0) ∧ (LB lLB t0) → ((BB (lBB - (5 - lLB)) t) ∧ (LB 5 t))
                                         ∨ ((BB 0 t) ∧ (LB (lLB + lBB) t))

variable LBtoBB : ∀ lBB, ∀ lLB, ∀ t0, ∃ t,
(after t t0) ∧ (BB lBB t0) ∧ (LB lLB t0) → ((BB 7 t) ∧ (LB (lLB - (7 - lBB)) t))
                                         ∨ ((BB (lBB + lLB) t) ∧ (LB 0 t))

/- Is it possible to store 6L in a bottle? That is, there will be a time
when the big bottle will have 6L? -/

theorem sixliters : ∃ t : T, BB 6 t := sorry
