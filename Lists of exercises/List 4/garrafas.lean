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

/- Como representar algo que varia no tempo? Se a garrafa maior tem 6
litros agora, é porque ela tinha 1 litro antes. Podemos representar o
tempo no domínio! -/

constant T : Type

/- Vamos criar as garrafas grande (big bottle, BB) e pequena (LB), que
são predicados que associam a um número natural (volume, em litros) se
essa garrafa está preenchida com esse volume. As duas garrafas iniciam
vazias, ou seja, existe um instante de tempo em que elas estão vazias
nesse instante de tempo:-/

constants BB LB : ℕ → T → Prop
constants beginBB : ∃ t : T, BB 0 t
constants beginLB : ∃ t : T, LB 0 t

/- Podemos encher essas garrafas. Ou seja, pra todo volume que a garrafa,
digamos, grande tem em algum momento, existe algum momento após em que
ela pode ser cheia: -/

constant after : T → T → Prop

variable fillBB : ∀ l : ℕ, ∀ t0 : T, ∃ t : T, (after t t0) ∧ (BB l t0) → BB 7 t
variable fillLB : ∀ l : ℕ, ∀ t0 : T, ∃ t : T, (after t t0) ∧ (LB l t0) → LB 5 t

-- Da mesma maneira, podemos esvaziar as garrafas:

variable emptyBB : ∀ l : ℕ, ∀ t0 : T, ∃ t : T, (after t t0) ∧ (BB l t0) → BB 0 t
variable emptyLB : ∀ l : ℕ, ∀ t0 : T, ∃ t : T, (after t t0) ∧ (LB l t0) → LB 0 t

/- E, claro, podemos transferir os volumes entre as garrafas. Ou seja,
para todos os volumes que as garrafas tem em algum momento, existe algum
momento após em que ocorre a transferência e: uma delas fica vazia ou a
outra fica cheia. Assim: -/

variable BBtoLB : ∀ lBB, ∀ lLB, ∀ t0, ∃ t,
(after t t0) ∧ (BB lBB t0) ∧ (LB lLB t0) → ((BB (lBB - (5 - lLB)) t) ∧ (LB 5 t))
                                         ∨ ((BB 0 t) ∧ (LB (lLB + lBB) t))

variable LBtoBB : ∀ lBB, ∀ lLB, ∀ t0, ∃ t,
(after t t0) ∧ (BB lBB t0) ∧ (LB lLB t0) → ((BB 7 t) ∧ (LB (lLB - (7 - lBB)) t))
                                         ∨ ((BB (lBB + lLB) t) ∧ (LB 0 t))
