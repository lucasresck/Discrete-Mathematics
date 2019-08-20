/-
Problema dos Vestidos
 
Três irmãs - Ana, Maria e Cláudia - foram a uma festa com vestidos de
cores diferentes. Uma vestia azul, a outra branco e a Terceira
preto. Chegando à festa, o anfitrião perguntou quem era cada uma
delas. As respostas foram:
- A de azul respondeu: “Ana é a que está de branco”
- A de branco falou: “Eu sou Maria”
- A de preto disse:  “Cláudia é quem está de branco”
O anfitrião foi capaz de identificar corretamente quem era cada pessoa
considerando que:
- Ana sempre diz a verdade
- Maria às vezes diz a verdade
- Cláudia nunca diz a verdade
Pensando um pouco sobre o problema, pode-se concluir que a Ana estava
com o vestido preto, a Cláudia com o branco e a Maria com o
azul.  
Formalizar o problema e usar algum método dedutivo para construir um
argumento formal a favor da conclusão. 
Dica: A tabela verdade teria 512 linhas! Existem várias possiveis
formalizações, na que estamos interesados, todos os simbolos
proposicionais necessários estão declarados abaixo. 
Vc deve interpretar as respostas e conclusões do anfitrião
considerando as possibilidades de quem poderia ter falado o que.
-/

variables AA AB AP MA MB MP CA CB CP : Prop

open classical

/- Vamos trabalhar as possibilidades de quem disse cada resposta para
concluirmos algumas hipóteses.
Se supormos que Ana estava de azul, encontramos que Ana estava de
branco, pois ela não mente. -/
variable h1 : AA → AB
/-Se supormos que Maria estava de branco, não concluimos nada. Na
verdade, não concluimos nada supondo que Maria estava usando alguma
cor, pois não temos certeza se ela mente ou fala a verdade.
Se supormos que Cláudia está vestindo azul, temos, pela sua resposta,
que Ana não está usando branco! -/
variable h2 : CA → ¬ AB
/- Suponhamos que Ana esteja de branco: então quem está de branco fala
sempre a verdade, de modo que Maria está de branco.-/
variable h3 : AB → MB
/- Se Cládia estava de branco, então a pessoa que estava de branco não
é a Maria, pois sempre mente. Porém, isso não significa que Maria não
estava de branco.
Suponhamos que Ana esteja de preto: então Cláudia está de branco:-/
variable h4 : AP → CB
/- Suponhamos que Cláudia esteja vestindo preto: a pessoa que está
vestindo preto está mentindo, logo Cláudia não está de branco:-/
variable h48 : CP -> ¬ CB
--Além disso, temos que: Ana está vestindo azul, branco ou preto:
variable h5 : AA ∨ AB ∨ AP
variable h6 : MA ∨ MB ∨ MP
variable h7 : CA ∨ CB ∨ CP
-- Ainda mais: cada vestido é realmente vestido por alguém:
variable h8 : AA ∨ MA ∨ CA
variable h9 : AB ∨ MB ∨ CB
variable h10 : AP ∨ MP ∨ CP
/- Sabemos também que uma pessoa vestir uma cor a impede de vestir
outras cores:-/
variable h20 : AA → (¬ AB ∧ ¬ AP)
variable h21 : AB → (¬ AA ∧ ¬ AP)
variable h22 : AP → (¬ AA ∧ ¬ AB)
variable h23 : MA → (¬ MB ∧ ¬ MP)
variable h24 : MB → (¬ MA ∧ ¬ MP)
variable h25 : MP → (¬ MA ∧ ¬ MB)
variable h26 : CA → (¬ CB ∧ ¬ CP)
variable h27 : CB → (¬ CA ∧ ¬ CP)
variable h28 : CP → (¬ CA ∧ ¬ CB)
/- Também é razoável assumir que apenas uma pessoa pode vestir uma
cor de vestido:-/
variable h38 : AA → (¬ MA ∧ ¬ CA)
variable h39 : AB → (¬ MB ∧ ¬ CB)
variable h40 : AP → (¬ MP ∧ ¬ CP)
variable h41 : MA → (¬ AA ∧ ¬ CA)
variable h42 : MB → (¬ AB ∧ ¬ CB)
variable h43 : MP → (¬ AP ∧ ¬ CP)
variable h44 : CA → (¬ AA ∧ ¬ MA)
variable h45 : CB → (¬ AB ∧ ¬ MB)
variable h46 : CP → (¬ AP ∧ ¬ MP)

example : AP ∧ MA ∧ CB :=
  have h11 : AP, from
    by_contradiction
    (assume h13 : ¬ AP,
    show false, from
      or.elim h5
        (assume h14 : AA,
        have h36 : AA → false, from
          (assume h37 : AA,
          show false, from 
            (show ¬ AB, from and.left (h20 h37)) 
            (show AB, from h1 h37)),
        show false, from h36 h14)
        (assume h15 : AB ∨ AP,
        show false, from
          or.elim h15
            (assume h16 : AB,
            have h37 : AB → false, from 
              (assume h47 : AB,
                (show ¬ MB, from and.left (h39 h47))
                (show MB, from h3 h47)),
            show false, from h37 h16)
            (assume h17 : AP,
            show false, from h13 h17))),
  have h19 : CB, from h4 h11,
  have h18 : MA, from
    by_contradiction
    (assume h29: ¬ MA,
    have h30 : ¬ AA, from and.left (h22 h11),
    have h31 : ¬ CA, from and.left (h27 h19),
    show false, from
    or.elim h8
      (assume h32 : AA, h30 h32)
      (assume h33 : MA ∨ CA,
      show false, from
        or.elim h33
          (assume h34 : MA, h29 h34)
          (assume h35 : CA, h31 h35))),
  have h12 : MA ∧ CB, from and.intro h18 h19,
  and.intro h11 h12
