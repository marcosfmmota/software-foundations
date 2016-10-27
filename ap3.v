(* -----------------------------------------------------------
   UNIVERSIDADE FEDERAL DO CEARÁ - DEPARTAMENTO DE COMPUTAÇÃO
   
   AVALIAÇÃO PARCIAL 3, NO SEMESTRE LETIVO 2016.2, DAS TURMAS:
   
     - CK0230 - PROVA ASSISTIDA POR COMPUTADOR - T01
     - CK0130 - TEORIA DA PROVA                - T01 .
   
   PROFESSOR: PABLO MAYCKON SILVA FARIAS.
   ----------------------------------------------------------- *)

(*
   DADOS DO ALUNO: MATRÍCULA: 354080
                   NOME     : Marcos Felipe de Menezes Mota
*)

(*
   INTRODUÇÃO: Caro aluno, esta prova possui uma questão de 5 pontos.

   Você deve escrever neste arquivo as respostas dessas questões, e
   então enviá-lo de volta para mim por e-mail, dentro do tempo de
   realização da prova.

   Por favor, coopere com o processo de ensino e aprendizagem desta
   disciplina e não compartilhe este arquivo com outras pessoas, nem
   durante nem depois da realização da prova. Obrigado!

   ATENÇÃO: AS ÚNICAS FONTES PERMITIDAS PARA CONSULTA são os
            capítulos que estudamos do livro da disciplina, além do
   manual do coq, para esclarecimentos sobre os recursos que foram
   estudados.

   IMPORTANTE: Ao responder às questões, você pode e deve usar
               definições e teoremas dos capítulos já estudados:
   a função do comando a seguir é justamente importar esses recursos.
*)

Require Export Rel.

(* ============================= QUESTÃO  ÚNICA ============================= *)

Module Q1. (* 5 PONTOS *)

(*
   RESUMO: nesta questão você deve:

     A) Definir uma predicado indutivo "pal" ("é palíndromo").
     B) Provar um teorema sobre palíndromos, tanto informalmente
        quanto formalmente.

   Mais informações seguem abaixo.
*)

(* PARTE 1: Defina um predicado indutivo e polimórfico "pal",
            de forma que "pal l" seja a afirmação de que a lista "l"
   (cujos elementos podem ser de um tipo T qualquer) é um palíndromo.

   Exemplos de palíndromos:

     - []
     - [3]
     - [b b]
     - [ a t a ]
     - [ a r a r a ]

   ATENÇÃO: em prova anterior, nós definimos um TIPO que representava
            palíndromos. Desta vez, porém, nós trabalharemos
   diretamente com o tipo "list", e definiremos um PREDICADO, que se
   aplica a algumas listas (gerando um Prop) e não a outras.
*)

Inductive pal {X:Type} : list X -> Prop :=
  | pal_nil : pal nil
  | pal_one : forall (n : X), pal (cons n nil )
  | pal_comp : forall (n : X) (l : list X), pal l -> pal (n :: (rev l) ++ [n]).    


(* PARTE 2: Escreva uma demonstração INFORMAL (em "matematiquês", não
            em "Coq'ês") de que o seguinte enunciado é VERDADEIRO ou
   de que ele é FALSO:

     Todo palíndromo "p" tem uma das seguintes formas:

       - p = l ++ (rev l)
       - p = l ++ ( m::(rev l) ) .
*)

Check pal_ind.
(*Prova informal:
  Nesse teorema podemos usar a definição de pal para mostrar que se p é uma lista palíndroma então existe
  uma lista l tao que p é igual a l concatenado com seu reverso ou p é l concatenado
  com seu reverso e com um elemento qualquer no meio.
  Usando o princípio de indução para o tipo pal, sabemos que precisamos mostrar a válidade do teorema
  para os seguintes casos:
  Caso de p ser nil para esse caso dizemos que existe l vazio sendo assim podemos dizer que ele foi
  formado por nil ++ rev nil.
  Depois temos o caso de p ser uma lista de apenas um elemento. Novamente podemos dizer que l é nil mas
  que p foi formado usando l ++ (m::(rev l))
  Por último temos que p é da forma n :: rev l ++ [n], ou seja, dois elementos iguais com uma lista palíndroma
  no meio. Nesse caso temos na hipótese de indução que l é palíndroma e que o teorema é verdadeiro 
  para l. Assim temos que mostrar que existe l0 tal que:
  n::rev l ++[n] = l0 ++ rev l0 ou n::rev l ++[n] = l0 ++(m: rev l0)
  Usando que l0 é uma lista com cabeça e cauda podemos fazer uma analíse de casos para como uma lista
  pode formar p = n::rev l + [n]. Temos que:
  Se l0 = nil então p = nil ou p = m o que é um absurdo porque esses casos já foram analisados, então
  l0 = h :: t. No caso l0 = h :: t, temos:
  p = h :: t ++ rev t ++ [h] ou p = h :: t ++ (m:: rev t) ++ [h]. Aplicando pal_comp temos:
  rev l = t ++ rev t ou rev l = t ++ (m:: rev t). Com o lema adicional que o reverso de uma palíndrome é
  igual a si mesmo temos que l = t ++ rev t ou l = t ++ (m:: rev t) o que é a hipotése de indução.     
     
*)

(* PARTE 3: Formalize aqui no Coq o enunciado e a prova da parte 2. *)

(*Theorem middle_nil_or_m : forall (X: Type) (l:list X) (p:list X) (m:X),
  p = l ++ (rev l) \/ p = l ++ (m::(rev l)) -> pal p.
Proof.
  intros. induction l.
  - simpl in H. destruct H.
    + rewrite H. apply pal_nil.
    + rewrite H. apply pal_one.
  - destruct H.
    + simpl H. 
Qed.*)

Lemma rev_aux : forall (X : Type) (n :X) (l : list X), rev (l ++ [n]) = n :: l.
Proof.
  induction l.
  - reflexivity.
  - admit.
Qed.

Lemma rev_pal_pal : forall (X : Type) (p : list X), pal p -> rev p = p.
Proof.
  intros. induction H.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHpal. rewrite rev_aux. reflexivity.
Qed. 

Theorem middle_nil_or_m :forall (X: Type) (p: list X) (m:X), pal p -> 
         exists (l: list X), p = l ++ (rev l) \/ p = l ++ (m::(rev l)).
Proof.
  intros. induction H.
  - exists nil. simpl. left. reflexivity.
  - exists nil. simpl. right. admit.
  - destruct IHpal. destruct H0.
    * exists x. left. admit.
    * exists x. right. admit.   
Qed.
End Q1.

(* ================================== FIM  ================================== *)
