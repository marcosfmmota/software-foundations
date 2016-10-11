(* -----------------------------------------------------------
   UNIVERSIDADE FEDERAL DO CEARÁ - DEPARTAMENTO DE COMPUTAÇÃO
   
   AVALIAÇÃO PARCIAL 2, NO SEMESTRE LETIVO 2016.2, DAS TURMAS:
   
     - CK0230 - PROVA ASSISTIDA POR COMPUTADOR - T01
     - CK0130 - TEORIA DA PROVA                - T01 .
   
   PROFESSOR: PABLO MAYCKON SILVA FARIAS.
   ----------------------------------------------------------- *)

(*
   DADOS DO ALUNO: MATRÍCULA: Marcos Felipe de Menezes Mota
                   NOME     : 354080
*)

(*
   INTRODUÇÃO: Caro aluno, esta prova possui 2 questões:

      - Q1: 4 pontos.
      - Q2: 1 ponto.

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

Require Export Logic.

(* =============================== QUESTÃO  1 =============================== *)

Module Q1. (* 4 PONTOS *)

(*
   RESUMO: nesta questão você deve:

     A) Definir um tipo "Deque".
     B) Escrever funções para remover do início e do fim de Deques,
        assim como para calcular o tamanho de uma Deque.
     C) Provar um teorema sobre tamanhos de Deques após remoções.

   Mais informações seguem abaixo.
*)

(* PARTE 1: Defina um tipo Deque, que armazene números naturais e
            permita inserções e remoções no início e no fim da
   estrutura -- mas não escreva nenhuma função ainda!
   
   ATENÇÃO: Você poderia fornecer uma definição indutiva para esse
   tipo, mas é mais rápido defini-lo em termos do tipo "list", para o
   qual já temos vários recursos à disposição!

   Não é necessário definir notações para esse tipo e nem para as
   funções abaixo.
*)

Definition Deque := list nat.


(* PARTE 2: Defina 3 funções: a primeira para remover do início e a
            segunda para remover do fim da Deque recebida como
   argumento. Essas duas primeiras funções devem retornar UM PAR
   ORDENADO, contendo:

     - Um "option nat", contendo o elemento removido (ou nada, caso a
       deque esteja vazia).

     - A deque resultante da remoção (que será a mesma dada como
       entrada quando esta estiver vazia).

   A terceira função deve retornar o número de elementos da Deque.
*)

SearchAbout list.

Definition remove_head (d : Deque) : option nat * Deque :=
  match d with
  | [] => (None, d)
  | h :: t => (Some h, t)
  end.

Fixpoint remove_tail (d : Deque) : option nat * Deque :=
  match d with
  | nil => (None, d)
  | h :: t => match t with
              | nil => (Some h, t)
              | h1 :: t1 => (fst(remove_tail t), h :: snd (remove_tail t))
              end
  end.

Compute(remove_tail [2;3;4;5]).

(* PARTE 3: Prove que, para toda deque "d", se de "d" é removido o
            elemento do início, em seguida é removido o elemento do
   final, e se esta segunda remoção de fato retorna um número, então
   o tamanho de "d" é 2 unidades a mais que o tamanho da deque após a
   segunda remoção.

   DICA: escreva um lema relacionando a forma de uma deque antes e
         depois de uma remoção do final da estrutura.
*)

Lemma length_remove_tail: forall (d : Deque), length(snd(remove_tail d)) + 1 = length d.
Proof.
  induction d.
  - simpl. symmetry. admit.
  - admit.
Qed.

Lemma plus_Sn_1: forall n: nat, S n = n+1.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem part3 : forall (d : Deque) (n:nat), 
        length(snd(remove_tail(snd(remove_head d)))) + 2 = (length d) -> 
        fst (remove_tail(snd(remove_head d))) = Some n.
Proof.
  intros. induction d as [|h t IHd].
  - simpl. simpl in H. inversion H.
  - simpl. simpl in H.  
    admit.
Qed. 

End Q1.

(* =============================== QUESTÃO  2 =============================== *)

Module Q2. (* 1 PONTO *)

(* PROVE ESTE TEOREMA: *)


Theorem em_demorgan: excluded_middle -> de_morgan_not_and_not.
  unfold de_morgan_not_and_not. unfold excluded_middle.
  unfold not. intros. destruct H0. split.
  - intros. apply double_neg in H0. 


End Q2.

(* ================================== FIM  ================================== *)
