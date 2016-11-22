Require Export ProofObjects.


(* ================================================================ *)

(** * O operador "fix" *)

(**
O operador [fix] está para [Fixpoint] assim como [fun] está para
[Definition], ou seja, [fix] serve para definir e usar localmente uma
função recursiva, sem registrar no contexto um nome para ela.

A notação é

  fix nome_local_da_função (argumentos...) : tipo_de_retorno := corpo

como ilustrado abaixo:
*)

Compute
  (
  fix last (l : list nat) : option nat
    :=
    match l with
    | [] => None
    | h1::t1 => match t1 with
                | [] => Some h1
                | h2::t2 => last t1
                end
    end
  )
  [1; 2; 3; 4; 5].

Fail Check last. (** Observe: [last] não está "registrada". *)


(* ================================================================ *)

(** * Provando Teoremas via [fix] *)

(**
Recapitule primeiramente que

  "Coq treats as "the same" any two terms that are _convertible_
   according to a simple set of computation rules. These rules, which
   are similar to those used by [Compute], include evaluation of
   function application, inlining of definitions, and simplification
   of [match]es."

Por exemplo:
*)


(**
Agora, recapitule o argumento deste teorema:  [forall n, n + 0 = n].

  ... (Explicado em sala)

Isso pode ser formalizado diretamente por uma função recursiva:
*)

Check f_equal.

Definition plus_0_r_po: forall n, n + 0 = n
  :=
  fix f (n : nat) : n + 0 = n
    :=
    match n with
    | O => @eq_refl nat 0 : 0 = 0
           (* Ou simplesmente:  @eq_refl nat 0 *)
           (* Ou simplesmente:  eq_refl *)
    | S n' => f_equal nat nat S (n' + 0) n' (f n')
              (* Ou simplesmente:  f_equal _ _ _ _ _ (f n') *)
    end.


(** EXERCÍCIO: prove por meio de uma função recursiva: *)

Definition plus_assoc_po: forall m n o, m + (n+o) = (m+n) + o :=
  fix f m n o : m + (n + o) = (m + n) + o :=
    match m with
    | O => eq_refl
    | S m' => f_equal _ _ S (m' + (n + o)) (m' + n + o) (f m' n o)
    end.


(* ================================================================ *)

(** * Provando Princípios de Indução de Conjuntos via [fix] *)

(**
O mesmo tipo de raciocínio permite provarmos _princípios de indução_
por meio de funções recursivas.

No caso de [nat], por exemplo, temos:
 *)

(* Inductive nat : Type :=
   | O : nat
   | S : nat -> nat *)

Definition nat_ind_po :
  forall P : nat -> Prop,
  P O ->
  ( forall x, P x -> P (S x) ) ->
  forall n : nat, P n
    :=
    fun P p0 ps  (* Essa função adicional recebe os argumentos
                    que não mudam durante as chamadas recursivas *)
      =>
      fix f n : P n
        :=
        match n with
        | O => p0
        | S n' => ( ps n' (f n') ) : P (S n')
                  (* Ou simplesmente:  ( ps n' (f n') ) *)
        end.


(** EXERCÍCIO: defina um tipo [listbool] e enuncie e prove um
    princípio de indução para ele: *)

Inductive listbool : Type :=
  | bnil : listbool
  | bcons : bool -> listbool -> listbool.

Check listbool_ind.

Definition listbool_ind_po :
  forall P : listbool -> Prop,
       P bnil ->
       (forall (b : bool) (l : listbool), P l -> P (bcons b l)) ->
       forall l : listbool, P l :=
  fun P pn pc =>
    fix f l : P l :=
    match l with
    | bnil => pn
    | bcons b l' => pc b l' (f l')
    end.  

(** EXERCÍCIO: Enuncie e prove o princípio de indução para [list].
               (Observe que, ao fazê-lo, você estará provando um
    princípio de indução para um tipo polimórfico, mas a ideia não
    muda.) *)


Definition list_ind_po : forall (X : Type) (P : list X -> Prop),
       P [] ->
       (forall (x : X) (l : list X), P l -> P (x :: l)) ->
       forall l : list X, P l :=
  fun X P pn pc =>
    fix f l : P l :=
    match l with
    | nil => pn
    | cons x l' => pc _ _ (f l')
    end.  

Print list.
(** EXERCÍCIO: Defina um tipo polimórfico para árvores binárias, e
    prove o princípio de indução correspondente. *)

Inductive btree (X : Type) : Type :=
  | bempty : btree X
  | bleaf : X -> btree X
  | nbranch : X -> btree X -> btree X -> btree X.


Definition btree_ind_po : forall (X : Type) (P : btree X -> Prop),
  P (bempty X) -> (forall (x : X) , P (bleaf X x)) ->
  (forall (x : X) (l : btree X) (r : btree X), P l -> P r -> P (nbranch X x l r)) ->
  forall b : btree X, P b 
  :=
  fun X P pe pl pb =>
    fix f bt : P bt :=
    match bt with
    | bempty => pe
    | bleaf x => pl x
    | nbranch x l' r' => pb x l' r' (f l') (f r') 
    end.

(** EXERCÍCIO: Escreva um princípio de indução para [nat] cujo passo
    "vá de 2 em 2", ou seja, de P(n) provamos P(S(S n)).

    Dica: Como fica a base?

    Observação: Numa prova com táticas, e supondo que nat_ind2 é o
    objeto de prova que você escreveu acima, você pode usá-lo assim:

      induction n using nat_ind2. *)


(* ================================================================ *)

(** * Provando Princípios de Indução de IndProp's via [fix] *)

(** EXEMPLO: essencialmente a mesma técnica ilustrada acima nos
             permite provar princípios de indução para proposições
    indutivamente definidas.

    Em geral, porém, nós precisamos de um recurso técnico novo: o
    "casamento de padrão dependente" ("dependent pattern matching"),
    que ainda não foi explicado.

    Para ilustrar, segue abaixo o princípio indutivo para [ev] (o
    recurso técnico novo está no "match ... in ... return ... with",
    mas ele serve apenas para convencer o Coq de que os termos
    retornados têm os tipos corretos, e pode ser ignorado por ora): *)

(* Inductive ev : nat -> Prop :=
   | ev_0 : ev 0
   | ev_SS : forall x : nat, ev x -> ev (S (S x)) . *)

Definition ev_ind_po:
  forall P : nat -> Prop,
  P 0 ->
  (forall n, ev n -> P n -> P (S (S n)) ) ->
  forall n, ev n -> P n
    :=
    fun P p0 ps
      =>
      fix f n pevn : P n
        :=
        match pevn in ev a return P a with
        | ev_0 => p0
        | ev_SS n' evn' (* n = S (S n') *) =>
            ps n' evn' (f n' evn')
        end.


(** Os exercícios abaixo são recomendados, e podem ser feitos usando
    apenas o tipo simples e já conhecido de casamento de padrão. *)


(** EXERCÍCIO: Enuncie e prove o princípio de indução para [and]. *)

(* Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B . *)
Check and_ind.

Definition and_ind_po: forall A B P : Prop, (A -> B -> P) -> A /\ B -> P :=
  fun A B P  (HABP : A -> B -> P) (H : A /\ B)
  => match H with
     | conj HA HB =>  HABP HA HB
     end.  

(** EXERCÍCIO: Enuncie e prove o princípio de indução para [False]. *)

(*  Inductive False : Prop := .  *)

Definition False_ind_po : forall P : Prop, False -> P :=
  fun P f => match f with
             end.

(** EXERCÍCIO: Enuncie e prove o princípio de indução para [True]. *)

(*  Inductive True : Prop :=  I : True .  *)

Definition True_ind_po : forall P : Prop, P -> True -> P :=
  fun P (HP : P) (HT : True) => HP.

(* ================================================================ *)