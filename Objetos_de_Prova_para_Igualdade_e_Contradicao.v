Require Export IndPrinciples.

(* ================================================================ *)

(** * Casamento de Padrão Dependente *)

(** Nós estudaremos a partir de agora a versão estendida do casamento
    de padrão ("match"), que às vezes é necessário usar para que o Coq
    reconheça que certos termos estão bem-tipados.

    A compreensão desse recurso nos permite terminar de entender como
    a igualdade funciona no Coq, e com ela a tática [rewrite], etc. O
    mesmo se aplica às táticas de prova por absurdo no Coq. *)

(** Primeiramente, portanto, recapitule que, até agora, quando
    escrevíamos um "match", o tipo dele não dependia do termo
    específico que estivesse sendo analisado. No caso da função
    [evenb], por exemplo, o tipo do valor retornado é sempre [bool],
    independentemente do valor ao qual ela é aplicado: *)

Compute
  (
  fix evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end
  )
  8.


(** Considere agora o caso deste teorema:

      forall n : nat, n + 0 = n

    Nós sabemos que podemos prová-lo por meio de uma função
    recursiva: *)

Fixpoint plus_0_r_po (n : nat) : n + 0 = n
  :=
  match n with
  | O => @eq_refl nat 0
  | S n' => f_equal nat nat S (n' + 0) n' (plus_0_r_po n')
  end.

(** Qual é, porém, o tipo do termo "match ... end"?

    É "n + 0 = n", onde "n" é o próprio termo sendo analisado no
    [match]. *)


(** Como um segundo exemplo, considere a seguinte prova para o
    princípio de indução para [ev]: *)

Fixpoint ev_ind_po
  (P : nat -> Prop)
  (p0: P 0)
  (ps: forall n, ev n -> P n -> P (S (S n)) )
  (n : nat)
  (pevn : ev n)
  :
  P n
    :=
    match pevn with
    | ev_0 => p0
    | ev_SS n' evn' (* n = S (S n') /\ ev n' *) =>
        ps n' evn' (ev_ind_po P p0 ps n' evn')
    end.

(** Novamente: qual é o tipo do termo "match ... end"?

    É "P n", onde "n", no que diz respeito ao "match", é o número "x"
    tal que "pevn" tem tipo "ev x". Nesse caso, portanto, o tipo do
    "match" depende do _tipo_ do termo sendo analisado. *)


(** Para casos como esses 2 acima, em que o tipo do "match" depende do
    valor e/ou tipo do termo sendo analisado, o Coq possui o
    _casamento de padrão dependente_, cuja regra de funcionamento está
    muito bem explicada no livro "CPDT", capítulo "More Dependent
    Types" ( http://adam.chlipala.net/cpdt/html/Cpdt.MoreDep.html ):

----------------------------------------------------------------------
A dependent pattern match is a match expression where the type of the
overall match is a function of the value and/or the type of the
discriminee, the value being matched on. In other words, the match
type depends on the discriminee.

[...]

We come now to the one rule of dependent pattern matching in Coq. A
general dependent pattern match assumes this form (with unnecessary
parentheses included to make the syntax easier to parse):

  match E as y in (T x1 ... xn) return U with
    | C z1 ... zm => B
    | ...
  end

The discriminee is a term E, a value in some inductive type family T,
which takes n arguments. An as clause binds the name y to refer to the
discriminee E. An in clause binds an explicit name xi for the ith
argument passed to T in the type of E.

We bind these new variables y and xi so that they may be referred to
in U, a type given in the return clause. The overall type of the match
will be U, with E substituted for y, and with each xi substituted by
the actual argument appearing in that position within E's type.

[...]

The last piece of the typing rule tells how to type-check a match
case. A generic constructor application C z1 ... zm has some type T
x1' ... xn', an application of the type family used in E's type,
probably with occurrences of the zi variables. From here, a simple
recipe determines what type we will require for the case body B. The
type of B should be U with the following two substitutions applied: we
replace y (the as clause variable) with C z1 ... zm, and we replace
each xi (the in clause variables) with xi'. In other words, we
specialize the result type based on what we learn based on which
pattern has matched the discriminee.
----------------------------------------------------------------------

*)

(** Como exemplos concretos da explicação acima, aqui estão objetos de
    prova que usam casamento de padrão dependente para os 2 teoremas
    anteriores, mas ATENÇÃO:

      Não apenas olhe para o que está escrito! Calcule por conta
      própria, de acordo com a regra acima, o tipo esperado para o
      termo retornado por cada caso de cada "match", e verifique se
      o termo retornado realmente tem o tipo esperado. *)

Definition plus_0_r_dpm : forall n : nat, n + 0 = n
  :=
  fix f (n : nat) : n + 0 = n
    :=
    match n as v return v + 0 = v with
    | O => @eq_refl nat 0
    | S n' => f_equal nat nat S (n' + 0) n' (plus_0_r_po n')
    end.

(** Observação: em casos como o do termo acima, em que o objeto
    analisado pelo match consiste apenas numa variável, a cláusula
    "as" é pode ser omitida, e a variável em questão pode ser
    diretamente mencionada na cláusula "return". Assim, o termo acima
    poderia ter a seguinte linha, mais simples:

      match n return n + 0 = n with
*)

Definition ev_ind_dpm:
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


(** O trecho acima do CPDT tem a seguinte continuação, também
    importante:

----------------------------------------------------------------------
A few details have been omitted above. In Chapter 3, we learned that
inductive type families may have both _parameters_ and regular
arguments. Within an [in] clause, a parameter position must have the
wildcard [_] written, instead of a variable. (In general, Coq uses
wildcard [_]'s either to indicate pattern variables that will not be
mentioned again or to indicate positions where we would like type
inference to infer the appropriate terms.) Furthermore, recent Coq
versions are adding more and more heuristics to infer dependent
[match] annotations in certain conditions. The general annotation
inference problem is undecidable, so there will always be serious
limitations on how much work these heuristics can do. When in doubt
about why a particular dependent [match] is failing to type-check, add
an explicit [return] annotation! At that point, the mechanical rule
sketched in this section will provide a complete account of "what the
type checker is thinking." Be sure to avoid the common pitfall of
writing a [return] annotation that does not mention any variables
bound by [in] or [as]; such a [match] will never refine typing
requirements based on which pattern has matched. (One simple exception
to this rule is that, when the discriminee is a variable, that same
variable may be treated as if it were repeated as an [as] clause.)
----------------------------------------------------------------------

*)


(** EXERCÍCIO: enuncie e prove um princípio de indução para [le'],
               que é a relação <= como definida em IndProp: *)

Inductive le' : nat -> nat -> Prop :=
  | le'_n : forall n, le' n n
  | le'_S : forall n m, (le' n m) -> (le' n (S m)).

Definition le'_ind_po : forall P : nat -> nat -> Prop,
  (forall n : nat, P n n) -> 
  (forall n m : nat, le' n m -> P n m -> P n (S m)) ->
  forall n m : nat, le' n m -> P n m :=
  fun P pn ps =>
    fix f n m ple' : P n m :=
    match ple' in le' a b return P a b with
    | le'_n n' => pn n'
    | le'_S n' m' plenm => ps n' m' plenm (f n' m' plenm)
    end. 


(** EXERCÍCIO: enuncie e prove o princípio de indução para [le],
               cuja definição é:

      Inductive le (n : nat) : nat -> Prop :=
      | le_n : n <= n
      | le_S : forall m : nat, n <= m -> n <= S m
      end.
*)

Definition le_ind_po : forall (n : nat) (P : nat -> Prop),
  P n -> (forall m : nat, n <= m -> P m -> P (S m)) ->
  forall m : nat, n <= m -> P m 
  :=
  fun n P pn ps =>
    fix f m ple : P m :=
    match ple in le _ b return P b with
    | le_n => pn
    | le_S m' plenm => ps m' plenm (f m' plenm)
    end.
    
(* ================================================================ *)

(** * Objetos de Prova para Igualdade *)

(** Recapitule a definição de igualdade no Coq: *)

Print eq.  (* Inductive eq (A : Type) (x : A) : A -> Prop :=
              | eq_refl : x = x
              end. *)

(** Uma vez compreendido o casamento de padrão dependente, a definição
    acima de igualdade se torna bastante simples: ela meramente diz
    que nós podemos sempre substituir o termo à direita do '=' pelo
    termo à esquerda!

    De fato, suponha que nós queremos provar P(y), e que temos

      hxy : x = y
      px : P x

    Nesse caso, basta fazer

      match hxy in _ = a return P a with
      | eq_refl => px
      end

    Usando esse conhecimento e a tática [refine], nós podemos
    facilmente provar os teoremas que nós provávamos usando [rewrite]:
*)

Definition eq_sym: forall (T : Type) (x y : T), x = y -> y = x
  :=
  fun T x y hxy
    =>
    match hxy in _ = y' return y' = x with
    | eq_refl (* ou simplesmente: eq_refl *)
        => @eq_refl T x
    end.


(** EXERCÍCIO: Prove usando uma função recursiva: *)

Definition eq_trans_po:
  forall (T: Type) (x y z : T), x = y -> y = z -> x = z 
  :=
  fun T x y z Hxy Hyz =>
  match Hyz in _ = z' return x = z' with
  | eq_refl => Hxy 
  end.  


(* ================================================================ *)

(** * Objetos de Prova para Contradição *)

(** Uma vez compreendido o conteúdo acima, construir objetos de prova
    para provas por contradição requer apenas mais uma observação: a
    de que uma contradição como

      eq10: 0 = 1

    implica que nós podemos deduzir P(1) a partir de P(0), para
    qualquer [P]! Além disso, já que nós podemos escolher [P] à
    vontade, então P(1) pode ser [False] -- justamente o que
    precisamos para obter qualquer conclusão a partir de [False_ind]
    --, enquanto P(0) pode ser qualquer coisa trivial de demonstrar,
    como [True]!

    Essa estratégia é ilustrada a seguir.
*)

(* ... *)

(* ================================================================ *)