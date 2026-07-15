(* begin hide *)
Require Import Arith List Lia.
Require Import Recdef.
Require Import Sorted.
Require Import Permutation.
Require Import Lia.
Require Import FunInd.
(* end hide*)

(**
Este trabalho apresenta uma prova formal da correção do algoritmo de ordenação por borbulhamento (a função [bs] a seguir). A formalização foi feita no assistente de provas Coq. O assistente de provas Coq utiliza o sistema de Dedução Natural, o que o torna adequado para o desenvolvimento de atividades computacionais no curso de Lógica Computacional 1. O Coq permite a extração de código certificado em diversas linguagens funcionais, como Ocaml, Haskell e Scheme. *)

(** Iniciaremos definindo a função [bubble] que recebe uma lista de naturais como argumento, e percorre esta lista comparando elementos consecutivos. Chamamos este processo de borbulhamento: *)

Function bubble (l: list nat ) {measure length l} :=
  match l with
  | nil => nil
  | x::nil => x::nil
  | x::y::l =>
      if x <=? y
      then x::(bubble (y::l))
            else y::(bubble (x::l))
            end.
Proof.
  - auto.
  - auto.
Defined.

(** Observe que esta função não é estruturalmente recursiva porque, por exemplo, a lista [(x::l)] não é uma sublista da lista original [(x::y::l)]. Neste caso, utilizamos [Function] para construir esta função e precisamos fornecer a medida que decresce em cada chamada recursiva, além de provar que esta medida efetivamente decresce a cada chamada recursiva. Por exemplo, [bubble (2::1::nil)] retorna a lista [(1::2::nil)].

 *)

Eval compute in bubble (2::1::nil).

(**

<<
   = 1 :: 2 :: nil
     : list nat
>>

*)

Eval compute in bubble (3::2::1::nil).

(**

<<
    = 2 :: 1 :: 3 :: nil
     : list nat
>>

*)

(** A função principal, ou seja, o algoritmo bubble sort propriamente dito, é dada pela função [bs] abaixo que recebe uma lista de naturais como argumento:

*)

Fixpoint bs (l: list nat) :=
  match l with
  | nil => nil
  | h::l' => bubble (h::(bs l'))
  end.    

(* begin hide *)
Eval compute in (bs (1::2::nil)).
Eval compute in (bs (2 :: 1::nil)).
Eval compute in (bs (3 :: 2 :: 1::nil)).
(* end hide *)



(** Sabemos que aplicar a função [bubble] a uma lista qualquer, não necessariamente vai retornar uma lista ordenada, 
mas o lema [bubble_sorted] a seguir nos mostra que se o primeiro elemento é o único elemento fora de ordem em uma lista,
ao aplicarmos a função [bubble], obtemos uma lista ordenada: *)

Lemma bubble_sorted: 
forall l, Sorted le l -> bubble l = l.

Proof.
  (* introduz as implicações*)
  intros l H. 
  
  (* inicia a prova por indução*)
  induction l as [| h t hip]. 
  - trivial.                                (* bubble de nada é nada, portanto, é trivial para nil*)

  - destruct t as [| h' t']. simpl.         (* quebra t em lista de 1 item ou lista de mais de 1 item*)
    + trivial.                              (* t caso [h' :: nil] é trivial*)
    + simpl. rewrite bubble_equation.
      destruct (h <=? h') eqn:Hle.          (* separa os casos do bubble x::y::l*)
      
      * (* if true then x::(bubble (y::l))*)
        simpl. f_equal.                      (* remove o h solto dos dois lados*)
        apply hip. inversion H; subst.       (* aplica a hipótese de indução hip e a tática inversion no H*) 
        apply H2.                            (* usa a hipótese H0 pra chegar na conclusão *)

      * (* if false y::(bubble (x::l))*)            
        inversion H; subst.         (* aplica inversion no H pra pegar construtores*)
        inversion H3; subst.        (* aplica inversion no H3 pra pegar construtores*)
        apply Nat.leb_gt in Hle.    (* transforma o Hle em equação*)
        lia.                        (* aplica regras matemáticas pra finalizar a prova*)
Qed.  


(* Lemma de apoio pro bs_sorted: *)
Lemma bubble_n: forall n l, Sorted le l -> Sorted le (bubble (n::l)).
Proof.
  (* introduções*)
  intros.

  (* aplica indução funcional na bolha*)
  functional induction (bubble (n :: l)).
  - trivial.                                                      (* ordenar nil é trivial*)
  - constructor. trivial. Search (HdRel). apply HdRel_nil.        (* ordenar [x :: nil], aplica o construtor e simplifica a prova por head nil*)
  - constructor. 
    + apply IHl1.                                                  (* ordenar bubble x :: y, aplica hipótese da indução*)
    + apply Nat.leb_le in e0. 
      destruct (bubble (y :: l1)) eqn:Hinduc. trivial.             (* quebra o bubble e resolve o nil*)
      constructor.  assert (Hy_n0 : y <= n0).
      inversion IHl1. subst. lia.                  (* quebra o x <= n0 em y <= n0 e x <= n0*)
      Search (Sorted le ?l). apply bubble_sorted in IHl1. 

   
Qed.
     
Lemma bs_sorted: forall l, Sorted le (bs l).
Proof.
  intros. 
  induction l as [| h t hip].
  - trivial.                                  (* bubble sort de nada é nada, portanto é trivial para nil*)
  - simpl. induction (bs t) as [| h' t' ] eqn:Esort.

    (* h :: nil*)
    + apply bubble_n.

    apply hip.


Qed.

(** A seguir, mostraremos que o algoritmo bubblesort (função [bs]) gera como saída uma permutação da lista de entrada. 
O lema a seguir nos diz que a função [bubble] também gera uma permutação da entrada: *)

Lemma bubble_perm: forall l, Permutation l (bubble l).
Proof.
  intro l. functional induction (bubble l). Admitted.

(** O lema [bs_permuta] a seguir, nos mostra que o algoritmo [bs] gera uma permutação da lista de entrada: *)

Lemma bs_permuta: forall l, Permutation l (bs l).
Proof. 
  (* instroduz a lista l*)
  intro l.

  (* inicia a prova por indução*)
  induction l as [| h t hip].         
  - trivial.                                              (* permutação de nada é nada, prova trivial*)
  - simpl. destruct (bs t) as [| h' t'] eqn:Eperm.        (* simplifica pro bubble e separa t como lista com head e tail*)
    + (* casos [nil] e [h :: nil]*)
      apply Permutation_sym in hip. apply Permutation_nil in hip.  
      subst. apply Permutation_refl.

    + (* caso de listas de mais de um item [x :: y :: t]*)
      destruct (h <=? h').                (*separa os casos do bubble*)
      * Search Permutation. perm_skip.          (*COM ERRO CORRIGIR!!!!!!!!!!!*)
        apply hip.       
      * rewrite perm_swap. apply perm_skip. apply hip.  (*COM ERRO CORRIGIR!!!!!!!!!!!*)
Qed.

(** Por fim, a correção do algoritmo [bs] é obtida pelo teorema a seguir que estabelece que o algoritmo [bs] 
retorna uma permutação da lista de entrada que está ordenada: *)
    
Theorem bs_correto: forall l, Sorted le (bs l) /\ Permutation l (bs l).
Proof.
Admitted.  

(** Repositório: %\url{https://github.com/flaviodemoura/bubble_sort}% *)
