(* begin hide *)
Require Import Arith List Lia.
Require Import Recdef.
Require Import Sorted.
Require Import Permutation.
Require Import Lia.
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
  
  (* l como [ | head tail hipótese_indução]*)
  induction l as [| h t hip]. 
  - trivial.      (* bubble de nada é nada, portanto, é trivial para nil*)

  - destruct t as [| h' t']. simpl.       (* quebra t em lista de 1 item ou lista de mais de 1 item*)
    + trivial.                            (* t caso [h' :: nil] é trivial*)
    + simpl. rewrite bubble_equation.
      destruct (h <=? h') eqn:Hle.          (* separa os casos do bubble x::y::l*)
      
      * (* if true then x::(bubble (y::l))*)
        simpl. f_equal.                     (* remove o h*)
        apply hip. inversion H; subst.       (* aplica a hipótese de indução hip e a inversão limpando o H*) 
        apply H2.                           (* usa a hipótese H0 pra chegar na conclusão *)

      * (* if false y::(bubble (x::l))*)
        f_equal.                                (*COM ERRO CORRIGIR!!!!!!!!!!!*)
        inversion H; subst.         
        apply Nat.leb_gt in Hle.
        lia. 
        contradiction Hle.

        

Qed.  

     
Lemma bs_sorted: forall l, Sorted le (bs l).
Proof.
  intros. 
  induction l as [| h t hip].
  - trivial.
  - simpl.   (*INCOMPLETO CORRIGIR!!!!!!!!!!!*)


(** A seguir, mostraremos que o algoritmo bubblesort (função [bs]) gera como saída uma permutação da lista de entrada. 
O lema a seguir nos diz que a função [bubble] também gera uma permutação da entrada: *)

Lemma bubble_perm: forall l, Permutation l (bubble l).
Proof.
  intro l. functional induction (bubble l). Admitted.

(** O lema [bs_permuta] a seguir, nos mostra que o algoritmo [bs] gera uma permutação da lista de entrada: *)

Lemma bs_permuta: forall l, Permutation l (bs l).
Proof. 
  intro l. induction l as [| h t hip].
  - trivial.
  - simpl. destruct (bs t) as [| h' t'] eqn:Ebpt.
    + apply Permutation_sym in hip. apply Permutation_nil in hip.
      subst. apply Permutation_refl.
    + destruct (h <=? h').
      * apply perm_skip. apply hip.  (*COM ERRO CORRIGIR!!!!!!!!!!!*)
      * rewrite perm_swap. apply perm_skip. apply hip.  (*COM ERRO CORRIGIR!!!!!!!!!!!*)
Qed.

(** Por fim, a correção do algoritmo [bs] é obtida pelo teorema a seguir que estabelece que o algoritmo [bs] 
retorna uma permutação da lista de entrada que está ordenada: *)
    
Theorem bs_correto: forall l, Sorted le (bs l) /\ Permutation l (bs l).
Proof.
Admitted.  

(** Repositório: %\url{https://github.com/flaviodemoura/bubble_sort}% *)
