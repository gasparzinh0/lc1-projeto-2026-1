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

(* Lemma de apoio pro bubble_n, resolve as cabeças das listas*)
Lemma bubble_head_le : forall y l n0 l0, 
  bubble (y :: l) = n0 :: l0 -> Sorted le (y :: l) -> y <= n0.
Proof.
  intros y l n0 l0 H_bub H_sort.
  assert (H_simpl : bubble (y :: l) = y :: l).
  apply bubble_sorted. exact H_sort.
  rewrite H_simpl in H_bub.
  injection H_bub as Hy_n0 _.
  subst n0.
  lia. 
Qed.

(* Lemma de apoio pra facilitar a resolução do bs_sorted: *)
Lemma bubble_n: forall n l, Sorted le l -> Sorted le (bubble (n::l)).
Proof.
  (* introduções*)
  intros.
  induction l as [| h t Hinduc].

  constructor. trivial. trivial.
  rewrite bubble_equation.
  destruct (n <=? h ) eqn: hip.
  - constructor.  (* hip verdadeira*)
    + (* caso 1: Sorted le (bubble (n0 :: l)) *)
      assert (H_bubble_cauda : bubble (h :: t) = h :: t). 
      apply bubble_sorted. exact H.
      rewrite H_bubble_cauda. exact H.

    + (* caso HdRel le n (bubble (n0 :: l)) *)
      (* Criamos a simplificação da cauda pelo lema bubble_sorted *)
      assert (H_bubble_cauda : bubble (h :: t) = h :: t). 
      apply bubble_sorted. exact H.
      (* Substituímos no HdRel *)
      rewrite H_bubble_cauda. (* simplifica o HdRel para n <= n0 *)
      constructor. apply Nat.leb_le in hip. exact hip.
  
  - constructor. (* hip falso*)
    + (* Sub-caso 1: Sorted le (bubble (n0 :: l)) *)
      assert (H_bubble_cauda : bubble (h :: t) = h :: t). 
      apply bubble_sorted. exact H.
      inversion H; subst. 
      apply Hinduc. apply H2.
      
    + (* Sub-caso 2: HdRel le n (bubble (n0 :: l)) *)
      destruct t as [| n1 l1]. 
      
      * rewrite bubble_equation. constructor. 
        apply Nat.leb_gt in hip. lia.

      * rewrite bubble_equation.
        destruct (n <=? n1) eqn:hn1.
          (* Se n <= n1, n fica na frente: vira n0 <= n *)
          constructor. apply Nat.leb_gt in hip. lia.
          (* Se n > n1, n1 fica na frente: vira n0 <= n1 *)
          constructor. 
          inversion H; subst. inversion H3; subst. assumption.
Qed.
     
Lemma bs_sorted: forall l, Sorted le (bs l).
Proof.
  intros. 
  induction l as [| h t hip].
  - trivial.                                  (* bubble sort de nada é nada, portanto é trivial para nil*)
  - simpl. apply bubble_n. apply hip.         (* aplica o bubble_n e a hipótese pra resolução*) 

Qed.


(** A seguir, mostraremos que o algoritmo bubblesort (função [bs]) gera como saída uma permutação da lista de entrada. 
O lema a seguir nos diz que a função [bubble] também gera uma permutação da entrada: *)

Lemma bubble_perm: forall l, Permutation l (bubble l).
Proof.
  (* introduz lista l*)
  intro l. 

  (* inicia a prova por indução funcional*)
  functional induction (bubble l).
  - trivial.                        (* permutação de nada é nada, portanto, prova trivial*)
  - trivial.                        (* permutação de x com nada [x :: nil] é trivial*)
  - constructor. apply IHl0.        (* tira o x e aplica a hipótese de indução*)
  - destruct bubble.                (* quebra a bolha*)
    + (* caso y :: nil*)
      apply Permutation_sym in IHl0.                         (* permuta o nil da hipótese*)
      apply Permutation_nil_cons in IHl0. inversion IHl0.    (* simplifica a hipótese pra falso e finaliza*)
                            
    + (* caso lista com mais de dois itens [y :: n :: l]*)
      eapply perm_trans.              (* transforma a lista secundária em uma lista qualquer pra assumir a lista principal*)
      apply perm_swap.                (* substitui a lista qualquer, juntando os dois casos*)
      constructor. apply IHl0.        (* limpa o goal e aplica a hipótese de indução*)

Qed.


(** O lema [bs_permuta] a seguir, nos mostra que o algoritmo [bs] gera uma permutação da lista de entrada: *)

Lemma bs_permuta: forall l, Permutation l (bs l).
Proof. 
  (* instroduz a lista l*)
  intro l.

  (* inicia a prova por indução*)
  induction l as [| h t hip].      
  - trivial.                                 (* permutação de nada é nada, prova trivial*)
  - apply Permutation_sym. eapply Permutation_trans. apply Permutation_sym.       (* generaliza h :: t pra lista qualquer ?l'*)
    simpl. apply bubble_perm. constructor. apply Permutation_sym. apply hip.      (* usa bubble_perm pra limpar as hipóteses e fecha a prova*)
 
Qed.

(** Por fim, a correção do algoritmo [bs] é obtida pelo teorema a seguir que estabelece que o algoritmo [bs] 
retorna uma permutação da lista de entrada que está ordenada: *)
    
Theorem bs_correto: forall l, Sorted le (bs l) /\ Permutation l (bs l).
Proof.
  (* introduções*)
  intros.

  (* quebra a proposição em 2 lados -> Sorted e Permutation*)
  split.
  - apply bs_sorted.            (* Aplicamos a prova constuída bs_sorted*)
  - apply bs_permuta.           (* Aplicamos a prova constuída bs_permuta*)

Qed.


(** Repositório: %\url{https://github.com/flaviodemoura/bubble_sort}% *)
