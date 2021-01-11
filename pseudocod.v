


(*Stringurile vor fi numele variabilelor*)

Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.





(*Urmeaza tipurile: *)
(*AExp*)

Inductive AExp :=
| avar : string -> AExp 
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| asub : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Scheme Equality for AExp.


Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (asub A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).
Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.

Check ( 2 +' 3 *' 5).
Check ( 2 +' "x" *' 5).
Check ( 1 +' "s").
Check ( 1 = 1).

(*BExp*)
Inductive BExp :=
| bvar : string -> BExp
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bequal : BExp -> BExp -> BExp
| aequal : AExp -> AExp -> BExp
| bor : BExp -> BExp -> BExp.

Coercion bvar : string >-> BExp.

Scheme Equality for BExp.

Notation "A =' B" := (aequal A B) (at level 47). 
Notation "A ='' B" := (bequal A B) (at level 47). 
Notation "A <=' B" := (blessthan A B) (at level 53).
Notation "A >=' B" := (blessthan A B) (at level 54).
Notation "!' A" := (bnot A ) (at level 40).
Notation "A &&' B" := (band A B) (at level 41).
Notation "A ||' B" := (bor A B) (at level 42).

(*Tipuri de variabile*)
Inductive Value :=
| undefined : Value
| error : Value
| natVal : nat -> Value
| boolVal : bool -> Value.

Scheme Equality for Value.

Coercion natVal : nat >-> Value.
Coercion boolVal : bool >-> Value. 


Check ("ok" >=' 5). (*Nu tocmai ok*)

(*Vector*)
Inductive Vector :=
| VDecl : string -> nat -> Vector (* variabila, dimensiune *)
| VAssign : string -> nat -> Value -> Vector (* variabila, al i-lea element, valoare*)
| VLook : string -> nat -> Vector. 



Notation " 'Vectorr' A [ B ] " := (VDecl A B)(at level 60).
Notation "'VAsigneaza' A [ B ] <-' C" := (VAssign A B C) (at level 61).
Notation "'VAfiseaza' A [ B ]" := (VLook A B) (at level 62).

Check ( Vectorr "V" [10]).
Check ( VAsigneaza "x" [3] <-' 5). 
Check (VAfiseaza "A"[5]).



(*Stiva*)
(* Implementare statica, *)
Inductive Stiva :=
(* ?luam un vector (?si ii mai adaugam un nat care va retine varful stivei?) *)
| SDecl : string ->Stiva
(* pe langa un vector simplu, stiva trebuie sa aiba si functiile de push, pop, top *)
| SPush : string -> Value -> Stiva (* vf++ *)
| SPop : string -> Stiva (* vf-- *)
| STop : string -> Stiva. (* vf-1 *)

Notation " 'Stivaa' A" := (SDecl A) (at level 60).
Notation " A 'SPush' ( B )" := (SPush A B) (at level 61).
Notation " A 'SPop'" := (SPop A) (at level 62).
Notation " A 'STop'" := (STop A) (at level 63).

Check ( Stivaa "S" ).
Check ( "a" SPush (3) ).
Check ("S" SPop).
Check ("A" STop).

(*Coada*)
Inductive Coada :=
| CStart : string -> Coada
(* pe langa un vector simplu, coada trebuie sa aiba si functiile de push, pop, front *)
| CPush : string -> Value -> Coada (* dr++ *)
| CPop : string -> Coada (* st++ *)
| CFront : string -> Coada. (* st *)

Notation " 'Coadaa' A" := (CStart A) (at level 64).
Notation " A 'CPush' ( B )" := (CPush A B) (at level 65).
Notation " A 'CPop'" := (CPop A) (at level 66).
Notation " A 'CFront'" := (CFront A) (at level 67).

Check ( Coadaa "S" ).
Check ( "a" CPush (3) ).
Check ("S" CPop).
Check ("A" CFront).




(* Matrice *)
(* Asemanator cu vector, adaugam inca un nat *)
Inductive Matrice :=
| MDecl : string -> nat -> nat -> Matrice (* variabila, dimensiune *)
| MAssign : string -> nat -> nat -> Value -> Matrice (* variabila, al i-lea element, valoare*)
| MLook : string -> nat -> nat -> Matrice. 

Notation " 'Matricee' A [ B ] [ C ] " := (MDecl A B C)(at level 60).
Notation "'MAsigneaza' A [ B ] [ C ] <-' D" := (MAssign A B C D) (at level 61).
Notation "'MAfiseaza' A [ B ] [ C ]" := (MLook A B C) (at level 62).

Check ( Matricee "A" [10] [10] ).
Check ( MAfiseaza "A" [ 2 ] [ 3 ] ).
Check ( MAsigneaza "A" [1] [ 2 ] <-' 3 ). 



(* Simulare I/O *)
(*Va fi posibila simularea I/O de genul: *)
(* Implementare pe baza de coada *)
(*-----------------------------*)
(*
Inductive InputOutput :=
| write : string -> InputOutput
| read : Value -> InputOutput.

Coercion write : string >-> InputOutput.
Coercion read : Value >-> InputOutput.
*)


(* Statements *)
Inductive Stmt :=
| natVarDecl : string -> Stmt (*pt variabile*)
| boolVarDecl : string -> Stmt 
| natVarAssign : string -> AExp -> Stmt (*pt variabile*)
| boolVarAssign : string -> BExp -> Stmt 
| natVector : Vector -> Stmt (*am declararea in vector, oare e ok asa? *)
| boolVector : Vector ->  Stmt
| natStiva : Stiva -> Stmt 
| boolStiva : Stiva -> Stmt
| natCoada : Coada -> Stmt 
| boolCoada : Coada -> Stmt 
| natMatrice : Matrice -> Stmt 
| boolMatrice : Matrice -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt.
(*| forr : Stmt -> BExp -> Stmt -> Stmt -> Stmt . *)

Coercion natVector : Vector >-> Stmt.
Coercion natStiva : Stiva >-> Stmt.
Coercion natCoada : Coada >-> Stmt.
Coercion natMatrice : Matrice >-> Stmt.

Notation "'VarNatural' A" := (natVarDecl A)(at level 68).
Notation "'VarBool' A " := (boolVarDecl A )(at level 69).
Notation " A '<n=' B" := (natVarAssign A B)(at level 70).
Notation " A '<b=' B" := (boolVarAssign A B)(at level 71).
Notation " 'VNatural' A" := (natVector A) (at level 68).
Notation " 'VBool' A" := (boolVector A) (at level 68).
Notation " 'SNatural' A" := (natStiva A) (at level 68).
Notation " 'SBool' A" := (boolStiva A) (at level 68).
Notation " 'CNatural' A" := (natCoada A) (at level 68).
Notation " 'CBool' A" := (boolCoada A) (at level 68).
Notation " 'MNatural' A" := (natMatrice A) (at level 68).
Notation " 'MBool' A" := (boolMatrice A) (at level 68).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90, left associativity).
Notation "'iff' A 'thenn' B 'elsee' C" := (ifthenelse A B C) (at level 91).
Notation "'whilee' ( A ) { B }" := (while A B)(at level 92).
Notation "'forr' ( A ,, B ,, C ) { S }" := ( A ;; while B (S ;; C) )(at level 97, B at level 9).

Check (VarNatural "s").
Check (VarBool "ok").
Check ("a" <n= 3).
Check ("a" <b= btrue).
Check ( "a" SPush (3) ).
Check ( "a" SPush (3) ;; "a" SPush (5) ).
Check ( MAfiseaza "A" [ 2 ] [ 3 ] ;; "a" SPush (5) ).
Check ( VNatural Vectorr "V" [10] ).
Check ( VAsigneaza "x" [3] <-' 5 ;; VAfiseaza "A"[5] ).
Check ( iff ("i" <=' 5) thenn ( "i" <n= 1 ) elsee ( "i" <n= 3)).
Check ( whilee ( "i" <=' 5) {"i" <n= "i" +' 1} ).
Check("i"<='5).
Check("i" <n= 1).
Check("i" <n= "i" +' 1).
Check (forr ( ("i" <n= 1 ) ,, ("i" <=' 5) ,, ("i" <n= "i" +' 1) )  {"i" <n= "i" +' 1} ).


Check
(
VarNatural "s" ;;
"s" <n= 0 ;;
VarNatural "i" ;;
whilee ( "i"<=' 5)
{
  "s" <n= "s" +' "i";;
  "i" <n= "i" +' 1
}

).

Check
(
VarNatural "s" ;;
"s" <n= 5;;
VarBool "ok";;
"ok" <b= btrue;;
whilee ("ok" ='' btrue )
{
  "s" <n= "s" +' 1 ;;
  iff ( "s" %' 2 =' 0 ) thenn
      "ok" <b= btrue
  elsee
      "ok" <b= bfalse 
}

).

Check 
(
MNatural (Matricee "A" [ 2 ] [ 1 ]) ;;
MNatural (MAsigneaza "A" [ 1 ] [ 1 ] <-' 0);;
MNatural (MAsigneaza "A" [ 2 ] [ 1 ] <-' 1) ;;
MNatural ( MAfiseaza "A" [ 2 ] [ 1 ] ) ;;

CBool (Coadaa "C") ;;
CBool ("C" CPush (true)) ;;
CBool ("C" CPop);;
CBool ("C" CFront);;

SBool (Stivaa "S");;
SBool ( "S" SPush (true) );;
SBool ( "S" SPop);;
SBool ( "S" STop);;

VBool ( Vectorr "V" [ 3 ] );;
VBool ( VAsigneaza "V" [1] <-' 1 );;
VBool ( VAsigneaza "V" [2] <-' 1 );;
VBool ( VAsigneaza "V" [3] <-' 1 );;
VBool ( VAfiseaza "V" [2] )

).


(*------------------------*)

(*------SEMANTICA---------*)

(*------------------------*)

(*o variabila (indiferent de tip) trebuie sa fie stocata la o adresa: nume_variabila->adresa*)

(*fiecare adresa retine o valoare: adresa->valoare*)

(*memorie: o variabila poate fi nealocata sau alocata (caz in care are un offset-nr nat) *)
Inductive Memory :=
| unallocated : Memory
| offset : nat -> Memory.

Scheme Equality for Memory.

Coercion offset : nat >-> Memory.

Definition Env := string -> Memory.

Definition MemLayer := Memory -> Value. 

Definition mlayer : MemLayer := fun x => undefined.

Definition env : Env := fun x => unallocated.

Definition update_env (env: Env) (x: string) (n: Memory) : Env :=
  fun y =>
      if (andb (string_beq x y ) (Memory_beq (env y) unallocated))
      then
        n
      else
        (env y).

Compute (env "z"). 

Compute ((update_env env "x" (offset 9)) "x").


Definition update_mem (layer: MemLayer) (x: Memory) (n: Value) : MemLayer :=
  fun y =>
    if( andb (Memory_beq x y) (Value_beq n (layer y)) ) (*sunt egale adresele si value egal*)
    then
       (layer y)
    else
      n.

Compute ((update_mem mlayer (offset 9) (natVal 5)) (offset 9)).



(*update_env pentru vectori *)

Fixpoint update_env_vector (env: Env) (x: string) (m: nat) (n: Memory) : Env :=
match m with 
| 0 => env
| S m' => match n with
           | unallocated => env
           | offset of => (update_env_vector (update_env env x (of+m')) x m' (of+1))
            end
end.

Compute ((update_env_vector env "x" 9 (offset 6)) "x").



(*
Definition valueFromString (env: Env) (s: string) (mem: Memory) (layer: MemLayer) : Value :=
fun y=>
    if (andb (string_beq s y ) (negb (env y) unallocated)) (*daca exista*)
    then
           if (andb (Memory_beq mem (mem y)) (Value_beq mem (layer y))) (*sunt egale adresele*)
           then (layer y)
           else undefined
    else (mlayer (env y)).
*)


(* Big-step SOS AExp *)

Reserved Notation "A =[ S , T ]=> N" (at level 60).
Inductive aeval : AExp -> Env -> MemLayer -> Value -> Prop :=
| const : forall n sigma tau, anum n =[ sigma , tau ]=> n 
| var : forall v sigma tau, avar v =[ sigma , tau ]=> (tau (sigma v))
(* | varVector : forall v sigma tau, avar v =[ sigma , tau ]=> tau(update_env_vector v number sigma(v))*)
| add : forall a1 a2 i1 i2 sigma tau n,
    a1 =[ sigma , tau ]=> natVal i1 ->
    a2 =[ sigma , tau ]=> natVal i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma , tau]=> n
| times : forall a1 a2 i1 i2 sigma tau n,
    a1 =[ sigma , tau ]=> natVal i1 ->
    a2 =[ sigma , tau ]=> natVal i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma , tau]=> n
| substract : forall a1 a2 i1 i2 sigma tau n,
    a1 =[ sigma , tau ]=> natVal i1 ->
    a2 =[ sigma , tau ]=> natVal i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[sigma , tau]=> n
| divide : forall a1 a2 i1 i2 sigma tau n,
    a1 =[ sigma , tau ]=> natVal i1 ->
    a2 =[ sigma , tau ]=> natVal i2 ->
    n = Nat.div i1 i2 ->
    a1 /' a2 =[sigma , tau]=> n
|modulo : forall a1 a2 i1 i2 sigma tau n,
    a1 =[ sigma , tau ]=> natVal i1 ->
    a2 =[ sigma , tau ]=> natVal i2 ->
   
    a1 %' a2 =[sigma , tau]=> n
where "a =[ sigma , tau ]=> n" := (aeval a sigma tau n).

Compute ((update_env env "x" (offset 9)) "x").
Compute ((update_mem mlayer (offset 9) (natVal 5)) (offset 9)).

(*
Example ex0 : "x" =[ env , mlayer ]=> 5.
Proof.
  eauto.
Qed.
*)

Example ex1 : 2 =[ env, mlayer ]=> 2.
Proof.
  apply const.
Qed.

Example ex2 : 2+'2 =[ env, mlayer ]=> 4.
Proof.
  eapply add.
  eapply const.
  eapply const.
  reflexivity.
Qed.

(*
Compute ((update_env env "sum" (offset 11)) "sum").
Compute ((update_mem mlayer (offset 11) (natVal 0)) (offset 11)).
Example ex3 : "sum" =[ env , mlayer ]=> 0.
Proof.
  eapply var.
Qed.
*)



Reserved Notation "B ={ S , T }=> B'" (at level 70).

Inductive beval : BExp -> Env -> MemLayer -> Value -> Prop :=
| e_true : forall sigma tau, btrue ={ sigma , tau }=> true
| e_false : forall sigma tau, bfalse ={ sigma , tau }=> false
| eb_var : forall v sigma tau, bvar v ={ sigma , tau }=> (tau (sigma v))
| e_lessthan : forall a1 a2 i1 i2 sigma tau b,
    a1 =[ sigma , tau ]=> natVal i1 ->
    a2 =[ sigma , tau ]=> natVal i2 ->
    b = Nat.leb i1 i2 ->
    a1 <=' a2 ={ sigma , tau }=> b
| e_nottrue : forall b sigma tau,
    b ={ sigma , tau }=> true ->
    (bnot b) ={ sigma , tau }=> false
| e_notfalse : forall b sigma tau,
    b ={ sigma , tau }=> false ->
    (bnot b) ={ sigma , tau }=> true
| e_andtrue : forall b1 b2 sigma tau t,
    b1 ={ sigma , tau }=> true ->
    b2 ={ sigma , tau }=> t ->
    band b1 b2 ={ sigma , tau }=> t
| e_andfalse : forall b1 b2 sigma tau,
    b1  ={ sigma , tau }=> false ->
    band b1 b2 ={ sigma , tau }=> false
where "B ={ S , T }=> B'" := (beval B S T B').


Example ex4 : (bnot btrue) ={ env, mlayer }=> false.
Proof.
  eapply e_nottrue.
  eapply e_true.
Qed.


Compute ((update_env env "ok" (offset 10)) "ok").
Compute ((update_mem mlayer (offset 10) (boolVal true)) (offset 9)).

(*
Example ex5 : "x" ={ env , mlayer }=> 5.
Proof.
  eapply eb_var.
Qed.
*)



Reserved Notation "B -{ S , T }-> C" (at level 60).


Inductive eval : Stmt -> Env -> MemLayer -> MemLayer -> Prop :=
| e_nat_decl: forall a i x sigma tau tau',
   a =[ sigma , tau ]=> i ->
   tau' = (update_mem tau (env x) undefined ) ->
   (VarNatural x) -{ sigma , tau }-> tau'
| e_bool_decl: forall a i x sigma tau tau',
   a =[ sigma , tau ]=> i ->
   tau' = (update_mem tau (env x) undefined ) ->
   (VarBool x) -{ sigma , tau }-> tau'
| e_nat_assign: forall a i x sigma tau tau',
    a =[ sigma , tau ]=> (natVal i) ->
    tau' = (update_mem tau (env x) (natVal i)) ->
    (x <n= a) -{ sigma , tau }-> tau'
| e_bool_assign: forall a i x sigma tau tau',
    a ={ sigma ,tau }=> (boolVal i) ->
    tau' = (update_mem tau (env x) (boolVal i)) ->
    (x <b= a) -{ sigma , tau }-> tau'
(*
| e_natVector : forall a i x sigma tau tau',
   a =[ sigma , tau ]=> i ->
   tau' = (update_mem tau (env x) undefined ) ->
   (natVector x) -{ sigma , tau }-> tau'
*)
| e_seq : forall s1 s2 sigma tau tau1 tau2,
    s1 -{ sigma , tau }-> tau1 ->
    s2 -{ sigma ,  tau1 }-> tau2 ->
    (s1 ;; s2) -{ sigma , tau }-> tau2
| e_if_then : forall b s sigma tau,
    ifthen b s -{ sigma , tau }-> tau
| e_if_then_elsetrue : forall b s1 s2 sigma tau tau',
    b ={ sigma , tau }=> true ->
    s1 -{ sigma , tau }-> tau' ->
    ifthenelse b s1 s2 -{ sigma , tau }-> tau' 
| e_if_then_elsefalse : forall b s1 s2 sigma tau tau',
    b ={ sigma , tau }=> false ->
    s2 -{ sigma , tau }-> tau' ->
    ifthenelse b s1 s2 -{ sigma , tau }-> tau' 
| e_whilefalse : forall b s sigma tau,
    b ={ sigma , tau }=> false ->
    while b s -{ sigma , tau }-> tau
| e_whiletrue : forall b s sigma tau tau',
    b ={ sigma  , tau }=> true ->
    (s ;; while b s) -{ sigma , tau }-> tau' ->
    while b s -{ sigma , tau }-> tau'
where "s -{ sigma , tau }-> tau'" := (eval s sigma tau tau').






