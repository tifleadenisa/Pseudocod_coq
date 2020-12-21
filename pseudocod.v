(*Schitarea ideilor*)

(*memorie: o variabila poate fi nealocata sau alocata (caz in care are un offset-nr nat) *)
Inductive Memory :=
| unallocated : Memory
| offset : nat -> Memory.

Coercion offset : nat >-> Memory.

(*Stringurile vor fi numele variabilelor*)

Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.

(*Tipuri de variabile*)
Inductive Value :=
| undefined : Value
| error : Value
| natVal : nat -> Value
| boolVal : bool -> Value.

Scheme Equality for Value.

Coercion natVal : nat >-> Value.
Coercion boolVal : bool >-> Value.

(*o variabila (indiferent de tip) trebuie sa fie stocata la o adresa: nume_variabila->adresa*)

(*fiecare adresa retine o valoare: adresa->valoare*)

Definition Var := string -> Memory -> Value.


(*Urmeaza tipurile: *)
(*AExp adaptat cu mem*)

Inductive AExp :=
| avar : string -> AExp (* Initial am vrut sa pun var -> AExp*)
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| asub : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.


Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (asub A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).
Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.

Check ( 2 +' 3 *' 5).
Check ( 2 +' "x" *' 5).
Check ( "x" ). (* Nu tocmai ok *)

(*BExp*)
Inductive BExp :=
(* | bvar : string -> BExp *)
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

Notation "A <=' B" := (blessthan A B) (at level 53).
Notation "A >=' B" := (blessthan A B) (at level 54).
Notation "!' A" := (bnot A ) (at level 40).
Notation "A &&' B" := (band A B) (at level 41).
Notation "A ||' B" := (bor A B) (at level 42).

(*Vector*)
Inductive Vector :=
| VDecl : string -> nat -> Vector (* variabila, dimensiune *)
| VAssign : string -> nat -> Value -> Vector (* variabila, al i-lea element, valoare*)
| VLook : string -> nat -> Vector. 

(* Oare se poate parcurge? sau ar trebui inlocuit Var?*)


Notation " A [ B ] " := (VDecl A B)(at level 60).
Notation "A [ B ] <<- C" := (VAssign A B C) (at level 61).
Notation "'Afiseaza' A [ B ]" := (VLook A B) (at level 62).

Check ( "V" [10]).
(* Check ( "x" [3] <<- 5). *) (* eroare *)



(*Stiva*)
(* Implementare statica, *)
Inductive Stiva :=
(* ?luam un vector (?si ii mai adaugam un nat care va retine varful stivei?) *)
| SDecl : string ->Stiva
(* pe langa un vector simplu, stiva trebuie sa aiba si functiile de push, pop, top *)
| SPush : Vector -> Value -> Stiva (* vf++ *)
| SPop : Vector -> Stiva (* vf-- *)
| STop : Vector -> Stiva. (* vf-1 *)

Notation " 'Stiva' A" := (SDecl A) (at level 60).
Notation " A 'SPush' ( B )" := (SPush A B) (at level 61).
Notation " A 'SPop'" := (SPop A) (at level 62).
Notation " A 'STop'" := (STop A) (at level 63).

Check ( Stiva "S" ).
(* Check ( "a" SPush ). *)

(*Coada*)
Inductive Coada :=
(* luam un vector si ii mai adaugam un nat care va retine varful stivei *)
| CStart : Vector -> Coada
(* pe langa un vector simplu, coada trebuie sa aiba si functiile de push, pop, front *)
| CPush : Vector -> Value -> Coada (* dr++ *)
| CPop : Vector -> Coada (* st++ *)
| CFront : Vector -> Coada. (* st *)

Notation " 'Coada' A" := (CStart A) (at level 64).
Notation " A '.CPush' ( B )" := (CPush A B) (at level 65).
Notation " A '.CPop'" := (CPop A) (at level 66).
Notation " A '.CFront'" := (CFront A) (at level 67).



(* Matrice *)
(* Asemanator cu vector, adaugam inca un nat *)
Inductive Matrice :=
| MDecl : string -> nat -> nat -> Matrice (* variabila, dimensiune *)
| MAssign : string -> nat -> nat -> Value -> Matrice (* variabila, al i-lea element, valoare*)
| MLook : string -> nat -> nat -> Matrice. 

Notation " A [ B ] [ C ] " := (MDecl A B C)(at level 60).
Notation "A [ B ] [ C ] <<- D" := (MAssign A B C D) (at level 61).
Notation "'Afiseaza' A [ B ] [ C ]" := (MLook A B C) (at level 62).

Check ( "A" [10] [10] ).
(*
Check ( Afiseaza "A" [ 2 ] [ 3 ] ).

Check ( "A" [1] [2] <<- 3 ). 
*)


(* Simulare I/O *)
(* Implementare pe baza de coada *)
(*-----------------------------*)

(* Statements *)
Inductive Stmt :=
| natDecl : string -> nat -> Stmt (*pt variabile*)
| boolDecl : string -> bool -> Stmt 
| natVector : Vector -> Stmt (*am declararea in vector, oare e ok asa? *)
| boolVector : Vector ->  Stmt
(*| natStiva : Stiva -> Stmt 
| boolStiva : Stiva -> Stmt
| natCoada : Coada -> Stmt 
| boolCoada : Coada -> Stmt *)
| natMatrice : Matrice -> Stmt 
| boolMatrice : Matrice -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| forr : Stmt -> BExp -> Stmt -> Stmt -> Stmt .

Notation "'natural' A <- B" := (natDecl A B)(at level 70).
Notation "'bool' A <- B" := (boolDecl A B)(at level 71).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90, left associativity).
Notation "'iff' A 'thenn' B 'elsee' C" := (ifthenelse A B C) (at level 91).
Notation "'whilee' ( A ) B" := (while A B)(at level 92).
Notation "forr ( A ,, B ,, C ) S " := (forr A B C S)(at level 93).

(* ?Environment? memorie + nume + tip + valoare, adica var+value?*)
(**)

