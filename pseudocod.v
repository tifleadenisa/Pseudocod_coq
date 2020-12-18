(*Schitarea ideilor*)

(*memorie: o variabila poate fi nealocata sau alocata (caz in care are un offset-nr nat) *)
Inductive Memory :=
| unallocated : Memory
| offset : nat -> Memory.

(*Stringurile vor fi numele variabilelor*)

Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.

(*Tipuri de variabile*)
Inductive Value :=
| undefined : Value
| natVal : nat -> Value
| boolVal : bool -> Value.

Scheme Equality for Value.

(*o variabila (indiferent de tip) trebuie sa fie stocata la o adresa: nume_variabila->adresa*)

(*fiecare adresa retine o valoare: adresa->valoare*)

Definition Var := string -> Memory -> Value.



(*Urmeaza tipurile: *)
(*AExp adaptat cu mem*)

Inductive AExp :=
| avar : string -> Memory -> nat -> AExp
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
(* Coercion avar : .... >-> AExp. *)

(*BExp*)
Inductive BExp :=
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

(*Vector string-nat(offset)-nat(dimensiune)-value*)
Inductive Vector :=
| VDecl : Var -> nat -> Vector (* variabila, dimensiune *)
| VAssign : Var -> nat -> Value -> Vector (* variabila, al i-lea element, valoare*)
| VLook : Var -> nat -> Vector. 


Notation " A [ B ] " := (VDecl A B)(at level 60).
Notation "A [ B ] <- C" := (VAssign A B C) (at level 61).
Notation "'Afiseaza' A [ B ]" := (VLook A B) (at level 62).

(*Stiva*)
(* Implementare statica, *)
Inductive Stiva :=
(* luam un vector si ii mai adaugam un nat care va retine varful stivei *)
| SStart : Vector ->Stiva
(* pe langa un vector simplu, stiva trebuie sa aiba si functiile de push, pop, top *)
| SPush : Vector -> Value -> Stiva (* vf++ *)
| SPop : Vector -> Stiva (* vf-- *)
| STop : Vector -> Stiva. (* vf-1 *)

Notation " 'stiva' A" := (SStart A) (at level 60).
Notation " A '.Push' ( B )" := (SPush A B) (at level 61).
Notation " A '.Pop'" := (SPop A) (at level 62).
Notation " A '.Top'" := (STop A) (at level 63).

(*Coada*)




(* ?Matrice? *)
(* ?I/O? *)
(* ?Tipuri de erori? *)
(* Tipuri de valori *)

(* Statements *)
(* ?Environment? memorie + nume + tip + valoare*)
(**)

