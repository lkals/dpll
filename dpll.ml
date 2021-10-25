open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)

let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* simplifie : int -> int list list -> int list list
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)

(*
lui donner une fonction qui prend une liste ( ca sera une clause en fin ) et qui envoie
| None si cette liste contient un certain élément
| Some l où l est cette liste 'moins' la négation d'un certain élément
*)


(* renvoie si l contient x*)
let rec contient x l =
  match l with
  | [] -> false
  | e::reste -> if e=x then true
      else contient x reste

(*renvoie la liste l sans la negation de x*)
(*qu° : peut-il y avoir 2 negations ?*)
let rec mnegation x l lpre=
  match l with
  | [] -> []
  | e::reste -> if -x=e then lpre@reste else mnegation x reste (e::lpre)

(*TODO : verifier que List.rev fasse bien ce qu'on demande *)
let simplifie i clauses = 
let filtr l = if contient i l then None else Some (mnegation i l [])
in List.rev (filter_map filtr clauses)
 



  (*let rec aux i clauses =
  match clauses with
  | [] -> failwith "liste vide"
  | c::cl -> aux i (filter_map (fun a -> if contient i a then None else Some (mnegation i a [])) c)::cl
  in aux clauses*)


(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (* branchement *)
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
let () = print_modele (solveur_split systeme [])
let () = print_modele (solveur_split coloriage [])


(* solveur dpll récursif *)

(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)

exception Not_found
exception Failure of string

let rec unitaire clauses =
      match clauses with 
      | [] -> raise Not_found
      | e :: l -> if (List.length e) = 1 then (List.hd e)
      else unitaire l

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)

(*let rec appartient x l =
    match l with
    | [] -> false
    | e :: l' -> if e = x then true else appartient x l'

let rec list_of_props clauses liste =
    match clauses with
    | [] -> liste
    | e :: l -> 
        match e with
        | [] -> list_of_props l liste
        | f :: l' -> if appartient f liste then list_of_props l'@l liste
        else list_of_props l'@l e::liste*)

(*let rec cherche_pur x clauses =
    match clauses with
    | [] -> true
    | e :: l' ->
        match e with
        | [] -> cherche_pur x l'
        | f :: l'' -> if f = -x then false
        else cherche_pur x [l'']@l'
        *)

(*let rec cherchep x cltmp clauses =
  match clauses with
  [] -> true
  | e::l' ->
    match e with
    | [] -> cherche_pur x l'
    | f::l'' -> if f=-x then false
    else cherche_pur x 
*)

let rec list_props_cl clause l=
  match clause with
  | [] -> []
  | e::reste -> list_props_cl reste (e::l)
  
let rec list_props clauses l=
  match clauses with
  | [] -> []
  | c::reste -> list_props reste (list_props_cl c [])@l 

let rec enleve_p_et_non_p x l lpre=
  match l with
  | [] -> lpre
  | e::reste -> if (x=e || -x=e) then enleve_p_et_non_p x reste lpre else enleve_p_et_non_p x reste (e::lpre)

(*let rec pur_pas_bon clauses = 
  let rec aux liste e =
    match liste with
    [] -> true 
    | f::reste -> if -e=f then false else aux reste e 
  in match list_props clauses [] with
  | [] -> 0
  | g::reste -> if (aux reste g) then g else pur_pas_bon (enleve_p_et_non_p g reste []) 
*)

let rec contient_neg x l =
  match l with
  | [] -> false
  | e::reste -> if -x=e then true
      else contient_neg x reste

let rec pur clauses = 
  let rec aux liste =
    match liste with
    [] -> raise (Failure "pas de littéral pur")
    | e::reste -> if not(contient_neg e reste) then e else aux (enleve_p_et_non_p e reste []) 
  in aux (list_props clauses [])


(*  enlever le p et le -p a chauqe p qu'on pracourt*)
 (*[1,2,3,-1,1,2]
   [1,2,3,2,1,2]
   aux (mnegation f (enleve_p f reste []) []) e 
   *)    
         


(*let rec puur clauses =
    (* prendre une clause c dans la liste des clauses
    le comparer aux autres clauses de la liste
    si on ne trouve pas de -c, c la proposition c est pur.*)
    match clauses with
    | [] -> false
    | e :: c ->
        match e with
        | [] -> pur c
        | f :: c' -> if cherche_pur f c then f
        else pur c'@c*)



(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (* à compléter *)
  if clauses = [] then Some interpretation else
  if mem [] clauses then None else
  (*try unitaire clauses with
  try pur clauses with*)
  (*comment choisir p ?*)
  (*let p = hd (hd clauses) in *)
  (*solveur_dpll_rec(simplifie p clauses) || solveur_dpll_rec(simplifie -p clauses)*)
  None

(* tests *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
