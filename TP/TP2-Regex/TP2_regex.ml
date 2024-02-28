type 'a regex = 
     | Vide
     | Epsilon
     | Lettre of 'a
     | Concat of 'a regex * 'a regex
     | Union of 'a regex * 'a regex
     | Etoile of 'a regex;;

let parse s =
  let open Printf in
  let n = String.length s in
  let i = ref 0 in
  let rec peek () =
    if !i >= n then None else match s.[!i] with
    | ' ' -> incr i; peek ()
    | c   -> Some c in
  let eat x =
    match peek () with
    | Some y when y = x -> incr i;
    | Some y -> failwith (sprintf "expected %c, got %c" x y)
    | None -> failwith "incomplete" in
  let rec regex () =
    let t = term () in
    match peek () with
    | Some '|' -> eat '|'; Union (t, regex ())
    | _ -> t
  and term () =
    let f = factor () in
    match peek () with
    | None | Some ')' | Some '|' -> f
    | _ -> Concat (f, term ())
 and factor () =
    let rec aux acc =
      match peek () with
      | Some '*' -> eat '*'; aux (Etoile acc)
      | _ -> acc in
    aux (base ())
  and base () =
    match peek () with
    | Some '(' -> eat '('; let r = regex () in eat ')'; r
    | Some '&' -> eat '&'; Epsilon
    | Some '#' -> eat '#'; Vide
    | Some (')' | '|' | '*' as c) -> failwith (sprintf "unexpected '%c'" c)
    | Some c -> eat c; Lettre c
    | None -> failwith "unexpected end of string" in
  let r = regex () in
  if !i = n then r else failwith "trailing ')' ?";;

let e0 = parse "(a|ba*)*|ab*a";;

let e1 = parse "a(a|b)*b";;

(* Les cas de bases sont déjà normalisés. Pour les cas inductif, on distingue :
    - L(#·e) = L(e·#) = L(#)
    - L(#|e) = L(e|#) = L(e)
    - L( #* ) = L(ε) *)

let rec normaliser = function
    | Concat (e, f) -> 
        let en = normaliser e and fn = normaliser f in
        if en = Vide || fn = Vide then Vide
        else Concat (en, fn)
    | Union (e, f)  -> 
        let en = normaliser e and fn = normaliser f in
        if en = Vide then fn
        else if fn = Vide then en
        else Union (en, fn)
    | Etoile e -> 
        let en = normaliser e in
        if en = Vide then Epsilon
        else Etoile en
    | e -> e;;

(* On teste juste si l'expression normalisée est vide. *)

let est_vide e = normaliser e = Vide;;

(* On parcourt récursivement l'expression, et on ajoute 1 pour chaque
   constructeur Lettre. *)

let rec nombre_lettres = function
    | Vide | Epsilon             -> 0
    | Lettre _                   -> 1
    | Union(e, f) | Concat(e, f) -> nombre_lettres e + nombre_lettres f
    | Etoile e                   -> nombre_lettres e;;

(* On commence par créer le tableau de correspondance, dont la taille est
   le nombre de lettres. Ensuite, on parcourt l'expression régulière, et chaque
   fois qu'on trouve une lettre, on crée son association dans le tableau (avec la
   référence i qu'on incrémente), puis on crée la nouvelle expression, avec la
   bonne numérotation. *)

let lineariser e =
    let k = nombre_lettres e in
    let t = Array.make k 'a' in
    let i = ref 0 in
    let rec aux_lin = function
        | Vide          -> Vide
        | Epsilon       -> Epsilon
        | Lettre a      -> t.(!i) <- a; incr i; Lettre (!i - 1)
        | Union (e, f)  -> Union (aux_lin e, aux_lin f)
        | Concat (e, f) -> Concat (aux_lin e, aux_lin f)
        | Etoile e      -> Etoile (aux_lin e) in
    aux_lin e, t;;

(* On utilise les règles inductives vues en cours. *)

let rec mot_vide = function
    | Vide | Lettre _    -> false
    | Epsilon | Etoile _ -> true
    | Union (e, f)       -> mot_vide e || mot_vide f
    | Concat (e, f)      -> mot_vide e && mot_vide f;;

(* On crée un nouveau tableau, et on crée l'union par un OU logique case
   par case. *)

let union t1 t2 =
    let n = Array.length t1 in
    assert (n = Array.length t2);
    let t = Array.make n false in
    for i = 0 to n - 1 do
        t.(i) <- t1.(i) || t2.(i)
    done;
    t;;

(* À nouveau, on suit les règles inductives du cours. Il faut faire
   attention au cas de la concaténation, toujours un peu particulier. *)

let rec prefixes n = function
    | Vide | Epsilon -> Array.make n false
    | Lettre i       -> 
        let t = Array.make n false in
        t.(i) <- true; t
    | Union(e, f)    -> union (prefixes n e) (prefixes n f)
    | Concat(e, f)   -> 
        let t1 = prefixes n e in
        if mot_vide e then union t1 (prefixes n f)
                      else t1
    | Etoile e       -> prefixes n e;;

let rec suffixes n = function
    | Vide | Epsilon -> Array.make n false
    | Lettre i       -> 
        let t = Array.make n false in
        t.(i) <- true; t
    | Union(e, f)    -> union (suffixes n e) (suffixes n f)
    | Concat(e, f)   -> 
        let t2 = suffixes n f in
        if mot_vide f then union (suffixes n e) t2
                      else t2
    | Etoile e       -> suffixes n e;;

(* On écrit une fonction qui fait l'union de deux matrices de booléens, sur le même
   principe que précédemment. *)

let union_matrice m1 m2 =
    let n = Array.length m1 in
    let m = Array.make_matrix n n false in
    for i = 0 to n - 1 do
        m.(i) <- union m1.(i) m2.(i)
    done;
    m;;

(* Dès lors, on suit à nouveau le principe inductif. On fait attention à l'étoile
   et la concaténation. *)

let rec facteurs n = function
    | Vide | Epsilon | Lettre _ -> Array.make_matrix n n false
    | Union (e, f) -> union_matrice (facteurs n e) (facteurs n f)
    | Concat (e, f) -> 
        let m = union_matrice (facteurs n e) (facteurs n f) in
        let suff = suffixes n e and pref = prefixes n f in
        for i = 0 to n - 1 do
            for j = 0 to n - 1 do
                m.(i).(j) <- m.(i).(j) || (suff.(i) && pref.(j))
            done
        done;
        m
    | Etoile e -> 
        let m = facteurs n e in
        let suff = suffixes n e and pref = prefixes n e in
        for i = 0 to n - 1 do
            for j = 0 to n - 1 do
                m.(i).(j) <- m.(i).(j) || (suff.(i) && pref.(j))
            done
        done;
        m;;

type 'a afnd = { finaux : bool array;
                 delta : ('a * int) list array };;

(* On suit l'algorithme du cours : on commence par linéariser l'expression, et
   on garde en mémoire le tableau d'association. On calcule V, P, S, F pour l'expression
   linéarisée, puis on crée l'automate avec un état de plus que le nombre de lettres. V
   permet de savoir si l'état initial est final, P permet d'écrire les transitions depuis
   l'état initial, S permet de savoir quels états sont finaux, et F donne les autres
   transitions. *)

let glushkov e =
    let elin, t = lineariser e in
    let n = Array.length t in
    let ve = mot_vide elin and
        pe = prefixes n elin and
        se = suffixes n elin and
        fe = facteurs n elin in
    let finaux = Array.make (n + 1) false and
        delta = Array.make (n + 1) [] in
    finaux.(0) <- ve;
    let transition q a q' = delta.(q) <- (a, q') :: delta.(q) in
    for q = 1 to n do
        if pe.(q - 1) then transition 0 t.(q - 1) q;
        finaux.(q) <- se.(q - 1);
        for q' = 1 to n do
            if fe.(q - 1).(q' - 1) then transition q t.(q' - 1) q'
        done
    done;
    {finaux = finaux; delta = delta};;

let g0 = glushkov e0;;

let g1 = glushkov e1;;

(* On crée le tableau des images, puis on parcourt chaque liste d'adjacence
   d'un état de X, et on ajoute un état dans Y chaque fois qu'on tombe sur
   une transition étiquetée par a. Le test tab_Y.(q') || a = b permet de ne
   pas supprimer des éléments de Y qu'on aurait déjà rajouté précédemment. *)

let delta_X aut tab_X a =
    let n = Array.length tab_X in
    let tab_Y = Array.make n false in
    for q = 0 to n - 1 do
        let traiter (b, q') = tab_Y.(q') <- tab_Y.(q') || a = b in
        if tab_X.(q) then List.iter traiter aut.delta.(q)
    done;
    tab_Y;;

(* On applique la définition de la fonction de transition étendue : on calcule
   l'image du tableau pour chaque nouvelle lettre. *)

let delta_etoile_X aut tab_X u =
    let tab_Y = ref tab_X in
    for i = 0 to String.length u - 1 do
        tab_Y := delta_ens aut !tab_Y u.[i]
    done;
    !tab_Y;;

(* On commence par créer un tableau correspondant à {0}, on calcule son image Y
   par le mot u, puis on vérifie s'il existe un état qui est à la fois dans Y et
   final. *)

let reconnu aut u =
    let n = Array.length aut.finaux in
    let tab_X = Array.make n false in
    tab_X.(0) <- true;
    let tab_Y' = delta_etoile aut tab_X u in
    let i = ref 0 in
    while !i < n && (not tab_Y'.(!i) || not aut.finaux.(!i)) do
        incr i
    done;
    !i < n;;

assert (reconnu g0 "ababaaaaaba");;
assert (reconnu g1 "abbbabaaab");;
assert (not (reconnu g1 "bbaaaabaaaa"));;

type 'a etat = { lettre : 'a option;
                 mutable sortie1 : 'a etat option;
                 mutable sortie2 : 'a etat option };;

type 'a afndn = { initial : 'a etat;
                  final : 'a etat};;

(* On suit les constructions dans le corrigé pdf. *)

let rec thompson = function
    | Vide -> 
        let initial = {lettre = None; sortie1 = None; sortie2 = None}
        and final = {lettre = None; sortie1 = None; sortie2 = None} in
        {initial; final}
    | Epsilon -> 
        let initial = {lettre = None; sortie1 = None; sortie2 = None}
        and final = {lettre = None; sortie1 = None; sortie2 = None} in
        initial.sortie1 <- Some final;
        {initial; final}
    | Lettre a -> 
        let initial = {lettre = Some a; sortie1 = None; sortie2 = None}
        and final = {lettre = None; sortie1 = None; sortie2 = None} in
        initial.sortie1 <- Some final;
        {initial; final}
    | Concat(e1, e2) -> 
        let t1 = thompson e1 and t2 = thompson e2 in
        t1.final.sortie1 <- Some t2.initial;
        {initial = t1.initial; final = t2.final}
    | Union(e1, e2) -> 
        let t1 = thompson e1 and t2 = thompson e2 in
        let initial = 
            {lettre = None; 
            sortie1 = Some t1.initial; 
            sortie2 = Some t2.initial}
        and final = {lettre = None; sortie1 = None; sortie2 = None} in
        t1.final.sortie1 <- Some final;
        t2.final.sortie1 <- Some final;
        {initial; final}
    | Etoile e -> 
        let th = thompson e in
        let final = {lettre = None; sortie1 = None; sortie2 = None} in
        let initial = 
            {lettre = None; 
            sortie1 = Some th.initial; 
            sortie2 = Some final} in
        th.final.sortie1 <- Some th.initial;
        th.final.sortie2 <- Some final;
        {initial; final};;

(* L'idée est la suivante : la fonction auxiliaire prend en argument un état et
   l'indice de la lettre en cours de lecture (n si on est à la fin du mot). On
   envisage les différents cas :
      - si pas de transitions sortante, on n'accepte que si l'état est l'état final
        de l'automate (on vérifie avec ==) et qu'on a lu l'intégralité du mot u ;
      - s'il y a une transition sortante étiquetée par une lettre, on doit alors 
        vérifier qu'il reste des lettres à lire, que la prochaine lettre à lire est
        celle de la transition, et qu'on accepte depuis l'état atteint, à partir de
        l'indice suivant ;
      - s'il y a une seule transition sortante étiquetée par ε, on vérifie qu'on
        accepte depuis l'état atteint ;
      - le cas un peu particulier est celui où il y a deux transitions sortantes, 
        étiquetées par ε. C'est dans ce cas qu'on fait du retour sur trace : on vérifie
        l'acceptation depuis le premier état atteint, et si ça ne marche pas, on vérifie
        depuis le deuxième état atteint. *)

let reconnu_thompson th u =
    let n = String.length u in
    let rec accepte q i = match q.lettre, q.sortie1, q.sortie2 with
        | None, None, None       -> q == th.final && i = n
        | Some a, Some p, None   -> i < n && u.[i] = a && accepte p (i + 1)
        | None, Some p, None     -> accepte p i
        | None, Some p1, Some p2 -> accepte p1 i || accepte p2 i
        | _ -> failwith "L'automate n'est pas normalisé" in
    accepte th.initial 0;;

let th0 = thompson e0;;

let th1 = thompson e1;;

assert (reconnu_thompson th0 "ababaaaaaba");;
assert (reconnu_thompson th1 "abbbabaaab");;
assert (not (reconnu_thompson th1 "bbaaaabaaaa"));;

(* On suit l'algorithme de réécriture décrite dans le pdf. *)

let rec reecriture = function
    | Vide          -> Vide
    | Lettre a      -> Lettre a
    | Epsilon       -> Union (Vide, Epsilon)
    | Concat (e, f) -> 
        begin match reecriture e, reecriture f with                          
            | Union (e', Epsilon), Union (f', Epsilon) -> 
                Union (Union (Union (Concat (e', f'), e'), f'), Epsilon)
            | Union (e', Epsilon), f'                  ->
                Union (Concat (e', f'), f')
            | e', Union (f', Epsilon)                  ->
                Union (Concat (e', f'), e')
            | e', f'                                   ->
                Concat (e', f') end
    | Union (e, f) -> 
        begin match reecriture e, reecriture f with
            | Union (e', Epsilon), Union (f', Epsilon)               
            | Union (e', Epsilon), f'          
            | e', Union (f', Epsilon)                  ->
                Union (Union (e', f'), Epsilon)
            | e', f'                                   ->
                Union (e', f') end
    | Etoile e -> 
        match reecriture e with
            | Union (e', Epsilon) | e' ->
                Union (Concat (e', Etoile e'), Epsilon);;

let thompson_bis e = thompson (reecriture e);;

let e2 = parse "a**";;

let th2 = thompson_bis e2;;

assert (reconnu_thompson th2 "aaa");;


















