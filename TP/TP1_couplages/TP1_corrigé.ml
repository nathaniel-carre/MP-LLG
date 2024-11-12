(* On utilise une référence correspondant à un indice. Tant que
l'élément courant n'est pas égal à x, on incrémente la référence.
Si on a atteint la fin du tableau, on renvoie None, sinon on a 
trouvé la première occurrence de x. *)
let premiere_occ tab x =
    let n = Array.length tab and i = ref 0 in
    while !i < n && tab.(!i) <> x do
        incr i
    done;
    if !i < n then Some !i else None;;

assert (premiere_occ [|0; 1; 2; 3; 4; 5; 6|] 4 = Some 4);;

(* Lorsque la liste n'est pas vide, on peut renvoyer None si l'élément
de tête est plus grand que y. Sinon, on lance un appel récursif sur la 
queue de la liste, et on rajoute éventuellement l'élément de tête. On fait
attention ici à la syntaxe lorsqu'on enchaîne les filtrages. *)
let rec liste_inf lst x y = match lst with
    | [] -> Some []
    | z :: q -> 
        if z > y then None
        else begin match liste_inf q x y with
            | None -> None
            | Some res ->
                if z > x then Some res
                else Some (z :: res)
        end;;

let lst = [6; 7; 9; 10; 2; 2; 4; 6; 18; 20];;

assert (liste_inf lst 8 25 = Some [6; 7; 2; 2; 4; 6]);;
assert (liste_inf lst 8 18 = None);;

(* Le chemin du fichier est à modifier éventuellement. *)
#use "utilitaire.ml";;

(* Certains calculs peuvent être un peu longs (quelques secondes sur ma machine, 
   mais peut-être plus sur un autre ordinateur). N'hésitez pas à commenter les
   tests sur les gros graphes pour gagner du temps. *)

let c1 = [|-1; 8; 9; -1; 6; 10; 4; -1; 1; 2; 5; -1|];;

(* On parcourt chaque sommet de X et on compte le nombre de sommets liés. À noter,
   on aurait pu faire le calcul sans utiliser g. *)
let cardinal_couplage g c =
    let nc = ref 0 in
    for x = 0 to g.nx - 1 do
        if c.(x) <> -1 then incr nc
    done;
    !nc;;

assert (cardinal_couplage g1 c1 = 4);;

(* On applique la définition du cours. On commence par créer un graphe de la bonne
taille, puis on parcourt les sommets de X, on crée les arêtes de s vers les sommets
libres de x. Puis, pour chaque voisin y d'un sommet x, on crée l'arête (y, x) ou
(x, y) selon que l'arête {x, y} soit dans le couplage ou non. On termine en parcourant
Y pour créer des arêtes des sommets libres vers t. *)
let graphe_augmentation g c =
    let n = g.nx + g.ny in
    let gc = Array.make (n + 2) [] in
    for x = 0 to g.nx - 1 do
        if c.(x) = -1 then gc.(n) <- x :: gc.(n);
        let traiter_voisin y =
            if c.(x) = y then gc.(y) <- x :: gc.(y)
            else gc.(x) <- y :: gc.(x)
        in
        List.iter traiter_voisin g.adj.(x)
    done;
    for y = g.nx to n - 1 do
        if c.(y) = -1 then gc.(y) <- n + 1 :: gc.(y)
    done;
    gc

(* C'est un algorithme de parcours de graphe. On utilise ici le tableau arbo
en cours de construction pour savoir si un sommet a déjà été vu ou non. La fonction
dfs prend en argument un prédécesseur de s et un sommet s et, si le sommet s n'a
pas été vu (donc si arbo.(s) vaut -2), marque son prédécesseur et relance un parcours
sur ses voisins. *)    
let arborescence gc s =
    let n = Array.length gc in
    let arbo = Array.make n (-2) in
    let rec dfs pred s = 
        if arbo.(s) = -2 then begin
            arbo.(s) <- pred;
            List.iter (dfs s) gc.(s)
        end
    in
    dfs (-1) s;
    arbo;;

(* On commence par calculer l'arborescence. Si le sommet t est accessible depuis s,
on reconstruit le chemin par la fin, en gardant en mémoire le sommet courant, et en
passant à son parent dans l'arborescence à chaque étape. *)    
let chemin gc s t =
    let arbo = arborescence gc s in
    if arbo.(t) = -2 then None
    else begin
        let sigma = ref [] and courant = ref arbo.(t) in
        while !courant <> s do
            sigma := !courant :: !sigma;
            courant := arbo.(!courant)
        done;
        Some (List.rev !sigma)
    end;;

(* Aucune difficulté ici : un chemin augmentant dans G correspond exactement aux 
sommets intermédiaires d'un chemin de s à t dans Gc. *)    
let chemin_augmentant g c =
    let gc = graphe_augmentation g c in
    let n = g.nx + g.ny in
    chemin gc n (n + 1)    

(* On parcourt les sommets deux par deux. Comme le chemin augmentant
   commence par une arête hors du couplage, chaque paire {x, y} 
   parcourue dans le code ci-dessus forme une arête hors du couplage.
   On modifie le couplage en y mettant cette arête et on continue.
   Notons que même si on a l'impression de ne faire que l'ajout des
   nouvelles arêtes, il n'est pas nécessaire « d'enlever » les arêtes
   qui sortent de CΔσ, car chacun des sommets concernés se voit déjà
   attribuer un autre voisin par C. *)
let rec augmenter c = function
    | []          -> ()
    | [_]         -> failwith "Problème de taille"
    | x :: y :: q -> c.(x) <- y; c.(y) <- x;
                     augmenter c q;;

(* On applique l'algorithme général du cours : on part d'un couplage
   vide et tant qu'il existe un chemin augmentant, on augmente le 
   couplage. *)
let couplage_maximum g =
    let c = Array.make (g.nx + g.ny) (-1) in
    let fini = ref false in
    while not !fini do
        match chemin_augmentant g c with
            | None       -> fini := true
            | Some sigma -> augmenter c sigma
    done;
    c;;

(* Quelques tests. *)
let c1 = couplage_maximum g1;; cardinal_couplage g1 c1;;
let c2 = couplage_maximum g2;; cardinal_couplage g2 c2;;
let c3 = couplage_maximum g3;; cardinal_couplage g3 c3;;

(* On utilise le tableau ordre_bfs en guise de file. L'idée est
   que l'indice debut indique l'indice du prochain élément à 
   sortir de la file, et que l'indice fin indique la case dans le
   tableau de la prochaine place libre dans la file. Comme chaque
   sommet ne passe qu'au plus une fois par la file (via un marquage
   précoce), cela ne créera pas d'indice hors des bornes. Le principe
   est alors le suivant : on commence par ajouter à la file tous les 
   sommets libres de X. Ensuite, tant que la file est non vide, on
   défile un sommet s, puis on essaie d'enfiler certains de ses voisins
   (de toute façon, ceux qui n'ont pas déjà été vus) :
    - si s ∈ X, on ne considère que les voisins qui ne sont pas couplés
    à s ;
    - sinon, on ne considère que le voisin couplé à s.
   Cela garantit que les chemins explorés sont des chemins alternants. *)
let bfs_alternant g c =
    let n = g.nx + g.ny in
    let dist = Array.make n (-1) in
    let ordre_bfs = Array.make n (-1) in
    let debut = ref 0 and fin = ref 0 in
    for x = 0 to g.nx - 1 do
        if c.(x) = -1 then begin
            ordre_bfs.(!fin) <- x;
            incr fin;
            dist.(x) <- 0;
        end
    done;
    while !debut < !fin do
        let s = ordre_bfs.(!debut) in
        incr debut;
        let traiter t =
            if dist.(t) = -1 then
                if (s < g.nx && c.(s) <> t) || (s >= g.nx && c.(s) = t) then begin
                    dist.(t) <- dist.(s) + 1;
                    ordre_bfs.(!fin) <- t;
                    incr fin
                end in
        List.iter traiter g.adj.(s)
    done;
    ordre_bfs, dist;;

(* C'est exactement le même principe que la fonction chemin_alternant. Les
   différences principales sont :
    - on part ici d'un sommet de Y (et pas de X) ;
    - on ne continue un chemin que par un sommet de distance inférieure. *)
let rec dfs_alternant g c dist vus y =
    if not vus.(y) then begin
        vus.(y) <- true;
        let rec traiter = function
           | []     -> None
           | x :: q -> if c.(x) = -1 then Some [y; x]
                       else if c.(x) = y || dist.(x) <> dist.(y) - 1 then traiter q
                       else begin
                           match dfs_alternant g c dist vus c.(x) with
                               | None       -> traiter q
                               | Some sigma -> Some (y :: x :: sigma)
                       end in
       traiter g.adj.(y)
    end else None;;

(* C'est le même principe que la fonction couplage_maximum, sauf qu'on
   parcourt les sommets de Y par ordre croissant de distance. Dès qu'on
   trouve un chemin augmentant, on note sa taille. Dès que la distance
   des sommets est supérieure à cette taille, on arrête de rajouter des
   chemins augmentants et on recommence à passer dans la boucle while
   externe. *)
let hopcroft_karp g =
    let n = g.nx + g.ny in
    let c = Array.make n (-1) in
    let fini = ref false in
    while not !fini do
        fini := true;
        let vus = Array.make n false in
        let ordre_bfs, dist = bfs_alternant g c in
        let taille_min = ref n in
        let i = ref 0 in
        while !i < n do
            let s = ordre_bfs.(!i) in
            if s = -1 || dist.(s) > !taille_min then i := n
            else if s >= g.nx && c.(s) = -1 then begin
               match dfs_alternant g c dist vus s with
                  | None       -> ()
                  | Some sigma -> taille_min := dist.(s);
                                  fini := false;
                                  augmenter c sigma
            end;
            incr i
        done
    done;
    c;;

(* Quelques tests. *)
let c1' = hopcroft_karp g1;; cardinal_couplage g1 c1';;
let c2' = hopcroft_karp g2;; cardinal_couplage g2 c2';;
let c3' = hopcroft_karp g3;; cardinal_couplage g3 c3';;

(* On compare les temps de calcul. On trouve (sur ma machine) :
    - 1,7 secondes pour couplage_maximum ;
    - 0,05 secondes pour hopcroft_karp. *)
chronometre couplage_maximum g3;;
chronometre hopcroft_karp g3;;