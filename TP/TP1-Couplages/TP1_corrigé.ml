(* Le chemin du fichier est à modifier éventuellement. *)
#use "utilitaire.ml";;

(* Certains calculs peuvent être un peu longs (quelques secondes sur ma machine, 
   mais peut-être plus sur un autre ordinateur). N'hésitez pas à commenter les
   tests sur les gros graphes pour gagner du temps. *)

(* On parcourt chaque sommet de X et on compte le nombre de sommets liés. À noter,
   on aurait pu faire le calcul sans utiliser g. *)
let cardinal_couplage g c =
    let nc = ref 0 in
    for x = 0 to g.nx - 1 do
        if c.(x) <> -1 then incr nc
    done;
    !nc;;

(* Le principe est le suivant : si x a déjà été vu, on renvoie None ; sinon, 
   on parcourt ses voisins y. On distingue :
    - si y est libre, le chemin (x, y) convient ;
    - si y est lié à x, on ne peut pas continuer le chemin en passant par y ;
    - sinon, c'est que y est couplé à un sommet z = c.(y), et on essaie de
    continuer le chemin depuis z. S'il existe un tel chemin σ, on renvoie 
    le chemin (x, y) @ σ.
   Si on n'a pas trouvé de chemin satisfaisant en passant par y, on 
   continue d'explorer les voisins de x. *)
let rec chemin_alternant g c vus x =
    if not vus.(x) then begin
       vus.(x) <- true;
       (* La fonction traiter : int list -> int list option s'occupe de 
          parcourir une liste d'adjacence et de construire l'option de
          chemin voulue. *)
       let rec traiter = function
           | []     -> None
           | y :: q -> if c.(y) = -1 then (vus.(y) <- true; Some [x; y])
                       else if vus.(y) || c.(y) = x then traiter q
                       else begin
                           vus.(y) <- true;
                           match chemin_alternant g c vus c.(y) with
                               | None       -> traiter q
                               | Some sigma -> Some (x :: y :: sigma)
                       end in
       traiter g.adj.(x)
    end else None;;

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
   couplage. Pour avoir la bonne condition d'arrêt, en rentrant 
   dans la boucle, on suppose que c'est la dernière itération (donc
   on fixe fini à true), et on ne modifie ce booléen que si on 
   trouve un chemin augmentant. La deuxième boucle while a pour
   objectif de parcourir tous les sommets de X et de lancer une
   recherche de chemin augmentant depuis ceux qui sont libres. *)
let couplage_maximum g =
    let c = Array.make (g.nx + g.ny) (-1) in
    let fini = ref false in
    while not !fini do
        fini := true;
        let vus = Array.make (g.nx + g.ny) false in        
        let x = ref 0 in
        while !x < g.nx && !fini do
            if c.(!x) = -1 then (match chemin_alternant g c vus !x with
                | None       -> ()
                | Some sigma -> augmenter c sigma; fini := false);
            incr x
        done
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

(* Même idée que pour le cardinal du couplage, sauf qu'on ajoute ici
   le poids. Attention aux opérations sur les flottants. *)
let poids_couplage g m c =
    let poids = ref 0.0 in
    for x = 0 to g.nx - 1 do
        if c.(x) <> -1 then
           poids := !poids +. m.(x).(c.(x))
    done;
    !poids;;

(* L'algorithme de Floyd-Warshall est un algorithme de programmation
   dynamique permettant de trouver toutes les distances dans un graphe
   entre deux sommets quelconques. On a en argument un graphe pondéré
   représenté par matrice d'adjacence. Il consiste à calculer une suite
   de matrices (M_k), k = 0, 1, …, n, telle que pour (s, t) ∈ S², on ait :
    « M_k[s][t] est la longueur minimale d'un chemin de s à t dont les
      sommets intermédiaires sont strictement inférieurs à k. »
   Pour calculer M_{k+1}[s][t], on remarque qu'un chemin de longueur
   minimale de s à t ne passant que par des sommets intermédiaires 
   strictement inférieurs à k + 1 est de l'une des deux formes suivantes :
    - ce chemin ne passe en fait jamais par un sommet intermédiaire k, donc
    il est de longueur M_k[s][t] ;
    - ce chemin passe une fois par un sommet intermédiaire k, auquel cas, il
    est la concaténation d'un chemin de s à k dont les sommets intermédiaires
    sont < k et d'un chemin de k à t dont les sommets intermédiaires sont < k.
    Sa longueur est donc M_k[s][k] + M_k[k][t].
   Finalement, la formule de récurrence est :
        M_{k+1}[s][t] = min(M_k[s][t], M_k[s][k] + M_k[k][t])
   L'initialisation se fait avec M_0 = M (la matrice d'adjacence du graphe).
   Pour remplir la matrice de prédécesseur, on initialise en mettant s comme
   prédécesseur de t pour chaque arête {s, t}. Ensuite, on modifie le prédécesseur
   chaque fois qu'on remarque que c'est plus court de passer par un sommet
   intermédiaire k. *)
let floyd_warshall m =
    let n = Array.length m in
    let pred = Array.make_matrix n n (-1) in
    for s = 0 to n - 1 do
        for t = 0 to n - 1 do
            if m.(s).(t) <> infinity then
               pred.(s).(t) <- s
        done
    done;
    for k = 0 to n - 1 do
        for s = 0 to n - 1 do
            for t = 0 to n - 1 do
                let poids = m.(s).(k) +. m.(k).(t) in
                if poids < m.(s).(t) then begin
                   m.(s).(t) <- poids;
                   pred.(s).(t) <- pred.(k).(t)
                end
            done
        done
    done;
    pred;;

(* En utilisant la matrice de prédécesseur, on peut partir de la
   fin et construire le chemin en prenant à chaque étape le 
   prédécesseur du dernier sommet. On s'arrête quand on atteint le
   sommet initial. *)
let plus_court_chemin m s t =
    let pred = floyd_warshall m in
    if pred.(s).(t) = -1 then None
    else begin
        let sigma = ref [] and u = ref pred.(s).(t) in
        while !u <> s do
            sigma := !u :: !sigma;
            u := pred.(s).(!u)
        done;
        Some !sigma
    end;;

(* On choisit de poser s = n et t = n + 1, où n = |S|. Le reste
   consiste à suivre la description de la construction. *)
let construire_GC g m c =
    let n = g.nx + g.ny in
    let gc = Array.make_matrix (n + 2) (n + 2) infinity in
    let s = n and t = n + 1 in
    for x = 0 to g.nx - 1 do
        if c.(x) = -1 then gc.(s).(x) <- 0.0;
        gc.(x).(x) <- 0.0;
        for y = g.nx to n - 1 do
            if c.(y) = -1 then gc.(y).(t) <- 0.0;
            if c.(x) <> y then gc.(x).(y) <- m.(x).(y)
                          else gc.(y).(x) <- -. m.(x).(y)
        done
    done;
    gc;;

(* Un peu la même idée que pour couplage_maximum, sauf qu'on
   cherche le chemin augmentant à l'aide des fonctions 
   précédentes. *)
let couplage_maximum_poids_minimum g m =
    let n = g.nx + g.ny in
    let c = Array.make n (-1) in
    let fini = ref false in
    while not !fini do
        let gc = construire_GC g m c in
        match plus_court_chemin gc n (n + 1) with
            | None       -> fini := true
            | Some sigma -> augmenter c sigma
    done;
    c;;

(* On vérifie que les couplages sont de la bonne taille et ont
   les bons poids. Il est déraisonnable d'essayer de lancer
   cette fonction sur g3. *)
let c1pm = couplage_maximum_poids_minimum g1 m1;;
let c2pm = couplage_maximum_poids_minimum g2 m2;;

poids_couplage g1 m1 c1pm;;
poids_couplage g2 m2 c2pm;;
cardinal_couplage g1 c1pm;;
cardinal_couplage g2 c2pm;;