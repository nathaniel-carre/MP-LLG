(* Un graphe biparti G = (X U Y, A) contient un champ nx
correspondant à |X|, un champ ny correspondant à |Y| et un
champ adj correspondant au tableau de listes d'adjacence de G *)
type graphe = {nx : int; ny : int; adj : int list array};;

(* Renvoie sous forme de liste un échantillon de taille
k parmi les éléments d'un tableau tab. *)
let echantillon tab k =
    let n = Array.length tab in
    assert (n >= k);
    let lst = ref [] in
    for i = 0 to k - 1 do
        let j = Random.int (n - i) in
        lst := tab.(j) :: !lst;
        tab.(j) <- tab.(n - i - 1);
        tab.(n - i -1) <- List.hd !lst
    done;
    !lst;;

(* Crée un graphe biparti G = (X U Y, A) pseudo-aléatoire,
tel que |X| = nx, |Y| = ny et tous les sommets de X sont de
degré ≤ deg_max. La graine permet l'initialisation des
valeurs pseudo-aléatoires. *)
let creer_graphe nx ny deg_max graine =
    Random.init graine;
    let adj = Array.make (nx + ny) [] in
    (* tab_Y est un tableau contenant les sommets de Y *)
    let tab_Y = Array.init ny (fun i -> i + nx) in
    for x = 0 to nx - 1 do
        let degx = Random.int (deg_max + 1) in
        let ajout_arete y = 
            adj.(x) <- y :: adj.(x);
            adj.(y) <- x :: adj.(y) in
        List.iter ajout_arete (echantillon tab_Y degx)
    done;
    {nx; ny; adj};;

(* Renvoie le temps écoulé, en secondes, pour faire un
calcul de la fonction f avec l'argument x. *)
let chronometre f x =
    let debut = Sys.time() in
    ignore (f x);
    Sys.time() -. debut;;

let g1 = creer_graphe 6 6 3 384;;
let g2 = creer_graphe 100 100 5 42;;
let g3 = creer_graphe 10000 10000 10 42;;