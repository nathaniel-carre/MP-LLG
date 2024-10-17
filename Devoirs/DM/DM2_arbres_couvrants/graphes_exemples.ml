let gen_poids poids_max nb_aretes =
    Array.init nb_aretes (fun i -> 1 + Random.int poids_max);;

let voisins g s t =
    List.exists (fun (u, _) -> u = t) g.(s);;
    
let graphe_pond_alea poids_max n nb_aretes =
    Random.init 42;
    let g = Array.make n [] in
    let restant = Array.init n (fun i -> i) in
    let tab = gen_poids poids_max nb_aretes in
    for i = 1 to n - 1 do    
        let b = ref true in
        while !b do
            let num_s = Random.int i in
            let num_t = i + Random.int (n - i) in
            let s = restant.(num_s) and t = restant.(num_t) in
            let poids = tab.(i - 1) in
            if List.length g.(s) < 10 && List.length g.(t) < 10 then
               (g.(s) <- (t, poids) :: g.(s);
                g.(t) <- (s, poids) :: g.(t);
                restant.(num_t) <- restant.(i);
                restant.(i) <- t;
                b := false)
        done
    done;
    let nb = ref (n - 1) in
    while !nb < nb_aretes do
        let s = Random.int n and t = Random.int n in
        if s <> t && not (voisins g s t) then begin
           let poids = tab.(!nb) in
           if List.length g.(s) < 10 && List.length g.(t) < 10 then
              (g.(s) <- (t, poids) :: g.(s);
              g.(t) <- (s, poids) :: g.(t);
              incr nb)
        end
    done;
    g;;

let g1 = graphe_pond_alea 20 10 15;;
let g2 = graphe_pond_alea 50 1000 1500;;
let g3 = graphe_pond_alea 100 50000 75000;;