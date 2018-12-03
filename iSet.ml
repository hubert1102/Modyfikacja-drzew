(* Autor rozwiązania: Hubert Budzyński *)
(* Recenzent: Kajetan Husiatyński *)

(* Przechowuję dla każdego poddrzewa dane w takiej kolejności: *)
(* lewe poddrzewo, przedział w wierzchołku, prawe poddrzewo, wysokość poddrzewa, ilość liczb naturalnych w całym poddrzewie *)
type t = 
  | Empty
  | Node of t * (int * int) * t * int * int
;;

(* card t  - ilość elementow w poddrzewie t *)
let card = function
    | Empty -> 0
    | Node (_, _, _, _, x) -> x
;;
(* wysokość drzewa t *)
let height = function 
    |Empty -> 0;
    |Node(_, _, _, h, _) -> h
;;

let empty = Empty;;

let is_empty = function
 |Empty -> true
 |_ -> false
;;

(* bezpieczne dodawanie aby nie przekroczyć max_int *)
let sum a b =
    if a + b < 0 then max_int else a+b;;
;;
(* analogicznie bezpieczne odejmowanie *)
let diff a b =
    if b < 0 then sum a (-b)
    else if a < min_int + b then min_int
    else a - b
;;

(* size (a, b) - ilość elementow w przedziale [a, b] *)
let size (a, b) = b - a + 1;;

(* make l [a, b] r - tworzy drzewo, gdzie w korzeniu jest przedzial [a, b], a l i r to odpowiednio lewe i prawe poddrzewa *)
(* budujemy tylko drzewa zbalansowane, gdzie l i r są podobnej wielkości, stąd stworzone drzewo jest zbalansowane *)
let make l (k: int*int) r = Node (l, k, r, max (height l) (height r) + 1, sum (sum (card l)  (card r))  (size k))
;;
(* bal l [a, b] r - balansuje drzewo o korzeniu [a, b], gdzie l, r to odpowiednio lewe i prawe poddrzewo *)
let rec bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _, _) ->
        if height ll >= height lr then make ll lk (bal lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _, _) ->
              make (make ll lk lrl) lrk (bal lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _, _) ->
        if height rr >= height rl then make (bal l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _, _) ->
              make (bal l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else make l k r
;;

(* mem n s - czy drzewo s zawiera element s *)
let mem n s =
  let rec loop = function
    | Node (l, (x, y), r, _, _) ->
        if n >= x && n <= y
            then true
            else if x > n
                then loop l
                else loop r
    | Empty -> false 
    in
    loop s
;;

(* iter f s - zgodnie z iSet.mli *)
let iter f s =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _, _) -> loop l; f k; loop r 
  in
  loop s
;;
(* fold f s acc - zgodnie z iSet.mli *)
let fold f s acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _, _) ->
          loop (f k (loop acc l)) r 
  in
  loop acc s
;;
(* elements s - zgodnie z iSet.mli *)
let elements s = 
  let rec loop acc = function
      Empty -> acc
    | Node(l, k, r, _, _) -> loop (k :: loop acc r) l 
  in
  loop [] s
;;
(* below x s - zwraca ilość elementow niewiekszych ok x w s *)
let rec below x = function
    |Empty -> 0
    |Node(l, (v1, v2), r, h, c) ->
        if v1 <= x && x <= v2 then sum (sum (diff x v1) (card l)) 1
        else if x < v1 then below x l
        else sum  (sum (sum (card l)  (diff v2  v1)) 1) (below x r)
;;
exception Empty_set;; (* delete_min i delete_max uruchamiane są tylko dla niepustego drzewa, exception na wszelki wypdaek *)

(* delete_min s - zwraca parę (t, (a, b)) gdzie t to zbalansowane drzewo s po usunięciu elementu najmniejszego, a para (a, b) to element najmniejszy *)
let rec delete_min = function
    |Empty -> raise Empty_set
    |Node(Empty, k, r, _, _) -> (r, k)
    |Node(l, k, r, _, _) -> let (x, y) = delete_min l in (bal x k r, y)
;;
(* analogicznie do delete_min *)
let rec delete_max = function
    |Empty -> raise Empty_set
    |Node (l, k, Empty, _, _) -> (l, k)
    |Node (l, k, r, _, _) -> let (x, y) = delete_max r in (bal l k x, y)
;;
(* łączy i balansuje dw drzewa s1 i s2, gdzie największy element s1 jest mniejszy o co najmniej 2 od najmniejszego elementu z s2 *)
let merge s1 s2 = match s1, s2 with
    |Empty, s2 -> s2
    |s1, Empty -> s1
    | _, _ -> let (t, k) = delete_min s2 in 
    bal s1 k t
;;

(* mniejsze x s - zwraca zbalansowane poddrzewo t, ktore zawiera wszystkie elementy s mniejsze od x *)
let rec mniejsze x = function 
    |Empty -> Empty
    |Node(l, (v1, v2), r, _, _) ->
        if v1 <= x && x <= v2 then 
            if v1 = x then l
            else bal l (v1, x-1) Empty
        else if x < v1 then mniejsze x l
            else bal l (v1, v2) (mniejsze x r)
;;
(* analogicznie do mniejsze *)
let rec wieksze x = function 
    |Empty -> Empty
    |Node(l, (v1, v2), r, _, _) ->
        if v1 <= x && x <= v2 then 
            if v2 = x then r
            else bal Empty (x+1, v2) r
        else if x > v2 then wieksze x r
            else bal (wieksze x l) (v1, v2) r
;;

(* split x s - daje parę (l, b, r) , gdzie l to drzewo elementow mniejszych od b w drzewie s, r drzewo większych, *) 
(* a b przyjmuje true jak x jest w s i false w przeciwnym wypadku *)
let split x s = ((mniejsze x s), (mem x s), (wieksze x s));;

(* zwraca drzewo utworzone po dodaniu przedziału (v1, v2) do drzewa s, drzewo wynikowe jest zbalansowane *)
(* uważamy na to, aby scalić przedziały w postaci [a,..., x] , [x+1, ..., b] w [a, ... , b] *)
let add (v1, v2) s =
    let (l1, _, r1) = split v1 s in let (_, _, r2) = split v2 r1 in
    let (l, (x, _)) =
        if mem (v1 - 1) l1 then delete_max l1
        else (l1, (v1, v2)) in
    let (r, (_, y)) = 
        if mem (v2 + 1) r2 then delete_min r2
        else (r2, (v1, v2)) in
	    bal l (x,y) r
;;
(* zwraca drzewo po usunięciu przedziału (v1, v2) z drzewa s *)
let remove (v1, v2) s = merge (mniejsze v1 s) (wieksze v2 s);;
    
