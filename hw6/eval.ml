open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible

type stoval = 
    Computed of value 
  | Delayed of exp * env

 and stack =
   Hole_SK
   | Frame_SK of stack * frame

 and state =
   Anal_ST of (stoval Heap.heap) * stack * exp * env
   | Return_ST of (stoval Heap.heap) * stack * value 

 (* Define your own datatypes *)
 and env = NOT_IMPLEMENT_ENV
 and value = NOT_IMPLEMENT_VALUE
 and frame = NOT_IMPLEMENT_FRAME

(* Define your own empty environment *)
let emptyEnv = NOT_IMPLEMENT_ENV

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp _ = raise NotImplemented

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)

let rec findElement x l = match l with
    | [] -> false
    | v::next -> if v = x then true
            else findElement x next

let rec union l m = match m with
    | [] -> l
    | v::next -> if findElement v l then union l next
                else union (l @ [v]) next
            

let appendVar x l = if findElement x l then l 
                        else l @ [x]


let rec getFreeVar e l = match e with
    | Tml.Tvar v -> appendVar v l
    | Tml.Tlam (x, t, ex) -> List.filter (fun p -> p > x || p < x) (getFreeVar ex l)
    | Tml.Tapp (ex1, ex2) -> getFreeVar ex1 (getFreeVar ex2 l)
    | Tml.Tpair (ex1, ex2) -> getFreeVar ex1 (getFreeVar ex2 l)
    | Tml.Tfst ex -> getFreeVar ex l
    | Tml.Tsnd ex -> getFreeVar ex l
    | Tml.Tinl (ex, t) -> getFreeVar ex l
    | Tml.Tinr (ex, t) -> getFreeVar ex l
    | Tml.Tcase (ex, x1, ex1, x2, ex2)->union (union (List.filter (fun p -> p > x2 || p < x2) (getFreeVar ex2 l)) (List.filter (fun p -> p > x1 || p < x1) (getFreeVar ex1 l))) (getFreeVar ex l)
            (*getFreeVar ex (List.filter (fun p -> p > x1 || p < x1) (getFreeVar ex1 (List.filter (fun p -> p > x2 || p < x2) (getFreeVar ex2 l))))*)
    | Tml.Tfix (x, t, ex) -> List.filter (fun p-> p > x || p < x) (getFreeVar ex l)
    | Tml.Tifthenelse (ex, ex1, ex2) -> getFreeVar ex (getFreeVar ex1 (getFreeVar ex2 l))
    | _ -> l

let giveIndex l =
    let rec giveIndex' n l' r = match l' with
        | [] -> r
        | v::next -> giveIndex' (n+1) next (r @ [(v, n)])
    in giveIndex' 0 l []

let addIndex l= 
    let rec addIndex' l' r = match l' with
        | [] -> r
        | (v,n)::next -> addIndex' next (r @ [(v,n+1)])
    in addIndex' l []

let rec takeIndex x l = match l with 
    | [] -> 10
    | (v, n)::next -> if x = v then n
                    else takeIndex x next


let texp2exp e =
    let rec texp2exp' e' l = match e' with
        | Tml.Tvar v -> Tml.Ind (takeIndex v l)
        | Tml.Tlam (x, t, ex) -> Tml.Lam (texp2exp' ex ([(x, 0)] @ (addIndex l)))
        | Tml.Tapp (ex1, ex2) -> Tml.App (texp2exp' ex1 l, texp2exp' ex2 l)
        | Tml.Tpair (ex1, ex2) -> Tml.Pair (texp2exp' ex1 l, texp2exp' ex2 l)
        | Tml.Tfst ex -> Tml.Fst (texp2exp' ex l)
        | Tml.Tsnd ex -> Tml.Snd (texp2exp' ex l)
        | Tml.Teunit -> Tml.Eunit
        | Tml.Tinl (ex, t) -> Tml.Inl (texp2exp' ex (l))
        | Tml.Tinr (ex, t) -> Tml.Inr (texp2exp' ex (l))
        | Tml.Tcase (ex, x1, ex1, x2, ex2) -> Tml.Case (texp2exp' ex l, texp2exp' ex1 ([(x1, 0)] @ (addIndex l)), texp2exp' ex2 ([(x2 ,0)] @ (addIndex l)))
        | Tml.Tfix (x, t, ex) -> Tml.Fix (texp2exp' ex ([(x, 0)] @ (addIndex l)))
        | Tml.Ttrue -> Tml.True
        | Tml.Tfalse -> Tml.False
        | Tml.Tifthenelse (ex, ex1, ex2) -> Tml.Ifthenelse (texp2exp' ex l, texp2exp' ex1 l, texp2exp' ex2 l)
        | Tml.Tnum n -> Tml.Num n
        | Tml.Tplus -> Tml.Plus
        | Tml.Tminus -> Tml.Minus
        | Tml.Teq -> Tml.Eq
    in texp2exp' e (giveIndex (getFreeVar e []))


(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *) 
let rec shifting x n i = match n with
    | Tml.Ind m -> if m < i then Tml.Ind m
            else Tml.Ind(m+x)
    | Tml.Lam e -> Tml.Lam (shifting x e (i+1))
    | Tml.App (e1, e2) -> Tml.App (shifting x e1 i, shifting x e2 i)
    | Tml.Fst e' -> Tml.Fst (shifting x e' i)
    | Tml.Snd e' -> Tml.Snd (shifting x e' i)
    | Tml.Pair (e1, e2) -> Tml.Pair (shifting x e1 i, shifting x e2 i)
    | Tml.Eunit -> n
    | Tml.Inl e' -> Tml.Inl (shifting x e' i)
    | Tml.Inr e' -> Tml.Inr (shifting x e' i)
    | Tml.Case (e1, e2, e3) -> Tml.Case (shifting x e1 i, shifting x e2 (i+1) , shifting x e3 (i+1))
    | Tml.True -> n
    | Tml.False -> n
    | Tml.Ifthenelse (e1, e2, e3) -> Tml.Ifthenelse (shifting x e1 i, shifting x e2 i, shifting x e3 i)
    | Tml.Fix e' -> Tml.Fix (shifting x e' (i+1))
    | Tml.Num _ -> n
    | Tml.Plus -> n
    | Tml.Minus -> n
    | Tml.Eq -> n


let rec sub m n i = match m with
    | Tml.Ind m' -> if m' < i then Tml.Ind m' 
            else if m' > i then Tml.Ind (m'-1)
            else shifting i n 0
    | Tml.Lam e -> Tml.Lam (sub e n (i+1))
    | Tml.App (e1, e2) -> Tml.App (sub e1 n i, sub e2 n i)
    | Tml.Fst e' -> Tml.Fst (sub e' n i)
    | Tml.Snd e' -> Tml.Snd (sub e' n i)
    | Tml.Eunit -> m
    | Tml.Pair (e1, e2) -> Tml.Pair (sub e1 n i, sub e2 n i)
    | Tml.Inl e' -> Tml.Inl (sub e' n i)
    | Tml.Inr e' -> Tml.Inr (sub e' n i)
    | Tml.Case (e1, e2, e3) -> Tml.Case (sub e1 n i, sub e2 n (i+1), sub e3 n (i+1))
    | Tml.True -> m
    | Tml.False -> m
    | Tml.Ifthenelse (e1, e2, e3) -> Tml.Ifthenelse (sub e1 n i, sub e2 n i, sub e3 n i)
    | Tml.Fix e' -> Tml.Fix (sub e' n (i+1))
    | Tml.Num _ -> m
    | Tml.Plus -> m
    | Tml.Minus -> m
    | Tml.Eq -> m

let rec step1 e = match e with
    | Tml.Ind _ -> raise Stuck
    | Tml.Lam _ -> raise Stuck
    | Tml.App (e1, e2) -> (try Tml.App (step1 e1, e2) with
                            | Stuck -> (match e1 with
                                | Tml.Lam e' -> (try Tml.App (e1, step1 e2) with Stuck -> sub e' e2 0)
                                | Tml.Plus -> (try Tml.App (e1, step1 e2) with 
                                                | Stuck -> (match e2 with
                                                        | Tml.Pair (Tml.Num a, Tml.Num b) -> (Tml.Num (a + b))
                                                        | _ -> raise Stuck))
                                | Tml.Minus -> (try Tml.App (e1, step1 e2) with
                                                | Stuck -> (match e2 with
                                                        | Tml.Pair (Tml.Num a, Tml.Num b) -> (Tml.Num (a - b))
                                                        | _ -> raise Stuck))
                                | Tml.Eq -> (try Tml.App (e1, step1 e2) with
                                                | Stuck -> (match e2 with
                                                        | Tml.Pair (a, b) -> (if a = b then Tml.True else Tml.False)
                                                        |_ -> raise Stuck))
                                | _ -> raise Stuck))
    | Tml.Fst e' -> (try Tml.Fst (step1 e') with 
                    | Stuck -> (match e' with
                            | Tml.Pair (a, b) -> a
                            | _ -> raise Stuck))
    | Tml.Snd e' ->  (try Tml.Snd (step1 e') with 
                    | Stuck -> (match e' with
                            |Tml.Pair (a, b) -> b
                            | _ -> raise Stuck))
    | Tml.Pair (e1', e2') ->( try Tml.Pair(step1 e1', e2') with 
                            | Stuck -> Tml.Pair(e1',step1 e2'))
    | Tml.Eunit -> raise Stuck
    | Tml.Inl e' -> Tml.Inl (step1 e')
    | Tml.Inr e' -> Tml.Inr (step1 e')
    | Tml.Case (e', e1', e2') ->(try Tml.Case (step1 e', e1', e2') with
                                | Stuck -> (match e' with
                                        | Inl x -> sub e1' x 0
                                        | Inr x -> sub e2' x 0
                                        | _ -> raise Stuck))
    | Tml.True -> raise Stuck
    | Tml.False -> raise Stuck
    | Tml.Ifthenelse (e', e1', e2') -> (try Tml.Ifthenelse (step1 e', e1', e2') with 
                                        | Stuck -> ( match e' with
                                                    | Tml.True -> e1'
                                                    | Tml.False -> e2'
                                                    | _ -> raise Stuck))
    | Tml.Fix e' -> sub e' e 0
    | Tml.Num _ -> raise Stuck
    | Tml.Plus -> raise Stuck
    | Tml.Minus -> raise Stuck
    | Tml.Eq -> raise Stuck


(* Problem 3. 
 * step2 : state -> state *)
let step2 _ = raise NotImplemented
                    
(* exp2string : Tml.exp -> string *)
let rec exp2string exp = 
  match exp with 
    Ind x -> string_of_int x
  | Lam e -> "(lam. " ^ (exp2string e) ^ ")"
  | App (e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
  | Pair (e1, e2) -> "(" ^ (exp2string e1) ^ "," ^ (exp2string e2) ^ ")"
  | Fst e -> "(fst " ^ (exp2string e) ^ ")"
  | Snd e -> "(snd " ^ (exp2string e) ^ ")"
  | Eunit -> "()"
  | Inl e -> "(inl " ^ (exp2string e) ^ ")"
  | Inr e -> "(inr " ^ (exp2string e) ^ ")"
  | Case (e, e1, e2) -> "(case " ^ (exp2string e) ^" of " ^ (exp2string e1) ^
                          " | " ^ (exp2string e2) ^ ")"
  | Fix e -> "fix. "  ^ (exp2string e) ^ ")"
  | Ifthenelse (e, e1, e2) -> 
     "(if " ^ (exp2string e) ^ " then " ^ (exp2string e1) ^ 
       " else " ^ (exp2string e2) ^ ")"
  | True -> "true"  | False -> "false"
  | Num n -> "<" ^ (string_of_int n) ^ ">"
  | Plus -> "+"  | Minus -> "-" | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let state2string st = match st with
    Anal_ST(_,_,exp,_) -> "Analysis : ???"
  | Return_ST(_,_,_) -> "Return : ??? "

(* ------------------------------------------------------------- *)     
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None

let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
  let rec steps e = 
    match (stepOpt1 e) with
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

let stepStream2 st =
  let rec steps st = 
    match (stepOpt2 st) with
      None -> Stream.from (fun _ -> None)
    | Some st' -> Stream.icons st' (steps st')
  in 
  Stream.icons st (steps st)
