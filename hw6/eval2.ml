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
let rec shifting i m ex = match ex with
    | Tml.Ind n -> if n < i then Tml.Ind n
                else Tml.Ind (n+m)
    | Tml.App (n1, n2) -> Tml.App (shifting i m n1, shifting i m n2)
    | Tml.Lam n -> Tml.Lam (shifting (i+1) m n)
    | Tml.Pair (n1, n2) -> Tml.Pair (shifting i m n1, shifting i m n2)
    | Tml.Fst n -> Tml.Fst (shifting i m n)
    | Tml.Snd n -> Tml.Snd (shifting i m n)
    | Tml.Eunit -> Tml.Eunit
    | Tml.Inl n -> Tml.Inl (shifting i m n)
    | Tml.Inr n -> Tml.Inr (shifting i m n)
    | Tml.Case (n, n1, n2) -> Tml.Case (shifting i m n, shifting (i+1) m n1, shifting (i+1) m n2)
    | Tml.Fix n -> Tml.Fix (shifting (i+1) m n)
    | Tml.True -> Tml.True
    | Tml.False -> Tml.False
    | Tml.Ifthenelse (n, n1, n2) -> Tml.Ifthenelse (shifting i m n, shifting i m n1, shifting i m n2)
    | Tml.Num n -> Tml.Num n
    | Tml.Plus -> Tml.Plus
    | Tml.Minus -> Tml.Minus
    | Tml.Eq -> Tml.Eq

let rec sub i m n = match m with
    | Tml.Ind m' -> if m'<i then Tml.Ind (m')
                else if m'>i then Tml.Ind (m'-1)
                else (shifting 0 i n)
    | Tml.Lam m' -> Tml.Lam(sub (i+1) m' n)
    | Tml.App (m1, m2) -> Tml.App (sub i m1 n, sub i m2 n)
    | Tml.Pair (m1, m2) -> Tml.App (sub i m1 n, sub i m2 n)
    | Tml.Fst m' -> Tml.Fst (sub i m' n)
    | Tml.Snd m' -> Tml.Snd (sub i m' n)
    | Tml.Eunit -> Tml.Eunit
    | Tml.Inl m' -> Tml.Inl (sub i m' n)
    | Tml.Inr m' -> Tml.Inr (sub i m' n)
    | Tml.Case (m', m1, m2) -> Tml.Case (sub i m' n, sub (i+1) m1 n, sub (i+1) m2 n)
    | Tml.Fix m' -> Tml.Fix (sub (i+1) m' n)
    | Tml.True -> Tml.True
    | Tml.False -> Tml.False
    | Tml.Ifthenelse (m', m1, m2) -> Tml.Ifthenelse (sub i m' n, sub i m1 n, sub i m2 n)
    | Tml.Num m' -> Tml.Num m'
    | Tml.Plus -> Tml.Plus
    | Tml.Minus -> Tml.Minus
    | Tml.Eq -> Tml.Eq


let rec step1 e = 
    let rec checkStuck ex = match ex with
        | Tml.App (_,_)| Tml.Fst _ | Tml.Snd _ | Tml.Fix _ 
        | Tml.Case (_,_,_) | Tml.Ifthenelse (_,_,_) -> false
        | Tml.Pair (ex1, ex2) -> (checkStuck ex1) && (checkStuck ex2)
        | Tml.Inl ex' -> checkStuck ex'
        | Tml.Inr ex' -> checkStuck ex'
        | _ -> true
    in
    match e with
    | Tml.App (e1, e2) -> (
        if checkStuck e1 then
            match e1 with
            | Tml.Lam e' -> (if checkStuck e2 then (sub 0 e' e2)
                            else Tml.App (e1, step1 e2))
            | Tml.Plus | Tml.Minus | Tml.Eq -> (if checkStuck e2 then match e2 with
                                                | Tml.Pair (Tml.Num a, Tml.Num b) -> (match e1 with
                                                    | Tml.Plus -> Tml.Num (a + b)
                                                    | Tml.Minus -> Tml.Num (a - b)
                                                    | Tml.Eq ->( if  a = b then Tml.True else Tml.False)
                                                    | _ -> raise Stuck
                                                )
                                                | _ -> raise Stuck
                                                else Tml.App(e1, step1 e2)) 
            | _ -> raise Stuck            
        else Tml.App (step1 e1, e2))
    | Tml.Fst e' -> (if checkStuck e' then match e' with 
                                        | Tml.Pair (a, b) -> a
                                        | _ -> raise Stuck
                     else Tml.Fst (step1 e'))
    | Tml.Snd e' -> (if checkStuck e' then match e' with
                                        | Tml.Pair (a, b) -> b
                                        | _ -> raise Stuck
                    else Tml.Snd (step1 e'))
    | Tml.Pair (e1', e2') ->( if checkStuck e1' then Tml.Pair(e1', step1 e2')
                            else Tml.Pair(step1 e1', e2'))
    | Tml.Inl e' -> Tml.Inl (step1 e')
    | Tml.Inr e' -> Tml.Inr (step1 e')
    | Tml.Case (e', e1', e2') -> (if checkStuck e' then match e' with
                                                    | Tml.Inl x -> sub 0 e1' x
                                                    | Tml.Inr x -> sub 0 e2' x 
                                                    | _ -> raise Stuck
                                else Tml.Case (step1 e', e1', e2')
                                )
    | Tml.Ifthenelse (e', e1', e2') -> (if checkStuck e' then match e' with
                                                    | Tml.True -> e1'
                                                    | Tml.False -> e2'
                                                    | _ -> raise Stuck
                                        else Tml.Ifthenelse (step1 e', e1', e2'))
    | Tml.Fix e' -> sub 0 e' (Tml.Fix e') 
    | _ -> raise Stuck

    
    

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
