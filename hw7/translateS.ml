open Mach
open Mono 
(* open Dict *)
exception NotImplemented
exception Wtf

(* location *)
type loc =
    L_INT of int          (* integer constant *)
  | L_BOOL of bool        (* boolean constant *)
  | L_UNIT                (* unit constant *)
  | L_STR of string       (* string constant *)
  | L_ADDR of Mach.addr   (* at the specified address *)
  | L_REG of Mach.reg     (* at the specified register *)
  | L_DREF of loc * int   (* at the specified location with the specified offset *)

type venv = (Mono.avid, loc) Dict.dict  (* variable environment *)
let venv0 : venv = Dict.empty           (* empty variable environment *)

type env = venv * int
let env0 : env = (venv0, 0)

(* val loc2rvalue : loc -> Mach.code * rvalue *)
let rec loc2rvalue l = match l with
    L_INT i -> (Mach.code0, Mach.INT i)
  | L_BOOL b -> (Mach.code0, Mach.BOOL b)
  | L_UNIT -> (Mach.code0, Mach.UNIT)
  | L_STR s -> (Mach.code0, Mach.STR s)
  | L_ADDR a -> (Mach.code0, Mach.ADDR a)
  | L_REG r -> (Mach.code0, Mach.REG r)
  | L_DREF (L_ADDR a, i) -> (Mach.code0, Mach.REFADDR (a, i))
  | L_DREF (L_REG r, i) -> (Mach.code0, Mach.REFREG (r, i))
  | L_DREF (l, i) ->
     let (code, rvalue) = loc2rvalue l in
     (Mach.cpost code [Mach.MOVE (Mach.LREG Mach.tr, rvalue)], Mach.REFREG (Mach.tr, i))
let rec pat2exp p= match p with
(*     P_WILD ->  *)
  | P_INT i -> E_INT i
  | P_BOOL b -> E_BOOL b
  | P_UNIT -> E_UNIT
  | P_VID vid -> E_VID vid
  | P_PAIR (PATTY(p1, ty1), PATTY(p2, ty2)) -> 
      E_PAIR (EXPTY(pat2exp p1, ty1), EXPTY(pat2exp p2, ty2))
(*
 * helper functions for debugging
 *)
(* val loc2str : loc -> string *)
let rec loc2str l = match l with 
    L_INT i -> "INT " ^ (string_of_int i)
  | L_BOOL b -> "BOOL " ^ (string_of_bool b)
  | L_UNIT -> "UNIT"
  | L_STR s -> "STR " ^ s
  | L_ADDR (Mach.CADDR a) -> "ADDR " ^ ("&" ^ a)
  | L_ADDR (Mach.HADDR a) -> "ADDR " ^ ("&Heap_" ^ (string_of_int a))
  | L_ADDR (Mach.SADDR a) -> "ADDR " ^ ("&Stack_" ^ (string_of_int a))
  | L_REG r -> 
     if r = Mach.sp then "REG SP"
     else if r = Mach.bp then "REG BP"
     else if r = Mach.cp then "REG CP"
     else if r = Mach.ax then "REG AX"
     else if r = Mach.bx then "REG BX"
     else if r = Mach.tr then "REG TR"
     else if r = Mach.zr then "REG ZR"
     else "R[" ^ (string_of_int r) ^ "]"
  | L_DREF (l, i) -> "DREF(" ^ (loc2str l) ^ ", " ^ (string_of_int i) ^ ")"

(*
 * Generate code for Abstract Machine MACH 
 *)
(* pat2code : Mach.label -> Mach.label - > loc -> Mono.pat -> Mach.code * venv *)
let pat2code l_start l_fail l pat = raise NotImplemented

(* patty2code : Mach.label -> Mach.label -> loc -> Mono.patty -> Mach.code * venv *)
let patty2code _ _ _ _ = raise NotImplemented
let rec findx l =
  match l with
  |[] -> None
  |h::t -> 
    (match h with
      M_RULE(PATTY(pat,pty),EXPTY(exp,ety)) ->
      match pat with
      |P_VID (avid,is) -> Some avid
      |_ -> findx t
    )

let rval2loc rval = match rval with
      INT i -> L_INT i
    | BOOL b -> L_BOOL b
    | UNIT -> L_UNIT
    | STR s -> L_STR s
    | ADDR a -> L_ADDR a
    | REG r -> L_REG r
    | REFADDR (a, i) -> L_DREF(L_ADDR a, i)
    | REFREG (r, i) -> L_DREF(L_REG r, i)
(* exp2code : env -> Mach.label -> Mono.exp -> Mach.code * Mach.rvalue *)
let rec exp2code env l_start exp =
  let rec exp2rvalue exp =
  match exp with
  E_INT i -> INT i
  | E_BOOL b -> BOOL b
  | E_UNIT -> UNIT
  in
  match exp with
  |E_INT i -> (code0,INT i)
  |E_BOOL b -> (code0,BOOL b)
  |E_UNIT -> (code0,UNIT)
  |E_FUN l -> 
  let f_final = labelNew () in
    let rec patmat l =
    (match l with
      h::t ->
      let M_RULE(PATTY(pat,pty),EXPTY(exp,ety)) = h in
      let mat = labelNew () in
      let nmat = labelNew () in
      let (code,rvalue) = exp2code env mat exp in
      (match pat with
      P_PAIR (_, _) ->
      let rec pat2jmpcode pair reg =
       (match pair with
          P_PAIR (PATTY(P_PAIR (pair11, pair12), _), PATTY (P_PAIR (pair21, pair22), _)) ->
           clist [PUSH(REFREG (reg, 0)); POP(LREG r26)] @@ (pat2jmpcode (P_PAIR (pair11, pair12)) r26) @@
           clist [PUSH(REFREG (reg, 1)); POP(LREG r27)] @@ (pat2jmpcode (P_PAIR (pair21, pair22)) r27)
        | P_PAIR(PATTY(P_PAIR (pair11, pair12), _), PATTY(pat, _)) ->
            let (_, rvalue') = exp2code env mat (pat2exp pat) in
            clist [PUSH(REFREG (reg, 0)); POP(LREG r26)] @@ (pat2jmpcode (P_PAIR (pair11, pair12)) r26) @@
            clist[JMPNEQ(ADDR(CADDR nmat), rvalue', REFREG(reg, 1))]
        | P_PAIR(PATTY(pat, _), PATTY(P_PAIR(pair21, pair22), _)) ->
            let (_, rvalue') = exp2code env mat (pat2exp pat) in
            clist [PUSH(REFREG (reg, 1)); POP(LREG r27)] @@ (pat2jmpcode (P_PAIR (pair21, pair22)) r27) @@
            clist[JMPNEQ(ADDR(CADDR nmat), rvalue', REFREG(reg, 0))]
        | P_PAIR(PATTY(pat1, _), PATTY(pat2, _)) -> 
            let (_, rvalue1) = exp2code env mat (pat2exp pat1) in
            let (_, rvalue2) = exp2code env mat (pat2exp pat2) in
            clist[JMPNEQ(ADDR(CADDR nmat), rvalue1, REFREG(reg, 0));
            JMPNEQ(ADDR(CADDR nmat), rvalue2, REFREG(reg, 1))])
      in
      clist[PUSH(REFREG(bp,-3)); POP(LREG r25)] @@ (pat2jmpcode pat r25) @@clist [LABEL mat]@@code@@clist[MOVE (LREG r19, rvalue); JUMP(ADDR(CADDR f_final));LABEL nmat]@@patmat t
      |P_WILD -> let (code,rvalue) = exp2code env mat exp in
      code@@clist[MOVE (LREG r19,rvalue);RETURN]
      |P_VID (avid,is) ->(match is with
          VAR -> 
          let (venv, num) = env in
          let env = (venv@[avid,L_DREF(L_REG bp,-3)], num) in
          let (code,rvalue) = exp2code env mat exp in
          code@@clist[MOVE (LREG r19,rvalue);RETURN]
        | CON ->
          let (code, rvalue) = exp2code env mat exp in
          clist[JMPNEQSTR(ADDR(CADDR nmat), REFREG(bp, -3), STR avid);LABEL mat] @@ code @@
          clist[MOVE (LREG r19, rvalue);RETURN; LABEL nmat] @@ patmat t)
      | P_VIDP ((avid, is), PATTY(pat1, ty)) ->(
        let (venv, num) = env in
        let (code, rvalue) = exp2code env mat exp in
        let matched = match Dict.lookup avid venv with |None -> BOOL true |Some k -> BOOL false in
        let conf = match Dict.lookup avid venv with |None -> L_INT 0 |Some k -> k in
        let (_, rvalue1) = exp2code env mat (pat2exp pat1) in
        let (_, value') = loc2rvalue conf in
        clist[JMPTRUE(ADDR(CADDR nmat), matched)] @@ 
        match pat1 with 
          P_WILD -> clist[]
        | _ ->(match value' with 
            INT i -> clist[JMPNEQ(ADDR(CADDR nmat), value', rvalue1)]
            | BOOL b -> (match rvalue1 with BOOL b2 -> clist[JMPTRUE(ADDR(CADDR nmat), BOOL (b<>b2))])
            | UNIT -> (match rvalue1 with UNIT -> clist[] | _ -> clist[JUMP(ADDR(CADDR nmat))]))
        @@ clist [LABEL mat] @@ code @@ clist[MOVE (LREG r19, rvalue); RETURN; LABEL nmat] @@ patmat t)
      | _ -> let (code',rvalue') = exp2code env mat (pat2exp pat) in
      clist[JMPNEQ(ADDR(CADDR nmat),rvalue',REFREG(bp,-3));LABEL mat]@@code @@clist[MOVE (LREG r19,rvalue);RETURN;LABEL nmat]@@patmat t
      )
    |[] -> clist[]
    )
  in (clist[LABEL l_start]@@(patmat l)@@clist[LABEL f_final],REG r19)
  |E_PAIR (expty1, expty2) -> (match (expty1, expty2) with
    (EXPTY (exp1, _), EXPTY (exp2, _)) ->
    (match exp1, exp2 with
    (E_PAIR _, E_PAIR _) -> 
        let (code1, val1) = exp2code env (labelNew ()) exp1 in
        let (code2, val2) = exp2code env (labelNew ()) exp2 in
        (clist ([LABEL (l_start)] @ code1 @[PUSH(REG r10)] @ code2 @[PUSH(REG r10)]@ 
        [MALLOC(LREG r10, INT 2); POP(LREG r12); POP(LREG r11); MOVE(LREFREG(r10, 0), REG r11); MOVE(LREFREG(r10, 1), REG r12)]), REG r10)
    | (E_PAIR _, _) -> 
        let (code1, val1) = exp2code env (labelNew ()) exp1 in
        (clist ([LABEL (l_start)] @ code1 @[PUSH(REG r10)]@[MALLOC(LREG r10, INT 2);POP(LREG r11);
        MOVE(LREFREG(r10, 0), REG r11); MOVE(LREFREG(r10, 1), exp2rvalue exp2)]), REG r10)
    | (_, E_PAIR _) -> 
        let (code2, val2) = exp2code env (labelNew ()) exp2 in
        (clist ([LABEL (l_start)] @ code2 @[PUSH(REG r10)]@ [MALLOC(LREG r10, INT 2); POP(LREG r12);
        MOVE(LREFREG(r10, 0), exp2rvalue exp1); MOVE(LREFREG(r10, 1), REG r12)]), REG r10)
    | _ ->
        (clist ([LABEL (l_start); MALLOC(LREG r10, INT 2); MOVE(LREFREG (r10, 0), exp2rvalue exp1); MOVE(LREFREG (r10, 1), exp2rvalue exp2)]), REG r10))
    )
  |E_VID (avid,is) ->
      let (venv,i) = env in
      let value = (match Dict.lookup avid venv with |None -> L_INT 0 |Some k -> k) in
      let (a,b) = loc2rvalue value in
      (a,b)
  | E_APP (expty1, expty2) ->
    (match (expty1, expty2) with
    (EXPTY(exp1, _), EXPTY(exp2, ty)) ->(match (exp1, exp2) with
      (E_PLUS, E_PAIR (EXPTY (exp11, _), EXPTY(exp12, _))) ->
      let (code1, value1) = exp2code env (labelNew ()) exp11 in
      let (code2, value2) = exp2code env (labelNew ()) exp12 in
      (match value1 with INT _ -> 
      (code2 @@ clist [LABEL (l_start); ADD(LREG ax, value1, value2)], REG ax)
      | _ ->
      (code1 @@ clist [MOVE (LREG r21, value1)] @@ code2 @@ clist [LABEL (l_start); ADD (LREG ax, REG r21, value2)], REG ax))
    
    | (E_MINUS, E_PAIR (EXPTY (exp11, _), EXPTY(exp12, _))) ->
      let (code1, value1) = exp2code env (labelNew ()) exp11 in
      let (code2, value2) = exp2code env (labelNew ()) exp12 in
      (match value1 with INT _ -> 
      (code2 @@ clist [LABEL (l_start); SUB (LREG ax, value1, value2)], REG ax)
      | _ ->
      (code1 @@ clist [MOVE (LREG r21, value1)] @@ code2 @@ clist [LABEL (l_start); SUB (LREG ax, REG r21, value2)], REG ax))
    | (E_MULT, E_PAIR (EXPTY (exp11, _), EXPTY(exp12, _))) ->
      let (code1, value1) = exp2code env (labelNew ()) exp11 in
      let (code2, value2) = exp2code env (labelNew ()) exp12 in
      (match value1 with INT _ -> 
      (code2 @@ clist [LABEL (l_start); MUL (LREG ax, value1, value2)], REG ax)
      | _ ->
      (code1 @@ clist [MOVE (LREG r21, value1)] @@ code2 @@ clist [LABEL (l_start); MUL (LREG ax, REG r21, value2)], REG ax))
    | (E_EQ, E_PAIR (EXPTY (exp11, _), EXPTY(exp12, _))) ->
      let (code1, value1) = exp2code env (labelNew ()) exp11 in
      let (code2, value2) = exp2code env (labelNew ()) exp12 in
      let neq = labelNew () in let eq = labelNew () in
      (code1 @@ clist [MOVE (LREG r29, value1)] @@ code2 @@ clist [LABEL (l_start);JMPNEQ(ADDR(CADDR(neq)),REG r29,value2);MOVE(LREG ax,BOOL true);
        JUMP (ADDR(CADDR(eq)));LABEL (neq);MOVE(LREG ax, BOOL false);LABEL (eq)], REG ax)
    | (E_APP (exp1,exp2),exp) -> 
      let (code,rvalue) = exp2code env (labelNew ()) exp in
      let (code',rvalue') = exp2code env (labelNew ()) (E_APP (exp1,exp2)) in
      (code@@clist[PUSH rvalue]@@code'@@clist[POP (LREG r18)],rvalue')
    | (E_FUN l,etype) ->
      (match etype with
          E_VID(str, CON) ->
        (let f_start = labelNew () in
        let f_ret = labelNew () in
        let (code, value) = exp2code env f_start exp1 in
        ((clist[PUSH (STR str); CALL(ADDR(CADDR f_start));JUMP(ADDR(CADDR f_ret))]) @@ code @@(clist[LABEL f_ret; POP(LREG r18)]), value)
        )
        | E_APP(EXPTY(E_VID (str, CONF), _), EXPTY(exp, _)) -> (
          let f_start = labelNew () in
          let f_ret = labelNew () in
          let (code', value') = exp2code env l_start exp in
          let (venv, i) = env in
          let (code, value) = exp2code (Dict.insert (str, rval2loc value') venv, i+1) f_start exp1 in 
          (code' @@ clist[PUSH (STR str);CALL(ADDR(CADDR f_start)); JUMP(ADDR(CADDR f_ret))] @@ code @@
          (clist[LABEL f_ret; POP(LREG r18)]), value))
        | _ ->
          let f_start = labelNew () in
          let f_ret = labelNew () in
          let (code,rvalue) = exp2code env l_start etype in
          let (code1,rvalue1) = exp2code env f_start (E_FUN l) in
          (code@@clist[PUSH (rvalue);CALL (ADDR(CADDR f_start));JUMP (ADDR(CADDR f_ret))]@@code1@@clist[LABEL f_ret;POP(LREG r18)],rvalue1)
      )
    | (E_VID (varname, is), exp) -> 
    match is with
      VAR ->(
      let (venv, num) = env in
      let tofun = (match Dict.lookup varname venv with Some k -> k | None -> L_INT 0) in
      let f_ret = labelNew () in
      let (code, rvalue) = exp2code env l_start exp in
      let (_, tofun') = loc2rvalue tofun in
      let ADDR(CADDR(tofun'')) = tofun' in
      let (code', rvalue') = exp2code env tofun'' exp1 in
      (code @@ clist [PUSH (rvalue); CALL(tofun'); JUMP(ADDR(CADDR f_ret))]@@code'@@[LABEL f_ret;POP(LREG r18)], REG r19)) 
    )
    )

(* expty2code : env -> Mach.label -> Mono.expty -> Mach.code * Mach.rvalue *)
let expty2code _ _ _ = raise NotImplemented

(* dec2code : env -> Mach.label -> Mono.dec -> Mach.code * env *)
let rec dec2code env l_start dec = 
  match dec with
  D_VAL (patty, expty) -> (match (patty, expty) with
    (PATTY(pat, _), EXPTY(exp, _)) ->
      (match pat with
        P_VID ((varname, _):vid) -> (*vid only as a variable name*)
          (match exp with
            E_FUN l ->  (let (expcode, value) = exp2code env (labelNew ()) exp in
            let jmplabel = labelNew () in
            let calllabel = labelNew () in
            let (venv, num) = env in
            ((clist[JUMP (ADDR(CADDR(jmplabel))); LABEL (calllabel)] @@ expcode @@ clist [LABEL (jmplabel)]), (Dict.insert (varname, L_ADDR (CADDR(calllabel))) venv, num)))
            | _ -> 
            (let (expcode, value) = exp2code env (labelNew ()) exp in
            let (venv, num) = env in
            (expcode @@ clist ([MALLOC(LREG r13, INT 2);MOVE(LREFREG(r13, 0), STR varname); MOVE(LREFREG(r13, 1), value);
            PUSH(REG r13)])),((Dict.insert (varname, L_DREF(L_DREF (L_ADDR (SADDR (bp+num)), -1), 1)) venv), num+1))
          )
        | P_PAIR (patty1, patty2) -> 
          let (expcode, value) = exp2code env (labelNew ()) exp in
          let rec pair2vars p_pair r env =
          let (venv, num) = env in
          (match p_pair with
            (PATTY(pat1, _), PATTY(pat2, _)) ->
              (match (pat1, pat2) with
                (P_WILD, P_WILD) -> ([], env)
              | (P_WILD, P_VID(varname2, _)) ->
                (([PUSH(REFREG(r, 1)); POP(LREG r15); MALLOC(LREG r17, INT 2); MOVE(LREFREG (r17, 0), STR varname2);
                MOVE(LREFREG (r17, 1), REG r15); PUSH(REG r17)]), ((Dict.insert (varname2, L_DREF(L_DREF (L_ADDR (SADDR (bp+num)), -1), 1)) venv), num+1))
              | (P_VID(varname1, _), P_WILD) ->
                (([PUSH(REFREG(r, 0)); POP(LREG r14); MALLOC(LREG r16, INT 2); MOVE(LREFREG (r16, 0), STR varname1);
                MOVE(LREFREG (r16, 1), REG r14); PUSH(REG r16)]), ((Dict.insert (varname1, L_DREF(L_DREF (L_ADDR (SADDR (bp+num)), -1), 1)) venv), num+1))
              | (P_WILD, P_PAIR(patty21, patty22)) -> 
                let (code1, env1) = (pair2vars (patty21, patty22) r15 env) in
                (([PUSH(REFREG(r, 1)); POP(LREG r15)] @ code1), env1)
              | (P_PAIR (patty11, patty12), P_VID(varname2, _)) -> 
                let (code1, env1) = (pair2vars (patty11, patty12) r14 env) in
                let (venv1, num1) = env1 in
                ((code1 @ ([PUSH(REFREG(r, 1)); POP(LREG r15); MALLOC(LREG r17, INT 2); MOVE(LREFREG (r17, 0), STR varname2);
                MOVE(LREFREG (r17, 1), REG r15); PUSH(REG r17)])), ((Dict.insert (varname2, L_DREF(L_DREF (L_ADDR (SADDR (bp+num1)), -1), 1)) venv1), num1+1))
              | (P_VID(varname1, _), P_PAIR(patty21, patty22)) -> 
                let (code1, env1) = (pair2vars (patty21, patty22) r15 env) in
                let (venv1, num1) = env1 in
                ((code1 @ ([PUSH(REFREG(r, 0)); POP(LREG r14); MALLOC(LREG r16, INT 2); MOVE(LREFREG (r16, 0), STR varname1);
                MOVE(LREFREG (r16, 1), REG r14); PUSH(REG r16)])), ((Dict.insert (varname1, L_DREF(L_DREF (L_ADDR (SADDR (bp+num1)), -1), 1)) venv1), num1+1))
              | (P_PAIR (patty11, patty12), P_WILD) -> 
                let (code1, env1) = (pair2vars (patty11, patty12) r14 env) in
                (([PUSH(REFREG(r, 0)); POP(LREG r14)] @ code1), env1)
              | (P_PAIR (patty11, patty12), P_PAIR (patty21, patty22)) ->
                let (code1, env1) = pair2vars (patty11, patty12) r14 env in
                let (code2, env2) = pair2vars (patty21, patty22) r15 env1 in
                (([PUSH(REFREG(r, 0)); POP(LREG r14)] @ code1 @ [PUSH(REFREG(r, 1)); POP(LREG r15)] @ code2), env2)
              )
          )
          in let (code1, env1) = pair2vars (patty1, patty2) r10 env in
          (expcode @@ clist (code1), env1)
      )
  )
  | D_REC (PATTY(P_VID (varname,is),_), EXPTY(exp,_)) ->( match exp with
            E_FUN l ->  (let (expcode, value) = exp2code env (labelNew ()) exp in
            let jmplabel = labelNew () in
            let calllabel = labelNew () in
            let (venv, num) = env in
            ((clist[JUMP (ADDR(CADDR(jmplabel))); LABEL (calllabel)] @@ expcode @@
              clist [RETURN; LABEL (jmplabel)]), (Dict.insert (varname, L_ADDR (CADDR(calllabel))) venv, num+1)))
            | _ -> 
            (let (expcode, value) = exp2code env (labelNew ()) exp in
            let (venv, num) = env in
            ((expcode @@ clist ([MALLOC(LREG r13, INT 2); MOVE(LREFREG(r13, 0), STR varname); MOVE(LREFREG(r13, 1), value);
              PUSH(REG r13)])),((Dict.insert (varname, L_DREF(L_DREF (L_ADDR (SADDR (bp+num)), -1), 1)) venv), num+1))
            )
          )
  | D_DTYPE -> (code0, env)

(* mrule2code : env -> Mach.label -> Mono.mrule -> Mach.code *)
 let rec mrule2code env l_start l_fail l = raise NotImplemented 
  
(* program2code : Mono.program -> Mach.code *)
let program2code (dlist, et) = 
  let rec dlist2code dlist env =
  match dlist with 
  (dec :: rem) -> let (code, env1) = (dec2code env (labelNew ()) dec) in
    let (code', env') = dlist2code rem env1 in
    (code @@ code', env')
  | [] -> (code0, env)
  in 
  let (dcode, denv) = (dlist2code dlist env0) in
  match et with
  EXPTY (exp, ty) -> let (a, b) = (exp2code denv (labelNew ()) exp) in
  cpost ([LABEL start_label] @ dcode @ a) [HALT b]