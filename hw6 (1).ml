(* TODO: Write a good set of tests for unused_vars. *)
let unused_vars_tests = [
  (* An example test case.
     Note that you are *only* required to write tests for Rec, Fn, and Apply!
  *) 
  
  (* rec (x = x + 4)*)
  (Rec("x",Int,(Primop(Plus,[Var "x";I 4]))),[]);
  
  (Rec ("TRUE", Bool, B true), ["TRUE"]); 
  (Fn ([("x", Int); ("y", Int);("z", Bool)],
       Primop (Plus, [Primop (Times, [Var "x"; Var "x"]);
                      Primop (Times, [Var "y"; Var "y"])])), ["z"]);
  (Apply (Primop(Plus,[I 1;I 2]),[Primop (Times, [Var "x"; Var "x"]);
                                  Primop (Times, [Var "y"; Var "y"])]), []);
  
]

(* TODO: Implement the missing cases of unused_vars. *)
let rec unused_vars =
  function
  | Var _ | I _ | B _ -> []
  | If (e, e1, e2) -> unused_vars e @ unused_vars e1 @ unused_vars e2
  | Primop (_, args) ->
      List.fold_left (fun acc exp -> acc @ unused_vars exp) [] args
  | Let (x, e1, e2) ->
      let unused = unused_vars e1 @ unused_vars e2 in
      if List.mem x (free_variables e2) then
        unused
      else
        x :: unused 
  | Rec (x, _, e) -> 
      let unused = unused_vars e in
      if List.mem x (free_variables e) then
        unused
      else
        x :: unused 
  | Fn (xs, e) ->
      let used = free_variables e in (* what are the unused vars in e*)
      let unused = unused_vars e in
      let namesXS = List.map(fun (h,t) -> h) xs in (* all var names in xs *)
      (* which namesXS are not used in e*)
      let filteredNamesXS = (List.filter (fun x -> not (List.mem x used)) namesXS) in
      filteredNamesXS@unused 
  | Apply (e, es) -> 
      let unused = unused_vars e in
      let unusedES = List.fold_left(fun acc exp -> acc @ unused_vars exp) [] es in
      unused@unusedES
(* TODO: Write a good set of tests for subst. *)
(* Note: we've added a type annotation here so that the compiler can help
   you write tests of the correct form. *)
let subst_tests : (((exp * name) * exp) * exp) list = [
  (* An example test case. If you have trouble writing test cases of the
     proper form, you can try copying this one and modifying it.
     Note that you are *only* required to write tests for Rec, Fn, and Apply!
  *)
  (((I 1, "x"), (* [1/x] *)
    (* let y = 2 in y + x *)
    Let ("y", I 2, Primop (Plus, [Var "y"; Var "x"]))),
   (* let y = 2 in y + 1 *)
   Let ("y", I 2, Primop (Plus, [Var "y"; I 1])));
  
  (((I 1, "x"), (* [1/x] *)
    Rec("x", Int, Primop (Plus, [Var "x"; Var "x"]))),
   Rec("x", Int, Primop (Plus, [Var "x"; Var "x"]))); 
   
  (((Primop (Plus, [Var "y"; I 1]), "x"), (* [y+1/x] *)
    Rec("y", Int, Primop (Plus, [Var "y"; Var "x"]))),
   Rec("z", Int, Primop (Plus, [Var "z"; Primop (Plus, [Var "y"; I 1])]))); 
  
  (((Primop (Plus, [Var "y"; I 1]), "x"), (* [y+1/x] *)
    Fn([("y", Int)], Primop (Plus, [Var "y"; Var "x"]))),
   Fn([("z", Int)], Primop (Plus, [Var "z"; Primop (Plus, [Var "y"; I 1])])));
  
  
  (((I 1, "x"), (* [1/x] *)
    Apply(I 5, [Primop (Plus, [Var "y"; Var "x"])])),
   Apply(I 5, [Primop (Plus, [Var "y"; I 1])]));
  
 
  (((I 1, "x"), (* [1/x] *)
    Fn([("y", Int)], Primop (Plus, [Var "y"; Var "x"]))),
   Fn([("y", Int)], Primop (Plus, [Var "y"; I 1])));
  
  (((I 1, "x"), (* [1/x] *)
    Fn([("y", Int); ("x", Int)], Primop (Plus, [Var "y"; Var "x"]))),
   Fn([("y", Int); ("x", Int)], Primop (Plus, [Var "y"; Var "x"])));
  
  
  (((I 1, "x"), (* [1/x] *)
    Apply(I 5, [Primop (Plus, [Var "y"; Var "x"]); Primop (Plus, [Var "x"; Var "x"])])), 
   Apply(I 5, [Primop (Plus, [Var "y"; I 1]); Primop (Plus, [I 1; I 1])]));
 
  
]

(* TODO: Implement the missing cases of subst. *)
let rec subst ((e', x) as s) exp =
  match exp with
  | Var y ->
      if x = y then e'
      else Var y
  | I n -> I n
  | B b -> B b
  | Primop (po, args) -> Primop (po, List.map (subst s) args)
  | If (e, e1, e2) ->
      If (subst s e, subst s e1, subst s e2)
  | Let (y, e1, e2) ->
      let e1' = subst s e1 in
      if y = x then
        Let (y, e1', e2)
      else
        let (y, e2) =
          if List.mem y (free_variables e') then
            rename y e2
          else
            (y, e2)
        in
        Let (y, e1', subst s e2)

  | Rec (y, t, e) -> if y = x then
        Rec (y, t, e) 
      else
        let (y, e) = 
          if List.mem y (free_variables e') then
            rename y e
          else
            (y, e)
        in
        Rec (y, t, subst s e)

  | Fn (xs, e) ->  let p x1 = (x1 = x) in
      let pr_mem x1 = (List.mem x1 (free_variables e')) in
      let xs1 = List.map fst xs in
      let xs2 = List.map snd xs in 
      (match List.filter p xs1 with
       | [] ->
           (match List.filter pr_mem xs1 with
            | [] -> Fn (xs, subst s e)
            | _ -> 
                let (xs1, e) = rename_all xs1 e in
                let xs = List.combine xs1 xs2 in
                Fn(xs, subst s e))
       | _ -> Fn (xs, e))

  | Apply (e, es) -> Apply (subst s e, List.map (subst s) es)

and rename x e =
  let x' = freshVar x in
  (x', subst (Var x', x) e)

and rename_all names exp =
  List.fold_right
    (fun name (names, exp) ->
       let (name', exp') = rename name exp in
       (name' :: names, exp'))
    names
    ([], exp)

(* Applying a list of substitutions to an expression, leftmost first *)
let subst_list subs exp =
  List.fold_left (fun exp sub -> subst sub exp) exp subs


(* TODO: Write a good set of tests for eval. *)
let eval_tests = [
  (* An example test case.
     Note that you are *only* required to write tests for Rec and Apply!
  *)
  (Let ("y", I 1, Primop (Plus, [Var "y"; I 5])), I 6) ;
  (Rec ("x", Int, I 5), I 5);
  (Apply (Fn ([], B true), []), B true);
  (Apply (Apply (Fn ([("y", Int)],
                     Fn ([("x", Int)],
                         Primop (Plus, [Var "y"; Var "x"]))), [I 3]),
          [I 4]), I 7);
  (Apply (Fn ([("x", Int); ("y", Int)],
              Primop (Plus,
                      [Primop (Times, [Var "x"; Var "y"]);
                       Primop (Times, [Var "x"; Var "y"])])), [I 3; I 3]), I 18)
  
]

(* TODO: Implement the missing cases of eval. *)
let rec eval exp =
  match exp with
  (* Values evaluate to themselves *)
  | I _ -> exp
  | B _ -> exp
  | Fn _ -> exp

  (* This evaluator is _not_ environment-based. Variables should never
     appear during evaluation since they should be substituted away when
     eliminating binding constructs, e.g. function applications and lets.
     Therefore, if we encounter a variable, we raise an error.
*)
  | Var x -> raise (Stuck (Free_variable x))

  (* Primitive operations: +, -, *, <, = *)
  | Primop (po, args) ->
      let args = List.map eval args in
      begin
        match eval_op po args with
        | None -> raise (Stuck Bad_primop_args)
        | Some v -> v
      end

  | If (e, e1, e2) ->
      begin
        match eval e with
        | B true -> eval e1
        | B false -> eval e2
        | _ -> raise (Stuck If_non_true_false)
      end

  | Let (x, e1, e2) ->
      let e1 = eval e1 in
      eval (subst (e1, x) e2)

  | Rec (f, tp, e) -> eval (subst (Rec (f, tp, e), f) e)

  | Apply (e, es) -> (*read it bottom up okay*)
      let e' = eval e in 
      match e' with 
      | Fn (xs, e1) -> 
          let vars = List.map fst xs in 
          let values = List.map eval es in
          
          (*if theyre the same size*)
          if List.length values = List.length vars then
            eval (subst_list (List.combine values vars) e1)
          else 
            raise (Stuck Arity_mismatch)
      | _ -> raise (Stuck Apply_non_fn)

(* TODO: Write a good set of tests for infer. *)
let infer_tests = [
  (* An example test case.
     Note that you are *only* required to write tests for Rec, Fn, and Apply!
  *)
  (([("x", Int)], Var "x"), Int);
  (*Rec*)
  (([("x", Int)], Rec ("y", Int, (Primop (Times, [(Var "x"); (Var "y")])))), Int); 
(*Fn*)
  (([("y", Int)], Fn ([], Var "y")), Arrow ([], Int));
  (([], Fn ([("y", Int)], (Primop (Plus, [(Var "y"); (Var "y")])))), Arrow ([Int], Int)); 
  (*(([], Fn ([("x", Int)], (Primop (Plus, [(Var "x"); (Var "x")])))), Arrow ([Int; Int], Int)); *)
  (([], Fn ([("x", Int); ("y", Int)], (Primop (Plus, [(Var "y"); (Var "x")])))), Arrow ([Int; Int], Int)); 
  (([], Fn ([("x", Int); ("x", Int)], (Primop (Plus, [(Var "x"); (Var "x")])))), Arrow ([Int; Int], Int)); 
  (*Apply*)
  (([("x", Int)], Apply(Fn ([], Var "x"), [])), Int);
  (([("x", Int)], Apply(Fn ([("y", Int)], (Primop (Plus, [(Var "y"); (Var "x")]))), [I 3])), Int);
  (([], Apply(Fn ([("x", Int); ("y", Int)], (Primop (Plus, [(Var "y"); (Var "x")]))), [I 3; I 4])), Int);

]

(* TODO: Implement the missing cases of infer. *)
let rec infer ctx e =
  match e with
  | Var x ->
      begin
        try lookup x ctx
        with Not_found -> raise (TypeError (Free_variable x))
      end
  | I _ -> Int
  | B _ -> Bool

  | Primop (po, exps) ->
      let (domain, range) = primopType po in
      check ctx exps domain range

  | If (e, e1, e2) ->
      begin
        match infer ctx e with
        | Bool ->
            let t1 = infer ctx e1 in
            let t2 = infer ctx e2 in
            if t1 = t2 then t1
            else type_mismatch t1 t2
        | t -> type_mismatch Bool t
      end

  | Let (x, e1, e2) ->
      let t1 = infer ctx e1 in
      infer (extend ctx (x, t1)) e2

  | Rec (f, t, e) -> let typ = infer (extend ctx (f, t)) e in
      if t = typ then
        typ
      else
        type_mismatch t typ
          

  | Fn (xs, e) -> let rec list_ext_ctx ctx ls = 
                    (match ls with
                     | [] -> ctx
                     | h::t -> (list_ext_ctx (extend ctx h) t)) in 
      (*list.map snd ??*)
      let t_list = List.map snd xs in
      Arrow(t_list, infer (list_ext_ctx ctx xs) e)

  | Apply (e, es) -> let typ_e = infer ctx e in
      let es_typs = List.map (infer ctx) es in
      match typ_e with
      |Arrow (ts, t) ->
          let rec type_check ts1 ts2= 
            match ts1, ts2 with
            | [], [] -> t
            | h::t, h1::t1 -> 
                if h = h1 then
                  type_check t t1
                else type_mismatch h h1
            | _ -> raise (TypeError Arity_mismatch)
          in type_check ts es_typs
      | _ -> raise (TypeError (Apply_non_arrow (typ_e)))

and check ctx exps tps result =
  match exps, tps with
  | [], [] -> result
  | e :: es, t :: ts ->
      let t' = infer ctx e in
      if t = t' then check ctx es ts result
      else type_mismatch t t'
  | _ -> raise (TypeError Arity_mismatch)
