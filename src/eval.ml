open Runtime

(** Make the stack read-only by pushing a new empty top frame onto it. *)
let make_ro {frame; frames; funs} =
  {frame = [] ; frames = frame :: frames; funs = funs}

(** Push a read-write value onto the top frame. *)
let push_rw x v st = { st with frame = (x, RW (ref v)) :: st.frame }

(** Push a read-only value onto the top frame. *)
let push_ro x v st = { st with frame = (x, RO v) :: st.frame }

(** Define a new function. *)
let push_fun f stack =
  { stack with funs = f :: stack.funs }

(** Push many read-only values *)
let push_ros xs vs st = List.fold_left2 (fun st x v -> push_ro x v st) st xs vs

(** Pop values from stack *)
let pop stack k =
  let rec remove k lst =
    match k, lst with
    | 0, lst -> lst
    | k, _ :: lst -> remove (k-1) lst
    | _, [] -> Runtime.error ~loc:Location.nowhere (Runtime.InternalError "pop")
  in
  {stack with frame = remove k stack.frame}

(** Lookup a value on the stack *)
let lookup_val k {frame; frames; _} =
  let rec lookup k vs vss =
    match k, vs, vss with
    | 0, ((_, RO v) :: _), _ -> Some v
    | 0, ((_, RW r) :: _), _ -> Some !r
    | k, [], (vs :: vss) -> lookup k vs vss
    | k, [], [] -> None
    | k, (_ :: vs), vss -> lookup (k-1) vs vss
  in
  lookup k frame frames

(** Lookup a reference to a read-write value on the stack *)
let lookup_ref k {frame; _} =
  let rec lookup k vs =
    match k, vs  with
    | 0, ((_, RO v) :: _) -> None
    | 0, ((_, RW r) :: _) -> Some r
    | k, [] -> None
    | k, (_ :: vs) -> lookup (k-1) vs
  in
  lookup k frame

(** Lookup a function definition *)
let lookup_fun k {funs; _} =
  let rec lookup k fs =
    match k, fs with
    | _, [] -> None
    | 0, f :: _ -> Some f
    | k, _ :: fs -> lookup (k-1) fs
  in
  lookup k funs

(** Print trace *)
let print_trace ~loc ~prec {frame;frames;_} =
  let xvs = frame @ List.flatten frames in
  Print.message ~loc "Trace"
    "\tprecision: %d@\n\t%t@."
    prec
    (fun ppf ->
      Format.pp_print_list
        ~pp_sep:(fun ppf () -> Format.fprintf ppf "@\n\t")
        (fun ppf (x,entry) ->
          let v = (match entry with
                   | Runtime.RO v -> v
                   | Runtime.RW r -> !r)
          in
          Format.fprintf ppf "%s:\t%t" x (Value.print_value v))
        ppf
        xvs)

(** Extraction of values with expected type *)

let as_integer ~loc v =
  match Value.computation_as_integer v with
  | None -> Runtime.error ~loc Runtime.IntegerExpected
  | Some k -> k

let as_boolean ~loc v =
  match Value.computation_as_boolean v with
  | None -> Runtime.error ~loc Runtime.BooleanExpected
  | Some b -> b

let as_unit ~loc v =
  match Value.computation_as_unit v with
  | None -> Runtime.error ~loc Runtime.UnitExpected
  | Some () -> ()

let as_value ~loc v =
  match Value.computation_as_value v with
  | None -> Runtime.error ~loc Runtime.ValueExpected
  | Some v -> v

(** [comp n stack c] evaluates computation [c] in the given [stack] at
    precision level [n], and returns the new stack and the computed value. *)
let rec comp ~prec stack {Location.data=c; Location.loc} : stack * Value.result =
  if !Config.trace then print_trace ~loc ~prec stack ;
  begin match c with

  | Syntax.Var k ->
     begin match lookup_val k stack with
     | None -> Runtime.error ~loc Runtime.OutOfStack
     | Some v -> stack, Value.return v
     end

  | Syntax.Boolean b ->
     stack, Value.CBoolean b

  | Syntax.Integer k ->
     stack, Value.CInteger k

  | Syntax.Float s ->
     let rl = Dyadic.of_string ~prec ~round:Dyadic.down s in
     let ru = Dyadic.of_string ~prec ~round:Dyadic.up s in
     let r = Real.make rl ru in
     stack, Value.CReal r

  | Syntax.CastReal e ->
     let v = comp_ro ~prec stack e in
     begin match Value.computation_as_integer v with
     | None -> Runtime.error ~loc:e.Location.loc Runtime.IntegerExpected
     | Some k ->
        let rl = Dyadic.of_integer ~prec ~round:Dyadic.down k
        and ru = Dyadic.of_integer ~prec ~round:Dyadic.up k in
        let r = Real.make rl ru in
        stack, Value.CReal r
     end

  | Syntax.Apply (k, es) ->
     begin match lookup_fun k stack with
     | None -> Runtime.error ~loc Runtime.InvalidFunction
     | Some f ->
        let vs = List.map (fun e -> comp_ro_value ~prec stack e) es in
        stack, f ~loc ~prec vs
     end

  | Syntax.Skip ->
     stack, Value.CNone

  | Syntax.Trace ->
     print_trace ~loc ~prec stack ;
     (stack, Value.CNone)

  | Syntax.Sequence (c1, c2) ->
     let stack, v1 = comp ~prec stack c1 in
     let () = as_unit ~loc:(c1.Location.loc) v1 in
     comp ~prec stack c2

  | Syntax.If (b, c1, c2) ->
     let v = comp_ro ~prec stack b in
     begin match as_boolean ~loc:(b.Location.loc) v with
     | true -> comp ~prec stack c1
     | false -> comp ~prec stack c2
     end

  | Syntax.Case lst ->
     let rec fold = function
       | [] -> raise Runtime.Abort
       | (b, c) :: lst ->
          if
            (let v = comp_ro ~prec stack b in
             as_boolean ~loc:(b.Location.loc) v)
          then
            comp ~prec stack c
          else
            fold lst
     in
     fold lst

  | Syntax.While (b, c) ->
     let rec loop stack =
       let v = comp_ro ~prec stack b in
       begin match as_boolean ~loc:(b.Location.loc) v with
       | false -> stack, Value.CNone
       | true ->
          let stack, v = comp ~prec stack c in
          let () = as_unit ~loc:(c.Location.loc) v in
          loop stack
       end
     in
     loop stack

  | Syntax.Newvar (lst, c) ->
     let rec fold stack' = function
       | [] -> stack'
       | (x,e) :: lst ->
          let v = comp_ro_value ~prec stack e in
          let stack' = push_rw x v stack' in
          fold stack' lst
     in
     let stack = fold stack lst in
     let stack, v = comp ~prec stack c in
     pop stack (List.length lst), v

  | Syntax.Let (lst, c) ->
     let rec fold stack' = function
       | [] -> stack'
       | (x, e) :: lst ->
          let v = comp_ro_value ~prec stack e in
          let stack' = push_ro x v stack' in
          fold stack' lst
     in
     let stack = fold stack lst in
     let stack, v = comp ~prec stack c in
     pop stack (List.length lst), v

  | Syntax.Assign (k, e) ->
     begin match lookup_ref k stack with
     | None -> Runtime.error ~loc Runtime.CannotWrite
     | Some r ->
        let v = comp_ro ~prec stack e in
        begin match Value.computation_as_value v with
        | None -> Runtime.error ~loc Runtime.ValueExpected
        | Some v -> r := v ;
                    stack, Value.CNone
        end
     end

  | Syntax.Lim (x, e) ->
     let stack' = push_ro x (Value.VInteger (Mpzf.of_int prec)) stack in
     let v = comp_ro ~prec stack' e in
     begin match Value.computation_as_real v with
     | None -> Runtime.error ~loc:e.Location.loc Runtime.RealExpected
     | Some r ->
           let err = Dyadic.shift ~prec ~round:Dyadic.up Dyadic.one (-prec) in
           let rl = Dyadic.sub ~prec ~round:Dyadic.down (Real.lower r) err
           and ru = Dyadic.add ~prec ~round:Dyadic.up (Real.upper r) err in
           let r = Real.make rl ru in
           stack, Value.CReal r
     end
  end

and comp_ro ~prec stack c : Value.result = snd (comp ~prec (make_ro stack) c)

and comp_ro_value ~prec stack c =
  as_value ~loc:(c.Location.loc) (comp_ro ~prec stack c)

let topcomp ~max_prec stack c =
  let rec loop prec =
    if prec > max_prec
    then
      None
    else begin
        try
          Some (comp_ro ~prec stack c)
        with
          Runtime.Abort ->
          Format.eprintf "<Loss of precision at %d>@." prec ;
          let prec = (prec * 3) / 2 + 1 in
          loop prec
      end
  in
  match loop !Config.init_prec with
  | Some v -> v
  | None -> Runtime.error ~loc:(c.Location.loc) Runtime.PrecisionLoss

let toplet_clauses stack lst =
  let rec fold stack' vs = function
    | [] -> stack', List.rev vs
    | (x, e, t) :: lst ->
       let v = topcomp ~max_prec:!Config.max_prec stack e in
       let v = as_value ~loc:(e.Location.loc) v in
       let stack' = push_ro x v stack' in
       let vs = v :: vs in
       fold stack' vs lst
  in
  fold stack [] lst

let topfun stack xs c =
  let g ~loc ~prec vs =
    try
      comp_ro ~prec (push_ros xs vs stack) c
    with
    | Error {Location.data=err; loc=loc'} ->
       raise (Error (Location.locate ~loc:loc' (CallTrace (loc, err))))
  in
  push_fun g stack

let topexternal ~loc stack s =
  match External.lookup s with
  | None -> error ~loc (UnknownExternal s)
  | Some g ->
     let h ~loc ~prec vs =
       try
         g ~prec vs
       with
       | Error {Location.data=err; loc=loc'} -> raise (Error (Location.locate ~loc:loc' (CallTrace (loc, err))))
     in
     push_fun h stack

let rec toplevel ~quiet runtime {Location.data=c; Location.loc} =
  match c with
  | Syntax.TyTopDo (c, t) ->
     let v = topcomp ~max_prec:!Config.max_prec runtime c in
     if not quiet then
       begin match t with
       | Type.Command -> ()
       | Type.Data dt ->
          Format.printf "%t : %t@."
            (Value.print_result v)
            (Type.print_valty dt)
       end ;
     runtime

  | Syntax.TyTopFunction (f, xts, c, t) ->
     let runtime = topfun runtime (List.map fst xts) c in
     if not quiet then
       Format.printf "function %s : %t@." f (Type.print_funty (List.map snd xts, t)) ;
     runtime

  | Syntax.TyTopExternal (f, s, ft) ->
     let runtime = topexternal ~loc runtime s in
     if not quiet then
       Format.printf "external %s : %t@." f (Type.print_funty ft) ;
     runtime

  | Syntax.TyTopFile cmds ->
     topfile ~quiet runtime cmds

  | Syntax.TyTopPrecision p ->
     Config.init_prec := p ;
     if not quiet then
       Format.printf "precision set to %d@." p ;
     runtime

and topfile ~quiet runtime = function
  | [] -> runtime
  | cmd :: cmds ->
     let runtime = toplevel ~quiet runtime cmd in
     topfile ~quiet runtime cmds
