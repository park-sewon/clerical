(** Clerical typing judgments *)

Require Import Clerical.

Open Scope clerical_scope.

Inductive has_type : context -> comp -> result_type -> Type :=
  | has_type_Var :
    forall Γ s τ,
      in_context_t Γ s τ -> has_type Γ (VAR s) (RData τ)

  | has_type_True :
      forall Γ,
        has_type Γ TRUE RBoolean

  | has_type_False :
      forall Γ,
        has_type Γ FALSE RBoolean

  | has_type_Integer :
      forall Γ k,
        has_type Γ (INT k) RInteger

  | has_type_Skip :
      forall Γ,
        has_type Γ SKIP RCommand

  | has_type_Sequence :
      forall Γ c1 c2 ρ,
        has_type Γ c1 RCommand ->
        has_type Γ c2 ρ ->
        has_type Γ (c1 ;; c2)  ρ

  | has_type_while :
      forall Γ b c,
        has_type (readonly  Γ) b RBoolean ->
        has_type Γ c RCommand ->
        has_type Γ (WHILE b DO c END) RCommand

  | has_type_Case :
      forall Γ b1 c1 b2 c2 ρ,
        has_type (readonly Γ) b1 RBoolean ->
        has_type Γ c1 ρ ->
        has_type (readonly Γ) b2 RBoolean ->
        has_type Γ c2 ρ ->
        has_type Γ (MCASE b1 ==> c1 OR b2 ==> c2 END) ρ

  | has_type_newvar :
      forall Γ s ρ τ e c,
        (in_context Γ s -> False) ->
        has_type (readonly Γ) e (RData τ) ->
        has_type (add_rw Γ s τ) c ρ ->
        has_type Γ (NEWVAR s := e IN c) ρ

  | has_type_assign :
      forall Γ s τ e,
        in_context_trw Γ s τ true ->
        has_type (readonly Γ) e (RData τ) ->
        has_type Γ (SET s := e) RCommand
.


(* Type checker: given a context it judeges type. if the given computation is not well-typed, it
   leads to None. *)
Fixpoint judge_type (Γ : context) (c : comp) : option result_type :=
  match c with
  | Var s => match locate Γ s with
             | None => None
             | Some v => let (a,b,c) := v in Some (RData b)
             end 
  | Boolean b => Some RBoolean
  | Integer z => Some RInteger
  | BinOp op a b => let τ :=  binary_op_type op (rev_type (judge_type (readonly Γ) a))
                                                    (rev_type (judge_type (readonly Γ) b)) in
                    match τ with
                    | Some τ => Some ( RData τ )
                    | None => None
                    end
  | UniOp op a => let τ := (unary_op_type op (rev_type (judge_type (readonly Γ) a))) in
                  match τ with
                  | Some τ => Some ( RData τ )
                  | None => None
                  end
  | Skip => Some RCommand
  | Sequence c1 c2 => let τ := (judge_type Γ c1) in
                      match τ with
                      | Some τ => match τ with
                                  | RCommand => judge_type Γ c2
                                  | _ => None
                                  end
                      | _ => None
                      end
  | Case b1 c1 b2 c2 => let Γ' := readonly Γ in
                        let τ₁ := judge_type Γ' b1 in
                        let τ₂ := judge_type Γ' b2 in
                        match τ₁  with
                        | Some RBoolean =>
                          match τ₂ with
                            | Some RBoolean => let ρ₁ := judge_type Γ c1 in
                                                          let ρ₂ := judge_type Γ c2 in
                                                          match ρ₁, ρ₂ with
                                                          | Some ρ₁', Some ρ₂' => if (same_result_type ρ₁' ρ₂') then ρ₁ else None
                                                          | _, _ => None
                                                          end
                            | _ => None
                          end
                            
                        | _ => None
                        end
  | While b c => let τ := judge_type (readonly Γ) b in
                 match τ with
                 | Some RBoolean => let  ρ := judge_type Γ c in
                                    match ρ with
                                    | Some Rcommand => Some Rcommand
                                    | _ => None
                                    end
                 | _ => None
                 end
                   
  | Newvar s e c => if (is_in_context Γ s)
                    then None
                    else
                      let τ := judge_type (readonly Γ) e in
                      match τ with
                      | Some τ => match τ with
                                  | RData τ => judge_type (add_rw Γ s τ) c
                                  | _ => None
                                  end
                      | _ => None
                      end
  | Assign s e => let v := locate Γ s in
                  match v with
                  | Some v => let (a,b,c) := v in
                              if c then (
                                  let ρ := judge_type (readonly Γ) e in
                                  match ρ with
                                  | Some ρ => if (same_result_type ρ (RData b)) then Some RCommand else None
                                  | _ => None
                                  end)
                              else None
                  | _ => None
                  end
  end.

(* prove that the type judgement function is correct upto the inductive definition has_type *)
Theorem Type_judgement_is_correct : forall Γ c τ, has_type Γ c τ -> judge_type Γ c = Some τ.
Proof.
Admitted.


            







            
(* examples for type judgement *)
Section type_examples.
        
  Definition Example1 :=
    (
      NEWVAR "x1" := INT 0 IN (* the accumulator is VAR 1 *)
                         NEWVAR "x2" := VAR "x1" IN (* the counter is VAR 0 *)
                                            WHILE (VAR "x1" <z INT 101) DO
                                            (SET "x1" := (VAR "x2" +z VAR "x2") ;;
                                                                                 SET "x2" := VAR "x1" +z INT 1)
                                            END ;;
                                            VAR "x2"
    ).


    Definition Example2 :=
    (
      NEWVAR "x1" := INT 0 IN (* the accumulator is VAR 1 *)
                         NEWVAR "x2" := VAR "x1" IN (* the counter is VAR 0 *)
                                            WHILE (VAR "x1" <z INT 101) DO
                                            (SET "x1" := (VAR "x2" +z VAR "x2") ;;
                                                                                 SET "x2" := VAR "x1" +z INT 1)
                                            END
    ).


    (* Ill typed *)
    Definition Example3 :=
    (
      (NEWVAR "x1" := INT 0 IN (* the accumulator is VAR 1 *)
                         NEWVAR "x2" := VAR "x1" IN (* the counter is VAR 0 *)
                                            WHILE (VAR "x1" <z INT 101) DO
                                            (SET "x1" := (VAR "x2" +z VAR "x2") ;;
                                                                                 SET "x2" := VAR "x1" +z INT 1)
                                            END +z INT 5)
    ).


  

  Eval compute in judge_type empty_context Example3.

End type_examples.


