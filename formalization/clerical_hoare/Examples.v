Require Import ZArith.
Require Import Clerical.
(*Require Import OperationalSemantics.*)

Open Scope clerical_scope.

Definition Example1 :=
  (NEWVAR "x" := (INT 1 +z INT 2 +z INT 3) IN
          SET "x" := (VAR "x" +z VAR "x") ;;
          VAR "x" +z INT 10).

Definition Example2 :=
  (SKIP ;;
   WHEN (INT 5 <z INT 3) THEN
     INT 42
   ELSE
     INT 10 <z INT 22
   END
  ).

(* Compute the sum 1 + 2 + ... + 10. *)
Definition Example3 :=
  (
    NEWVAR (INT 0) IN (* the accumulator is VAR 1 *)
    NEWVAR (INT 1) IN (* the counter is VAR 0 *)
      WHILE (VAR 0 <z INT 101) DO
        (SET 1 := (VAR 1 +z VAR 0) ;;
        SET 0 := VAR 0 +z INT 1)
      END ;;
      VAR 1
  ).

Definition wait (n : Z) :=
  NEWVAR INT 0 IN
    WHILE (VAR 0 <z INT n) DO
      SET 0 := (VAR 0 +z INT 1)
    END.

Eval compute in (judge_type wait).