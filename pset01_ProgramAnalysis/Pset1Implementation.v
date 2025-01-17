(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 1 *)

(* Welcome to 6.822!  Read through `Pset1Signature.v` before starting here. *)

Require Import Frap Pset1Signature.

Module Impl.
  (* The first part of this assignment involves the [bool] datatype,
   * which has the following definition.
   * <<
       Inductive bool :=
       | true
       | false.
     >>
   * We will define logical negation and conjunction of Boolean values,
   * and prove some properties of these definitions.
   *)

  (* Define [Neg] so that it implements Boolean negation, which flips
   * the truth value of a Boolean value.
   *)
  Definition Neg (b : bool) : bool :=
      match b with
      | true => false
      | false => true
      end.

  (* For instance, the negation of [true] should be [false].
   * This proof should follow from reducing both sides of the equation
   * and observing that they are identical.
   *)
  Theorem Neg_true : Neg true = false.
  Proof.
      equality.
  Qed.

  (* Negation should be involutive, meaning that if we negate
   * any Boolean value twice, we should get the original value back.

   * To prove a fact like this that holds for all Booleans, it suffices
   * to prove the fact for both [true] and [false] by using the
   * [cases] tactic.
   *)
  Theorem Neg_involutive : forall b : bool, Neg (Neg b) = b.
  Proof.
      intros.
      cases b.
      - simplify.
        equality.
      - simplify.
        equality.
  Qed.

  (* Define [And] so that it implements Boolean conjunction. That is,
   * the result value should be [true] exactly when both inputs
   * are [true].
   *)
  Definition And (x y : bool) : bool :=
      match x, y with
      | true, true => true
      | _,_ => false
      end.

  (* Here are a couple of examples of how [And] should act on
   * concrete inputs.
   *)
  Theorem And_true_true : And true true = true.
  Proof.
      simplify.
      equality.
  Qed.

  Theorem And_false_true : And false true = false.
  Proof.
    simplify.
    equality.
  Qed.

  (* Prove that [And] is commutative, meaning that switching the order
   * of its arguments doesn't affect the result.
   *)
  Theorem And_comm : forall x y : bool, And x y = And y x.
  Proof.
    intros.
    cases x.
    - cases y.
     + apply And_true_true.
     + apply And_false_true.
    - cases y.
     + simplify.
     equality.
     + equality.
  Qed.

  (* Prove that the conjunction of a Boolean value with [true]
   * doesn't change that value.
   *)
  Theorem And_true_r : forall x : bool, And x true = x.
  Proof.
      intros.
      cases x.
      - apply And_true_true.
      - apply And_false_true.
  Qed.

  (* In the second part of this assignment, we will work with a simple language
   * of imperative arithmetic programs that sequentially apply operations
   * to a natural-number-valued state.

   * The [Prog] datatype defines abstract syntax trees for this language.
   *)

  Print Prog.

  (* Define [run] such that [run p n] gives the final state
   * that running the program [p] should result in, when the
   * initial state is [n].
   *)
  Fixpoint run (p : Prog) (initState : nat) : nat :=
    match p with
    | Done => initState
    | AddThen n p => run p (n + initState)
    | MulThen n p => run p (n * initState)
    | DivThen n p => run p (initState / n)
    | VidThen n p => run p (n / initState)
    | SetToThen n p => run p n
    end.

  Compute Done.

  Compute run (AddThen 5 (AddThen 2 Done)) 12.


  Theorem run_Example1 : run Done 0 = 0.
  Proof.
      simplify.
      equality.
  Qed.

  Theorem run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
  Proof.
      simplify. 
      equality.
  Qed.

  Theorem run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
  Proof.
    simplify. 
    equality.
  Qed.

  (* Define [numInstructions] to compute the number of instructions
   * in a program, not counting [Done] as an instruction.
   *)
  Fixpoint numInstructions (p : Prog) : nat :=
  match p with
  | Done => 0
  | AddThen _ p => 1 + numInstructions p
  | MulThen _ p => 1 + numInstructions p
  | DivThen _ p => 1 + numInstructions p
  | VidThen _ p => 1 + numInstructions p
  | SetToThen _ p => 1 + numInstructions p
  end.

  Theorem numInstructions_Example :
    numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
  Proof.
      simplify.
      equality.
  Qed.

  (* Define [concatProg] such that [concatProg p1 p2] is the program
   * that first runs [p1] and then runs [p2].
   *)
  Fixpoint concatProg (p1 p2 : Prog) : Prog :=
    match p1 with
    | Done => p2
    | AddThen n p   => (AddThen n (concatProg p p2))
    | MulThen n p   => (MulThen n (concatProg p p2))
    | DivThen n p   => (DivThen n (concatProg p p2))
    | VidThen n p   => (VidThen n (concatProg p p2)) 
    | SetToThen n p => (SetToThen n (concatProg p p2))  
    end.

  Compute concatProg (AddThen 1 Done) (MulThen 2 Done).

  Theorem concatProg_Example :
       concatProg (AddThen 1 Done) (MulThen 2 Done)
       = AddThen 1 (MulThen 2 Done).
  Proof.
      simplify.
      equality.
  Qed.

  (* Prove that the number of instructions in the concatenation of
   * two programs is the sum of the number of instructions in each
   * program.
   *)
  Theorem concatProg_numInstructions
    : forall (p1 p2 : Prog), numInstructions (concatProg p1 p2)
                        = numInstructions p1 + numInstructions p2.
  Proof.
      intros.
      induct p1.
      induct p2.
      (* TODO: Way to automate this repetition? *)
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
  Qed.

  (* Prove that running the concatenation of [p1] with [p2] is
     equivalent to running [p1] and then running [p2] on the
     result. *)
  Theorem concatProg_run
    : forall (p1 p2 : Prog) (initState : nat),
      run (concatProg p1 p2) initState =
      run p2 (run p1 initState).
  Proof.
      intros.
      induct p1.
      induct p2.
      (* TODO: Way to automate this repetition? *)
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
      simplify. equality.
  Qed.

  (* Read this definition and understand how division by zero is handled. *)
  
  (* If we try to divide by zero at any time during the program execution we
     terminate the program execution, returning the current state at that point
     and boolean value of 'false', to indicate a division by zero error occurred. *)
  Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
    match p with
    | Done => (true, state)
    | AddThen n p => runPortable p (n+state)
    | MulThen n p => runPortable p (n*state)
    | DivThen n p =>
        if n ==n 0 then (false, state) else
        runPortable p (state/n)
    | VidThen n p =>
        if state ==n 0 then (false, 0) else
        runPortable p (n/state)
    | SetToThen n p =>
        runPortable p n
    end.
  Arguments Nat.div : simpl never. (* you don't need to understand this line *)

  (* Here are a few examples: *)

  Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
  Example runPortable_good : forall n,
    runPortable goodProgram1 n = (true, 10/(1+n)).
  Proof. simplify. equality. Qed.

  Definition badProgram1 := AddThen 0 (VidThen 10 Done).
  Example runPortable_bad : let n := 0 in
    runPortable badProgram1 n = (false, 0).
  Proof. simplify. equality. Qed.

  Definition badProgram2 := AddThen 1 (DivThen 0 Done).
  Example runPortable_bad2 : forall n,
    runPortable badProgram2 n = (false, 1+n).
  Proof. simplify. equality. Qed.

  (* Prove that running the concatenation [p] using [runPortable]
     coincides with using [run], as long as [runPortable] returns
     [true] to confirm that no divison by zero occurred. *)
  Lemma runPortable_run : forall p s0 s1,
    runPortable p s0 = (true, s1) -> run p s0 = s1.
  Proof.
      intros.
      induct p.
      simplify. equality.
      simplify. apply IHp. equality.
      simplify. apply IHp. equality.
      simplify. cases n. 
      simplify. equality.
      simplify. apply IHp. equality.
      simplify. cases s0. 
      simplify. equality.
      simplify. apply IHp. equality.
      simplify. apply IHp. equality.
  Qed.

  (* The final goal of this pset is to implement [validate : Prog -> bool]
     such that if this function returns [true], the program would not trigger
     division by zero regardless of what state it starts out in.  [validate] is
     allowed to return [false] for some perfectly good programs that never cause
     division by zero, but it must recognize as good the examples given below.  In
     jargon, [validate] is required to be sound but not complete, but "complete
     enough" for the use cases defined by the examples given here: *)

  Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
  Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
  Definition goodProgram4 := Done.
  Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
  Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
  Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).

  (* If you already see a way to build [validate] that meets the
   * requirements above, _and have a plan for how to prove it correct_,
   * feel free to just code away. Our solution uses one intermediate definition
   * and one intermediate lemma in the soundness proof -- both of which are more
   * sophisticated than the top-level versions given here. *)

  (* If a clear plan hasn't emerged in 10 minutes (or if you get stuck later),
   * take a look at the hints for this pset at the end of the signature file.
   * It is not expected that this pset is doable for everyone without the hints,
   * and some planning is required to complete the proof successfully.
   * In particular, repeatedly trying out different combinations of tactics
   * and ideas from hints until something sticks can go on for arbitrarily long
   * with little insight and no success; just guessing a solution is unlikely.
   * Thus, we encourage you to take your time to think, look at the hints when
   * necessary, and only jump into coding when you have some idea why it should
   * succeed. Some may call Coq a video game, but it is not a grinding contest. *)

  (* HINT 1 (see Pset1Signature.v) *)


  (* Data type representing an abstract program state. *)
  Inductive AbstractState := 
    | Zero              (* {0} *)
    | Positive          (* {1,2,3...} *)
    | ZeroOrPositive    (* {0,1,2,3...}*)
    | DivByZero.        (* special constructor for marking that a program may divide by zero. *)

  (* 
    To check whether a given program may divide by zero, for any possible
    initial state, we perform a basic form of symbolic execution.
    
    Specifically, we consider an abstraction of a concrete program state (a
    natural number) and only consider whether it is zero or nonzero, since this
    is the information needed to determine whether a divide by zero may occur.
    By propagating this information through via a symbolic execution, we can
    check whether we ever encounter a 'VidThen' instruction when the current
    state may possibly be zero. Additionally, we also check for the simpler case
    of encountering a 'DivThen 0 p' instruction, which means that a program
    always has the potential to divide by zero.  
  *)
  Fixpoint symbolicEval (p : Prog) (absState : AbstractState) : AbstractState :=
    match p with
      | Done => absState
      | AddThen n p  => symbolicEval p (if n ==n 0 then absState else Positive)
      | MulThen n p  => symbolicEval p (if n ==n 0 then Zero else absState)
      | DivThen n p  => (* state / n *)
            if n ==n 0 then DivByZero else
            (* p/1 won't change the abstract state for any value p. *)
            (symbolicEval p (if n ==n 1 then absState else Zero))
      | VidThen n p  => (* n / state *)
        match absState with
        | Zero 
        | ZeroOrPositive
        | DivByZero => DivByZero (* state is zero means we hit a divide by zero error. *) 
        (* dividing by any positive number larger than n could run us to zero, so we err 
           on the conservative side and simply propagate Zero. *)
        | Positive => (symbolicEval p Zero)
        end
      | SetToThen n p => symbolicEval p (if n ==n 0 then Zero else Positive)
    end.

  Definition validate (p : Prog) : bool := 
    (* Programs always start with some unknown natural number, 
       so the abstract initial state is always zero or positive. *)
    match (symbolicEval p ZeroOrPositive) with
        | Zero
        | Positive
        | ZeroOrPositive => true
        | DivByZero => false
    end.
  
  (* TODO: Fill in this function definition.. *)
  (* Fixpoint validate' (p : Prog) : bool :=
  end. *)

  Definition myProgram1 := AddThen 0 (AddThen 0 Done).

  Compute validate myProgram1.
  Compute validate goodProgram2.
  Compute validate goodProgram3.
  Compute validate goodProgram4.
  Compute validate goodProgram5.
  Compute validate badProgram1. 
  Compute validate badProgram2.

  (* Start by making sure that your solution passes the following tests, and add
   * at least one of your own tests: *)

  Example validate1 : validate goodProgram1 = true. Proof. equality. Qed.
  Example validate2 : validate goodProgram2 = true. Proof. equality. Qed.
  Example validate3 : validate goodProgram3 = true. Proof. equality. Qed.
  Example validate4 : validate goodProgram4 = true. Proof. equality. Qed.
  Example validate5 : validate goodProgram5 = true. Proof. equality. Qed.
  Example validate6 : validate goodProgram6 = true. Proof. equality. Qed.
  Example validate7 : validate goodProgram7 = true. Proof. equality. Qed.
  Example validateb1 : validate badProgram1 = false. Proof. equality. Qed.
  Example validateb2 : validate badProgram2 = false. Proof. equality. Qed.

  (* Then, add your own example of a bad program here, and check that `validate`
   * returns `false` on it: *)

  Definition badProgram3 : Prog := AddThen 1 (VidThen 10 (MulThen 0 (VidThen 10 Done))).
  Definition badProgram4 : Prog := SetToThen 0 ((MulThen 0 (VidThen 10 Done))).
  Definition badProgram5 : Prog := AddThen 1 (VidThen 0 (MulThen 0 (VidThen 10 Done))).
  Definition badProgram6 : Prog := AddThen 1 (DivThen 3 (VidThen 1 Done)).
  Definition goodProgram6a : Prog := AddThen 1 (DivThen 1 (VidThen 1 Done)).

  Example validateb3 : validate badProgram3 = false. Proof. equality. Qed.
  Example validateb4 : validate badProgram4 = false. Proof. equality. Qed.
  Example validateb5 : validate badProgram5 = false. Proof. equality. Qed.
  Example validateb6 : validate badProgram6 = false. Proof. equality. Qed.
  Example validateb6a : validate goodProgram6a = true. Proof. equality. Qed.

  (* HINTs 2-6 (see Pset1Signature.v)  *)

  (* Finally, before diving into the Coq proof, try to convince yourself that
   * your code is correct by applying induction by hand.  Can you describe the
   * high-level structure of the proof?  Which cases will you have to reason
   * about?  What do the induction hypotheses look like?  Which key lemmas do
   * you need?  Write a short (~10-20 lines) informal proof sketch before
   * proceeding. *)

  (** Proof sketch: **)
  (* 
  
  Our goal is to prove that, if our validate function returns true, then
  'runPortable' will run without a divide by zero error, and its output will be
  equivalent to the output of running the standard 'run' function on the given
  program. This consists of two main subgoals. We want to prove that if validate
  returns true, then:

    (1) 'runPortable' runs without a divide by zero error.
    (2) 'runPortable' returns the same result as 'run'.

  Proving (1) is our main task, since, once that is proved, we can use the
  previously established lemma 'runPortable_run' to prove (2), since that lemma
  establishes that if 'runPortable' returns true, then its output is equivalent
  to 'run'. 
  
  To prove (1), we focus on establishing a key lemma, stated as
  'symbolicEval_sound', which proves a property of the helper function
  'symbolicEval'. Basically, we need to show that if 'symbolicEval p
  ZeroOrPositive' does NOT return a DivByZero result, then 'runPortable p s'
  should return true, for any given input s. Since the 'validate' function uses
  'symbolicEval' for its core logic, proving this is mostly sufficient to
  establish (1).
  
  We can prove 'symbolicEval_sound' by induction on the program 'p'. That is, we
  need to show that, given a program p, if symbolicEval hasn't encountered a
  DivByZero up to the current point and runPortable hasn't either, then if
  'symbolicEval (XThen p) ZeroOrPositive' doesn't return a DivByZero, then
  neither does 'runPortable (XThen p) s', where XThen represents any possible
  program instruction. 
  
  We use an auxiliary lemma statement, 'symbolicEval_sound_strong', which
  strengthens the induction hypothesis in order to prove 'symbolicEval_sound'.
  The induction hypothesis for this lemma consists of 3 main facts, for any
  program p:

  - if symbolicEval p ZeroOrPositive <> DivByZero, then runPortable returns without error.
  - if symbolicEval p Positive <> DivByZero, then runPortable run with positive input returns without error.
  - if symbolicEval p Zero <> DivByZero, then runPortable returns without error.
  
  *)

  (* Now you're ready to write the proof in Coq: *)

  (* Key soundness helper lemma, using a strengthened lemma statement. *)
  Lemma symbolicEval_sound_strong : 
    forall p, 
        ((symbolicEval p ZeroOrPositive <> DivByZero) -> forall s, fst (runPortable p s) = true) /\
        ((symbolicEval p Positive <> DivByZero) -> forall s, s <> 0 -> fst (runPortable p s) = true) /\
        ((symbolicEval p Zero <> DivByZero) -> forall s, fst (runPortable p s) = true).
        simplify.
        induct p.

        (* Done *)
        - simplify. equality.
        
        (* AddThen n p *)
        - simplify. split; cases n; simplify.
            + equality.
            + cases IHp. cases H1. apply H1. equality. linear_arithmetic.
            + split.
              cases IHp. cases H0. apply H0. 
              equality.
            + split. cases IHp. 
              cases H0. simplify. apply H0. equality. 
              linear_arithmetic.
              cases IHp. cases H0. simplify. apply H0. simplify. equality. linear_arithmetic.
        
        (* MulThen n p *)
        - simplify. split; cases n; cases IHp; cases H0; simplify.
            + apply H1. equality.
            + apply H. equality.
            + split;simplify.
              apply H1. equality.
              apply H1. equality. 
            + split;simplify.
              apply H0. equality. linear_arithmetic.
              apply H1. equality.
        
        (* DivThen n p *)
        - split; simplify; cases IHp; simplify; try split.
            + cases (n ==n 0).
                * simplify. equality.
                * cases (n ==n 1). simplify. apply H0. equality.
                  simplify. cases H1. apply H2. equality.
            + simplify. cases (n ==n 0).
                * simplify. equality.
                * cases (n ==n 1). simplify. cases H0. apply H0. equality.
                  rewrite e. rewrite Nat.div_1_r. equality. 
                  cases H0. apply H3. equality.
            + simplify. cases (n ==n 0). 
                * equality.
                * cases (n ==n 1). 
                  cases H0. apply H2. equality.
                  cases H0. apply H2. equality.
        
        (* VidThen n p *)
        - split; simplify; cases IHp; try split; simplify.
            + cases H1. equality.
            + cases H0. cases (s ==n 0).
                * equality.
                * apply H3. equality.
            + cases H0. equality.
        
        (* SetToThen n p *)
        - split; simplify; cases IHp; try split; simplify.
            + cases (n ==n 0).
                * cases H1. apply H2. equality.
                * cases H1. apply H1. equality. equality.
            + cases (n ==n 0).
                * cases H0. apply H3. equality.
                * cases H0. apply H0. equality. equality.
            + cases (n ==n 0).
                * cases H0. apply H2. equality.
                * cases H0. apply H0. equality. equality.
    Qed.

    (* Key soundness lemma. If symbolicEval does not report a divide by zero, 
      then 'runPortable' doesn't. *)
    Lemma symbolicEval_sound : 
    forall p, 
        ((symbolicEval p ZeroOrPositive <> DivByZero) ->
        forall s, fst (runPortable p s) = true).
        apply symbolicEval_sound_strong.
    Qed.

  (* symbolicEval does not return a DivByZero error iff 'validate'
     returns true. *)
  Lemma symbolicEval_implies_validate : 
    forall p, (symbolicEval p ZeroOrPositive <> DivByZero) <->
              (validate p) = true.
    simplify.
    unfold validate.
    cases (symbolicEval p ZeroOrPositive).
    - simplify. equality. 
    - simplify. equality.
    - simplify. equality.
    - simplify. equality.
  Qed.

  (* Simple helper lemma that essentially states the basic fact that 
     P = (fst P, snd P), for a pair P. *)
  Lemma tup_eq : 
    forall s, forall p, (runPortable p s) = (fst (runPortable p s), snd (runPortable p s)).
    simplify.
    cases (runPortable p s).
    f_equal.
  Qed.

  (* If validate returns true, then runPortable should return true. *)
  Lemma validate_sound_fst : forall p, validate p = true ->
    (forall s, fst (runPortable p s) = true).
    simplify. apply symbolicEval_implies_validate in H as HN.
    apply symbolicEval_sound. equality. 
  Qed.

  Lemma runPortable_run_aux2 :  
  forall p s0 s1,   
      (fst (runPortable p s0) = true) -> (snd (runPortable p s0) = s1 -> (run p s0) = s1).
  Proof.
      simplify.
    apply runPortable_run.
    simplify.
    rewrite tup_eq.
    f_equal.
    equality.
    equality.
  Qed.

  Lemma runPortable_run_strong : forall p s0 s1,
  fst (runPortable p s0) = true -> ((snd (runPortable p s0) = s1) <-> (run p s0) = s1).
  Proof.  
    simplify. split.
    apply runPortable_run_aux2. equality.
    simplify. induct p.
    - simplify. equality.
    - simplify. apply IHp. equality. equality.
    - simplify. apply IHp. equality. equality.
    - simplify. cases n. simplify. equality. simplify. apply IHp. simplify. equality. simplify. equality.
    - simplify. cases s0. simplify. equality. simplify. apply IHp. simplify. equality. equality.
    - simplify. apply IHp. simplify. equality. equality.
  Qed.

  Lemma runPortable_run_strong2 : forall p s0,
  fst (runPortable p s0) = true -> ((snd (runPortable p s0)) = (run p s0)).
  Proof.  
    simplify. apply runPortable_run_strong. simplify. equality.
    simplify. equality.
  Qed.

  Lemma validate_sound_snd : 
    forall p, validate p = true ->
        forall s, snd (runPortable p s) = (run p s).
    simplify.
    apply validate_sound_fst with (s:=s) in H.
    apply runPortable_run_strong2. equality.
  Qed.

  Lemma validate_sound : forall p, validate p = true ->
    forall s, runPortable p s = (true, run p s).
    simplify.
    rewrite tup_eq. 
    rewrite pair_equal_spec.
    split.
    apply validate_sound_fst. equality.
    apply validate_sound_snd. equality.
  Qed.

  (* Here is the complete list of commands used in one possible solution:
    - Search, for example Search (_ + 0).
    - induct, for example induct x
    - simplify
    - propositional
    - equality
    - linear_arithmetic
    - cases, for example cases (X ==n Y)
    - apply, for example apply H
    - apply in, for example apply H1 in H2 or apply somelemma in H1
    - apply with, for example apply H1 with (x:=2)
    - apply in with, for example apply H1 with (x:=2) in H2
    - rewrite, for example rewrite H
    - rewrite in, for example rewrite H1 in H2 or rewrite somelemma in H1
    - ;, for example simplify; propositional *)
End Impl.

(* The following line checks that your `Impl` module implements the right
   signature.  Make sure that it works, or the auto-grader will break!
   If there are mismatches, Coq will report them (`Signature components for
   label … do not match`): *)
Module ImplCorrect : Pset1Signature.S := Impl.
