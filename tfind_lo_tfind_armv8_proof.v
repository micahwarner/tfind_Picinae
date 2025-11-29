Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv8_pcode.
Require Import tfind_lo_tfind_armv8.

Import ARM8Notations.
Open Scope N.
Open Scope bool.

Definition tfind_exit (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x10005c => true
  | _ => false
  end | _ => false end.

(* tfind_lo_tfind_armv8 *)

(* tfind does not corrupt memory. *)
Theorem tfind_preserves_memory:
  forall_endstates tfind_lo_tfind_armv8 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

(* tfind does not corrupt the LR register (call-return safety). *)
Theorem tfind_preserves_lr:
  forall_endstates tfind_lo_tfind_armv8 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.


Section Invariants.

  Variable sp : N          (* initial stack pointer *).
  Variable mem : memory    (* initial memory state *).
  Variable raddr : N       (* return address (R_X30) *).
  Variable arg1 : N        (* tfind: 1st pointer arg (R_X0)
                              callback signature *).
  Variable arg2 : N        (* tfind: 2nd pointer arg (R_X1)
                              root node pointer *).
  Variable arg3 : N        (* tfind: 3rd pointer arg (R_X2)
                              address of subroutine*).
  Variable x20 x21 : N     (* R_X20, R_X21 (callee-save regs) *).

  Definition mem' fbytes := setmem 64 LittleE 40 mem (sp ⊖ 48) fbytes.

  Definition postcondition (s:store) :=
    ∃ n k fb,
      s V_MEM64 = mem' fb /\
      s R_X0 = n /\ (n=0 -> (mem' fb) Ⓑ[arg1+k] = 0).
  
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* tfind entry point *)
    | 0x100000 => Inv 1 (
        s R_SP = sp /\ s V_MEM64 = mem /\
        s R_X0 = arg1 /\ s R_X1 = arg2 /\ s R_X2 = arg3
      )
        (* X1 Parameter Validation *)
    | 0x100010 => Inv 1 (∃ fb k,
      s R_SP = sp ⊖ 48 /\ s V_MEM64 = mem' fb /\
      s R_X19 = arg2 ⊕ k /\ s R_X20 = arg1 ⊕ k /\ s R_X21 = arg3 ⊕ k
      )
      
    (* loop invariant *)
    | 0x100020 => Inv 1 (∃ fb k,
      s R_SP = sp ⊖ 48 /\ s V_MEM64 = mem' fb /\
      s R_X19 = arg2 ⊕ k /\ s R_X20 = arg1 ⊕ k /\ s R_X21 = arg3 ⊕ k
      )

    (* case-equal, non-null characters found (successful find)*)
    | 0x100034 => Inv 1 (∃ fb k,
      s R_SP = sp ⊖ 48 /\ s V_MEM64 = mem' fb /\
      s R_X19 = arg2 ⊕ k /\ s R_X20 = arg1 ⊕ k /\ s R_X21 = arg3 ⊕ k
      )

    (* tfind return site *)
    | 0x10005c => Post 1 (postcondition s)

    | _ => NoInv
    end.

  Definition invs1 := make_invs 1 tfind_lo_tfind_armv8 invs.
  Definition exits1 := make_exits 1 tfind_lo_tfind_armv8 invs.
  
End Invariants.

Search "satisfies_all".

(* Create a step tactic that prints a progress message (for demos). *)
Ltac step := time arm8_step.

Theorem tfind_partial_correctness:
  forall s sp mem t s' x' arg1 arg2 arg3 a'
         (ENTRY: startof t (x',s') = (Addr 0x100000, s))
         (MDL: models arm8typctx s)
         (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = a')
         (RX0: s R_X0 = arg1) (RX1: s R_X1 = arg2) (RX2: s R_X2 = arg3),
          satisfies_all tfind_lo_tfind_armv8 
                           (invs1  sp mem arg1 arg2 arg3)
                           (exits1 sp mem arg1 arg2 arg3) ((x',s')::t).
Proof.
  (* Use prove_invs to initiate a proof by induction. *)
  intros. apply prove_invs.
  (* Base case: The invariant at the subroutine entry point is satisfied. *)
  simpl. rewrite ENTRY. step. repeat split; assumption.
  
  (* Change assumptions about s into assumptions about s1. *)
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply welltyped. intro MDL1.
  set (x20 := s R_X20) in *. set (x21 := s R_X21) in *. clearbody x20 x21.
  clear - PRE MDL1. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  
  (* Break the proof into cases, one for each internal invariant-point. *)
  destruct_inv 64 PRE.
  
  (* Address 100000: tfind entry point *)
  destruct PRE as (MEM & SP & X0 & X1 & X3).  
  step. step. step. step.
  generalize_frame mem as fb.
  exists fb, 0. psimpl. split.
  reflexivity. 
Qed.
