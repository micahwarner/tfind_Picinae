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
  Variable x20 x21 : N     (* tolower: R_X20, R_X21 (callee-save regs) *).

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

    (* loop invariant *)
    | 0x100020 => Inv 1 (
      )

    (* case-equal, non-null characters found *)
    | 0x100034 => Inv 1 (
    
      )

    (* tfind return site *)
    | 0x10005c => Post 1 (postcondition s)

    | _ => NoInv
    end.

