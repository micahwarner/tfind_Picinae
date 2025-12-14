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
  Variable arg1 : N        (* tfind: 1st pointer arg (R_X0)
                              desired index *).
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
      s R_X0 = arg1 ⊕ k /\ s R_X1 = arg2 ⊕ k /\ s R_X2 = arg3 ⊕ k
      )
      
    (* loop invariant *)
    | 0x100020 => Inv 1 (∃ fb k,
      s R_SP = sp ⊖ 48 /\ s V_MEM64 = mem' fb /\
      s R_X19 = mem' fb Ⓠ[arg2+k] /\ s R_X20 = arg1 ⊕ k /\ s R_X21 = arg3 ⊕ k
      )

    (* case-equal, non-null characters found (successful find)*)
    | 0x100034 => Inv 1 (∃ fb k,
      s R_SP = sp ⊖ 48 /\ s V_MEM64 = mem' fb /\
      s R_X19 = mem' fb Ⓠ[arg2+k] /\ s R_X20 = arg1 ⊕ k /\ s R_X21 = arg3 ⊕ k
      )
      
    (* 0x100048: Just before the "not found" path completes; stack frame and saved registers intact. *)
    | 0x100048 => Inv 1 (∃ fb,
      s R_SP = sp ⊖ 48 /\
      s V_MEM64 = mem' fb /\ (s R_X1 = 0 \/ s R_X19 = 0)
    )

  (* 0x10004c: After executing `mov x19,#0` (or arriving from cbz), x19 holds the final result value. *)
  | 0x10004c => Inv 1 (∃ n k fb,
      s R_SP = sp ⊖ 48 /\
      s V_MEM64 = mem' fb /\
      s R_X19 = n /\             (* result in x19 (or 0 if not found) *)
      s R_X20 = arg1 ⊕ k /\
      s R_X21 = arg3 ⊕ k
    )

  (* 0x100050: After `mov x0,x19`, the function result is now placed in x0 for return. *)
  | 0x100050 => Inv 1 (∃ n k fb,
      s R_SP = sp ⊖ 48 /\
      s V_MEM64 = mem' fb /\
      s R_X0 = n /\ s R_X19 = n /\
      s R_X20 = arg1 ⊕ k /\
      s R_X21 = arg3 ⊕ k
    )

    (* tfind return site *)
    | 0x10005c => Post 1 (postcondition s)

    | _ => NoInv
    end.

  Definition invs1 := make_invs 1 tfind_lo_tfind_armv8 invs.
  Definition exits1 := make_exits 1 tfind_lo_tfind_armv8 invs.
  
End Invariants.

Search "satisfies_all".

Require Import Coq.Lists.List. 
Require Import Coq.Bool.Bool.
Import ListNotations.

Fixpoint path_moreleft (p q : list bool) : bool := (* check if path p is more left than path q*)
  match p, q with
  | [], [] => true
  | [], b :: qs => b               (* [] ≤ (b::qs) iff b = true *)
  | b :: ps, [] => negb b          (* (b::ps) ≤ [] iff b = false *)
  | b1 :: ps, b2 :: qs =>
      if Bool.eqb b1 b2 then path_moreleft ps qs
      else negb b1                 (* false < true → negb false = true; negb true = false *)
  end.
  
Compute path_moreleft [] [false].   (*p is root, q is left child of root, = false *)
Compute path_moreleft [] [true].    (*p is root, q is right child of root, = true  *)
Compute path_moreleft [false] [].   (*p is left child of root, q is root, = true  *)
Compute path_moreleft [false] [false; false]. (*p is first left child of root, q is left child of p, = false *)
Compute path_moreleft [false; true] [false].  (*p is right child of q, q is left child of root = false *)

(* Reflexivity: p <= p *)
Theorem path_moreleft_refl : forall p, path_moreleft p p = true.
Proof.
  induction p as [ | b p IH ].
  - simpl. reflexivity.
  - simpl. replace (Bool.eqb b b) with true.
    * apply IH.
    * destruct b; simpl; reflexivity.
Qed.

(* Antisymmetry: if p ≤ q and q ≤ p then p = q *)
Theorem path_moreleft_antisym : forall p q,
  path_moreleft p q = true ->
  path_moreleft q p = true ->
  p = q.
Proof.
  induction p as [ | b1 p IH ]; intros [ | b2 q ] Hpq Hqp; simpl in *.
  - reflexivity.
  - (* p = [], q = b2 :: q *)
    destruct b2; simpl in *; try discriminate.
  - (* p = b1 :: p, q = [] *)
    destruct b1; simpl in *; try discriminate.
  - (* p = b1 :: p, q = b2 :: q *)
    destruct (Bool.eqb b1 b2) eqn:Heq12.
    + (* heads equal *) 
    apply eqb_prop in Heq12.
    f_equal.
      * apply Heq12.
      * apply IH.
        -- exact Hpq.
        -- rewrite Heq12 in Hqp. replace (Bool.eqb b2 b2) with true in Hqp.
           apply Hqp. destruct b2; reflexivity.
    + (* heads differ - impossible *)
    simpl in Hpq, Hqp.
    destruct b1; destruct b2; simpl in *; try discriminate.
Qed.

(* Totality: for any p,q either p ≤ q or q ≤ p *)
Theorem path_moreleft_total : forall p q,
  path_moreleft p q = true \/ path_moreleft q p = true.
Proof.
  induction p as [ | b p IH ]; intros [ | c q ]; simpl.
  - left. reflexivity. (* [], [] *)
  - (* p = [], q = c::q *) 
    destruct c.
    + left. simpl. reflexivity.
    + right. simpl. reflexivity.
  - (* p = b::p, q = [] *) 
    destruct b.
    + right. simpl. reflexivity.
    + left. simpl. reflexivity.
  - (* p = b::p, q = c::q *)
    destruct (Bool.eqb b c) eqn:Eb.
    + (* b = c *)
    apply eqb_prop in Eb. subst c.
    destruct (IH q) as [H|H].
      * left. exact H.
      * right. replace (Bool.eqb b b) with true. simpl. exact H.
        destruct b; simpl; reflexivity.
    + (* b <> c *) 
      destruct b, c; simpl in *; try contradiction; auto.
Qed.

Inductive ValueAt
          (w : bitwidth) (e : endianness) (len : bitwidth)
          (m : memory) (addr : addr)
  : list bool -> N -> Prop :=
| VA_nil
    (H0 : addr <> 0) :
    ValueAt w e len m addr nil (getmem w e len m addr)
| VA_left
    (H0 : addr <> 0)
    (p : list bool) (v : N)
    (H1 : ValueAt w e len m (addr + 8) p v) :
    ValueAt w e len m addr (false :: p) v
| VA_right
    (H0 : addr <> 0)
    (p : list bool) (v : N)
    (H1 : ValueAt w e len m (addr + 16) p v) :
    ValueAt w e len m addr (true :: p) v.

Definition cmp_fun := memory -> N -> N -> N.

(* interpretation convention: result = 0 means "the relation holds" *)
Definition cmp_result_rel (cmp : cmp_fun) (m : memory) : N -> N -> Prop :=
  fun x y => cmp m x y = 0.

Definition sorted_tree
           (w : bitwidth) (e : endianness) (len : bitwidth)
           (m : memory) (addr : addr) (cmp : cmp_fun): Prop :=
  let rel := cmp_result_rel cmp m in
  forall p1 p2 v1 v2,
    path_moreleft p1 p2 = true ->
    ValueAt w e len m addr p1 v1 ->
    ValueAt w e len m addr p2 v2 ->
    rel v1 v2.

(* Every node is trivially “sorted” relative to itself; its value is always ≤ itself. *)
Theorem sorted_tree_refl :
  forall w e len m addr p v (cmp : cmp_fun),
    sorted_tree w e len m addr cmp ->
    (forall x, cmp_result_rel cmp m x x) ->
    path_moreleft p p = true /\ cmp_result_rel cmp m v v.
Proof.
  intros w e len m addr p v Hval Hsorted.
  split.
  - apply path_moreleft_refl.
  - apply H.
Qed.

(* If two paths are mutually “more-left” than each other, 
they must be the same path, so their values are equal. *)
Theorem sorted_tree_antisym :
  forall w e len m addr p q v1 v2 (cmp : cmp_fun),
    ValueAt w e len m addr p v1 ->
    ValueAt w e len m addr q v2 ->
    sorted_tree w e len m addr cmp ->
    path_moreleft p q = true ->
    path_moreleft q p = true ->
    (forall x y, cmp_result_rel cmp m x y -> cmp_result_rel cmp m y x -> x = y) ->
    p = q /\ v1 = v2.
Proof.
  intros w e len m addr p q v1 v2 cmp Hval1 Hval2 Hsorted Hpq Hqp Hcmp_antisym.
  (* paths equal by antisymmetry of path_moreleft *)
  assert (p = q) as Heq.
  { apply path_moreleft_antisym; assumption. }
  split; [assumption|].
  (* values are comparable by the sorted_tree property *)
  unfold sorted_tree in Hsorted. simpl in Hsorted.
  assert (cmp_result_rel cmp m v1 v2) as H12.
  { apply Hsorted with (p1 := p) (p2 := q); assumption. }
  assert (cmp_result_rel cmp m v2 v1) as H21.
  { apply Hsorted with (p1 := q) (p2 := p); assumption. }
  (* use antisymmetry of the comparator relation to conclude equality *)
  specialize (Hcmp_antisym v1 v2 H12 H21). now subst.
Qed.

(* Any two nodes in the tree are comparable: the value at the more-left path is 
always ≤ the value at the more-right path. *)

Theorem sorted_tree_total :
  forall w e len m addr p q v1 v2 (cmp : cmp_fun),
    ValueAt w e len m addr p v1 ->
    ValueAt w e len m addr q v2 ->
    sorted_tree w e len m addr cmp ->
    (path_moreleft p q = true /\ cmp_result_rel cmp m v1 v2) \/
    (path_moreleft q p = true /\ cmp_result_rel cmp m v2 v1).
Proof.
  intros w e len m addr p q v1 v2 cmp Hval1 Hval2 Hsorted.
  destruct (path_moreleft_total p q) as [Hpq | Hqp].
  - left. split; [assumption | unfold sorted_tree in Hsorted; simpl; apply Hsorted with (p1:=p) (p2:=q); assumption].
  - right. split; [assumption | unfold sorted_tree in Hsorted; simpl; apply Hsorted with (p1:=q) (p2:=p); assumption].
Qed.


(* This needs to be edited to restrict a good callee to maintain certain registers/data *)
Definition callee_postcondition cmp (s s1: store) : Prop :=
    s V_MEM64 = s1 V_MEM64 /\ 
    s R_X19 = s1 R_X19 /\
    s R_X20 = s1 R_X20 /\
    s R_X21 = s1 R_X21 /\
    s R_SP = s1 R_SP /\
    s1 R_X0 = cmp (s V_MEM64) (s R_X0) (s R_X1).

Definition good_callee cmp (a:addr) := forall p inv xp s t,
    (forall s1 t1, callee_postcondition cmp s s1 ->
              nextinv p inv xp true ((Addr (s R_X30), s1) :: t1 ++ ((Addr a, s)::t))
    ) -> nextinv p inv xp true ((Addr a, s) :: t).

(* Create a step tactic that prints a progress message (for demos). *)
Ltac step := time arm8_step.

Theorem tfind_partial_correctness:
  forall s sp mem t s' x' arg1 arg2 arg3 a'
         (ENTRY: startof t (x',s') = (Addr 0x100000, s))
         (MDL: models arm8typctx s)
         (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = a')
         (RX0: s R_X0 = arg1) (RX1: s R_X1 = arg2) (RX2: s R_X2 = arg3)
         (cmp: N -> N -> N -> N)
         (H1: forall a, good_callee cmp a)
         (H: good_callee cmp arg3),
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
  clear - PRE MDL1 H H1 cmp. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  
  (* Break the proof into cases, one for each internal invariant-point. *)
  destruct_inv 64 PRE.
  
  (* Address 100000: tfind entry point *)
  (* destruct PRE as (MEM & SP & X0 & X1 & X3).  *)
  destruct PRE as (SP & MEM & X0 & X1 & X2).
  step. step. step. step.
  generalize_frame mem as fb.
  exists fb, 0. psimpl.
  repeat (split || assumption || reflexivity). (* solves by definition *)
  
  (* Address 100010: tfind Parameter Validation*)
  destruct PRE as (fb & k & SP & MEM & X0 & X1 & X2).
  step. 
    (* the root pointer is invalid / 0 *)
    exists fb. repeat (reflexivity || assumption || split). left. apply N.eqb_eq, BC.
    
    (* valid root pointer*)
    step. step. step. exists fb, k. repeat (reflexivity || assumption || split). 
    
  
  (* Address 100020: tfind main Loop*)  
  destruct PRE as (fb & k & SP & MEM & X19 & X20 & X21).
  step.
  
    (* invalid pointer at current node*)
  + exists fb. repeat (reflexivity || assumption || split). right. apply N.eqb_eq, BC.
  
    (* valid node main loop section with BLR call *)
  + step. step. step. apply H1. intros. unfold callee_postcondition in H0.
  step. exists fb, k. repeat (destruct H2 || destruct H0 || destruct H3). repeat (split || assumption).
  
  + destruct PRE as (fb & k & SP & MEM & X19 & X20 & X21).
  step.
  exists (s R_X19), k, fb.
  repeat (assumption || reflexivity || split).
  step. step. step. step.
  exists fb, k.
  repeat split.
  assumption.
  admit. (* Expression for child node calculation *)
  assumption.
  assumption.
  
  + destruct PRE as (fb & SP & MEM & zero).
  step. 
    
Qed.
