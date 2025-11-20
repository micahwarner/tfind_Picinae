(* Automatically generated with pcode2coq
arch: armv8
file: tfind.lo
function: tfind
*)

Require Import Picinae_armv8_pcode.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition tfind_lo_tfind_armv8 : program := fun _ a => match a with

(* 0x00100000: stp x29,x30,[sp, #-0x30]! *)
(*    1048576: stp x29,x30,[sp, #-0x30]! *)
| 0x100000 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x40e8, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X29) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x40f0, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X30) $;
	(* (register, 0x8, 8) INT_ADD (register, 0x8, 8) , (const, 0xffffffffffffffd0, 8) *)
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x8, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (register, 0x8, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100004: mov x29,sp *)
(*    1048580: mov x29,sp *)
| 0x100004 => Some (4,
	(* (register, 0x40e8, 8) COPY (register, 0x8, 8) *)
	Move R_X29 (Var R_SP)
)

(* 0x00100008: stp x19,x20,[sp, #0x10] *)
(*    1048584: stp x19,x20,[sp, #0x10] *)
| 0x100008 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4098, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X19) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x40a0, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X20) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x8, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x0010000c: str x21,[sp, #0x20] *)
(*    1048588: str x21,[sp, #0x20] *)
| 0x10000c => Some (4,
	(* (unique, 0x6500, 8) INT_ADD (register, 0x8, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x6500) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x6500, 8) , (register, 0x40a8, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6500)) (Cast CAST_LOW 64 (Var R_X21)) LittleE 8)
)

(* 0x00100010: cbz x1,0x00100048 *)
(*    1048592: cbz x1,0x00100048 *)
| 0x100010 => Some (4,
	(* (unique, 0x18f80, 1) INT_EQUAL (register, 0x4008, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x18f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X1) (Word 0x0 64))) $;
	(*  ---  CBRANCH (ram, 0x100048, 8) , (unique, 0x18f80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18f80))) (
		Jmp (Word 0x100048 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100014: ldr x19,[x1] *)
(*    1048596: ldr x19,[x1] *)
| 0x100014 => Some (4,
	(* (unique, 0x6800, 8) COPY (register, 0x4008, 8) *)
	Move (V_TEMP 0x6800) (Var R_X1) $;
	(* (register, 0x4098, 8) LOAD (const, 0x1b1, 8) , (unique, 0x6800, 8) *)
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6800)) LittleE 8)
)

(* 0x00100018: mov x20,x0 *)
(*    1048600: mov x20,x0 *)
| 0x100018 => Some (4,
	(* (register, 0x40a0, 8) COPY (register, 0x4000, 8) *)
	Move R_X20 (Var R_X0)
)

(* 0x0010001c: mov x21,x2 *)
(*    1048604: mov x21,x2 *)
| 0x10001c => Some (4,
	(* (register, 0x40a8, 8) COPY (register, 0x4010, 8) *)
	Move R_X21 (Var R_X2)
)

(* 0x00100020: cbz x19,0x00100048 *)
(*    1048608: cbz x19,0x00100048 *)
| 0x100020 => Some (4,
	(* (unique, 0x18f80, 1) INT_EQUAL (register, 0x4098, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x18f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X19) (Word 0x0 64))) $;
	(*  ---  CBRANCH (ram, 0x100048, 8) , (unique, 0x18f80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18f80))) (
		Jmp (Word 0x100048 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100024: ldr x1,[x19] *)
(*    1048612: ldr x1,[x19] *)
| 0x100024 => Some (4,
	(* (unique, 0x6800, 8) COPY (register, 0x4098, 8) *)
	Move (V_TEMP 0x6800) (Var R_X19) $;
	(* (register, 0x4008, 8) LOAD (const, 0x1b1, 8) , (unique, 0x6800, 8) *)
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x6800)) LittleE 8)
)

(* 0x00100028: mov x0,x20 *)
(*    1048616: mov x0,x20 *)
| 0x100028 => Some (4,
	(* (register, 0x4000, 8) COPY (register, 0x40a0, 8) *)
	Move R_X0 (Var R_X20)
)

(* 0x0010002c: blr x21 *)
(*    1048620: blr x21 *)
| 0x10002c => Some (4,
	(* (register, 0x0, 8) COPY (register, 0x40a8, 8) *)
	Move R_PC (Var R_X21) $;
	(* (register, 0x40f0, 8) INT_ADD (const, 0x10002c, 8) , (const, 0x4, 8) *)
	Move R_X30 (BinOp OP_PLUS (Word 0x10002c 64) (Word 0x4 64)) $;
	(*  ---  CALLIND (register, 0x0, 8) *)
	Jmp (Var R_PC)
)

(* 0x00100030: cmp w0,#0x0 *)
(*    1048624: cmp w0,#0x0 *)
| 0x100030 => Some (4,
	(* (unique, 0x1c980, 4) COPY (const, 0x0, 4) *)
	Move (V_TEMP 0x1c980) (Word 0x0 32) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (const, 0x0, 4) , (register, 0x4000, 4) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X0)))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4000, 4) , (const, 0x0, 4) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	(* (unique, 0x1ca80, 4) INT_SUB (register, 0x4000, 4) , (unique, 0x1c980, 4) *)
	Move (V_TEMP 0x1ca80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x1c980))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x1ca80, 4) , (const, 0x0, 4) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1ca80)) (Word 0x0 32))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x1ca80, 4) , (const, 0x0, 4) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1ca80)) (Word 0x0 32))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x00100034: cbz w0,0x0010004c *)
(*    1048628: cbz w0,0x0010004c *)
| 0x100034 => Some (4,
	(* (unique, 0x18f00, 1) INT_EQUAL (register, 0x4000, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x18f00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_X0)) (Word 0x0 32))) $;
	(*  ---  CBRANCH (ram, 0x10004c, 8) , (unique, 0x18f00, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18f00))) (
		Jmp (Word 0x10004c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100038: cset x1,gt *)
(*    1048632: cset x1,gt *)
| 0x100038 => Some (4,
	(* (unique, 0x2b80, 1) BOOL_NEGATE (register, 0x101, 1) *)
	Move (V_TEMP 0x2b80) (UnOp OP_NOT (Var R_ZR)) $;
	(* (unique, 0x2c00, 1) INT_EQUAL (register, 0x100, 1) , (register, 0x103, 1) *)
	Move (V_TEMP 0x2c00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_NG) (Var R_OV))) $;
	(* (unique, 0x2d00, 1) BOOL_AND (unique, 0x2b80, 1) , (unique, 0x2c00, 1) *)
	Move (V_TEMP 0x2d00) (BinOp OP_AND (Var (V_TEMP 0x2b80)) (Var (V_TEMP 0x2c00))) $;
	(* (register, 0x4008, 8) INT_ZEXT (unique, 0x2d00, 1) *)
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d00)))
)

(* 0x0010003c: add x1,x19,x1, LSL #0x3 *)
(*    1048636: add x1,x19,x1, LSL #0x3 *)
| 0x10003c => Some (4,
	(* (unique, 0x4400, 8) INT_LEFT (register, 0x4008, 8) , (const, 0x3, 4) *)
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X1) (Word 0x3 64)) $;
	(* (unique, 0x12380, 8) COPY (unique, 0x4400, 8) *)
	Move (V_TEMP 0x12380) (Var (V_TEMP 0x4400)) $;
	(* (register, 0x105, 1) INT_CARRY (register, 0x4098, 8) , (unique, 0x12380, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x12380))) (Var R_X19))) $;
	(* (register, 0x106, 1) INT_SCARRY (register, 0x4098, 8) , (unique, 0x12380, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x12380))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x12380)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x12480, 8) INT_ADD (register, 0x4098, 8) , (unique, 0x12380, 8) *)
	Move (V_TEMP 0x12480) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x12380))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x12480, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12480)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x12480, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12480)) (Word 0x0 64))) $;
	(* (register, 0x4008, 8) COPY (unique, 0x12480, 8) *)
	Move R_X1 (Var (V_TEMP 0x12480))
)

(* 0x00100040: ldr x19,[x1, #0x8] *)
(*    1048640: ldr x19,[x1, #0x8] *)
| 0x100040 => Some (4,
	(* (unique, 0x6500, 8) INT_ADD (register, 0x4008, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x6500) (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	(* (register, 0x4098, 8) LOAD (const, 0x1b1, 8) , (unique, 0x6500, 8) *)
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6500)) LittleE 8)
)

(* 0x00100044: b 0x00100020 *)
(*    1048644: b 0x00100020 *)
| 0x100044 => Some (4,
	(*  ---  BRANCH (ram, 0x100020, 8) *)
	Jmp (Word 0x100020 64)
)

(* 0x00100048: mov x19,#0x0 *)
(*    1048648: mov x19,#0x0 *)
| 0x100048 => Some (4,
	(* (register, 0x4098, 8) COPY (const, 0x0, 8) *)
	Move R_X19 (Word 0x0 64)
)

(* 0x0010004c: ldr x21,[sp, #0x20] *)
(*    1048652: ldr x21,[sp, #0x20] *)
| 0x10004c => Some (4,
	(* (unique, 0x6500, 8) INT_ADD (register, 0x8, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x6500) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	(* (register, 0x40a8, 8) LOAD (const, 0x1b1, 8) , (unique, 0x6500, 8) *)
	Move R_X21 (Load (Var V_MEM64) (Var (V_TEMP 0x6500)) LittleE 8)
)

(* 0x00100050: mov x0,x19 *)
(*    1048656: mov x0,x19 *)
| 0x100050 => Some (4,
	(* (register, 0x4000, 8) COPY (register, 0x4098, 8) *)
	Move R_X0 (Var R_X19)
)

(* 0x00100054: ldp x19,x20,[sp, #0x10] *)
(*    1048660: ldp x19,x20,[sp, #0x10] *)
| 0x100054 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x8, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4098, 8) COPY (unique, 0x24680, 8) *)
	Move R_X19 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x40a0, 8) COPY (unique, 0x24800, 8) *)
	Move R_X20 (Var (V_TEMP 0x24800))
)

(* 0x00100058: ldp x29,x30,[sp], #0x30 *)
(*    1048664: ldp x29,x30,[sp], #0x30 *)
| 0x100058 => Some (4,
	(* (unique, 0x7c80, 8) COPY (register, 0x8, 8) *)
	Move (V_TEMP 0x7c80) (Var R_SP) $;
	(* (register, 0x8, 8) INT_ADD (register, 0x8, 8) , (const, 0x30, 8) *)
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7c80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7c80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7c80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7c80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x40e8, 8) COPY (unique, 0x24680, 8) *)
	Move R_X29 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x40f0, 8) COPY (unique, 0x24800, 8) *)
	Move R_X30 (Var (V_TEMP 0x24800))
)

(* 0x0010005c: ret *)
(*    1048668: ret *)
| 0x10005c => Some (4,
	(* (register, 0x0, 8) COPY (register, 0x40f0, 8) *)
	Move R_PC (Var R_X30) $;
	(*  ---  RETURN (register, 0x0, 8) *)
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx tfind_lo_tfind_armv8.
Proof. Picinae_typecheck. Qed.
