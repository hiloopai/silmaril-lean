module

public import Silmaril.Compiler.Core.Verified.ArgvAbort.Defs
public import Silmaril.Compiler.Core.Verified.LoopLink.Defs
public import Silmaril.Compiler.Core.Verified.IntExprLir.Defs
public import Silmaril.Machine.X86.Lir.LinMem.Defs
public import Silmaril.Compiler.Core.Verified.PrintLink.Defs

/-! # Runtime code for `if (c) abort(); return e;` over `argv[i][j]`

`blocks P` is a control-flow graph of three blocks of `__ccomp_start(argc, argv)` (`argv` in
register 2 is the linear address of `Spec.argBlock`):

* block 0 loads slot `i` of the pointer array (`argv[i]`, 8 bytes at `argv + 8 i`) and the byte
  `j` it points to (`argv[i][j]`) into register 3, computes the test `c == 0` (`Term.ops`) and
  branches on `test = 1`;
* block 1 (the test is not `1`, the C condition holds) records `abort` in the control block (word 5
  := 2) and traps, which crt0 observes as SIGABRT;
* block 2 computes the return expression and returns it.

The byte the code reads is `ArgvChar.charOfArgs args i j` (`load_slot`, `load_char`): the
character of the string (or its terminator), and `0` for the null slot `i = argc` (whose Core
run is undefined behaviour). `link_sound`: every observation is exhaustion, `abort` with no output
when the test is in range and not `1`, or `exit` with the return expression's value when the
test is `1` and both are in range.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvAbortLink

open Silmaril.Machine
open Spec Backend
open IntExpr (Term)
open ArgvAbort (Plan)
open ArgBlock (strAddr)

/-! ## The code -/

def entryOps (P : Plan) : List (Lir.Op Mir.Reg) :=
  [.load .b8 .zero 5 2 (8 * P.ij.1), .load .b1 .zero 3 5 P.ij.2] ++ P.test.ops 6 ++
    [.const 7 1, .binary (.cmp .eq) 8 6 7]

def abortOps : List (Lir.Op Mir.Reg) := [.const 9 0, .const 10 2, .store .b8 9 (ctlAddr + 40) 10]

def retOps (P : Plan) : List (Lir.Op Mir.Reg) := P.ret.ops 11 ++ [.move 0 11]

def blocks (P : Plan) : List (Lir.Block Mir.Reg) :=
  [⟨(entryOps P).map .op, .branch 8 2 1⟩, ⟨abortOps.map .op, .trap⟩, ⟨(retOps P).map .op, .ret [.reg 0]⟩]

def link (P : Plan) : Mir.Linked := LoopLink.link (blocks P)

/-! ## The argument block in the linear memory -/

theorem artifact_memSize {l : Mir.Linked} {a : Artifact} (h : artifactOf l = .ok a) :
    a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize := by
  unfold artifactOf at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  rfl

theorem lmem_block {a : Artifact} {args : List String} {x : Nat} (h₁ : a.argBase ≤ x)
    (h₂ : x < a.argBase + (argBlock a.argBase args).length) :
    (a.lmem args).bytes x = BitVec.ofNat 8 ((argBlock a.argBase args)[x - a.argBase]!).toNat := by
  simp [Artifact.lmem, h₁, h₂]

theorem leValue_digits : ∀ (n W : Nat),
    X86.Ext.leValue (List.ofFn fun k : Fin n => BitVec.ofNat 8 ((W >>> (8 * (k : Nat))) % 256)) =
      W % 2 ^ (8 * n)
  | 0, W => by simp [X86.Ext.leValue, Nat.mod_one]
  | n + 1, W => by
    rw [List.ofFn_succ, X86.Ext.leValue]
    have hs : (fun k : Fin n => BitVec.ofNat 8 ((W >>> (8 * ((k.succ : Fin (n + 1)) : Nat))) % 256)) =
        (fun k : Fin n => BitVec.ofNat 8 (((W >>> 8) >>> (8 * (k : Nat))) % 256)) := by
      funext k
      rw [← Nat.shiftRight_add, show 8 * ((k.succ : Fin (n + 1)) : Nat) = 8 + 8 * (k : Nat) by
        simp [Fin.val_succ]; omega]
    rw [hs, leValue_digits n (W >>> 8)]
    simp only [Fin.val_zero, Nat.mul_zero, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [show 2 ^ (8 * (n + 1)) = 2 ^ 8 * 2 ^ (8 * n) by rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm],
      Nat.mod_mul]
    simp

/-- The word in slot `i` of the pointer array: the address of string `i`, or null. -/
def slotWord (base : Nat) (args : List String) (i : Nat) : Nat :=
  if i < args.length then strAddr base args i else 0

theorem slot_bytes {args : List String} (ha : ArgsOk args) (base : Nat) {i : Nat} (hi : i ≤ args.length) :
    ((argBlock base args).drop (8 * i)).take 8 = le8 (slotWord base args i) := by
  unfold slotWord
  split
  · exact ArgBlock.argBlock_slot base args (ArgBlock.ascii_of_argsOk ha) (by assumption)
  · obtain rfl : i = args.length := by omega
    exact ArgBlock.argBlock_slot_null base args (ArgBlock.ascii_of_argsOk ha)

theorem block_length {args : List String} (ha : ArgsOk args) (base : Nat) :
    8 * (args.length + 1) ≤ (argBlock base args).length ∧ (argBlock base args).length ≤ 4096 := by
  have hl := ArgBlock.length_argBlock base args (ArgBlock.ascii_of_argsOk ha)
  have hl0 := ArgBlock.length_argBlock 0 args (ArgBlock.ascii_of_argsOk ha)
  have hb := ha.2.2
  simp only [minArgSize] at hb
  simp only [strAddr, List.take_length] at hl hl0
  omega

/-- String `i` lies in the block. -/
theorem strAddr_lt {args : List String} (ha : ArgsOk args) (base : Nat) {i : Nat} (hi : i < args.length) :
    strAddr base args i - base + args[i].length < (argBlock base args).length := by
  have h := ArgBlock.argBlock_nul base args (ArgBlock.ascii_of_argsOk ha) hi
  exact (List.getElem?_eq_some_iff.mp h).1

theorem slotWord_lt {args : List String} (ha : ArgsOk args) (base i : Nat) :
    slotWord base args i ≤ base + 4096 := by
  unfold slotWord; split
  · rename_i hi
    have := strAddr_lt ha base hi
    have := (block_length ha base).2
    have := ArgvReloc.le_strAddr base args i
    omega
  · omega

/-- **The slot load** of `argv[i]`. -/
theorem load_slot {a : Artifact} (hbase : a.argBase = Silmaril.Compile.Forks.CoreComp.Target.argBase) (hsize : a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize)
    {args : List String} (ha : ArgsOk args) {i : Nat} (hi : i ≤ args.length) :
    (a.lmem args).load .b8 .zero (a.argBase + 8 * i) =
      some (BitVec.ofNat 64 (slotWord a.argBase args i)) := by
  obtain ⟨hl₁, hl₂⟩ := block_length ha a.argBase
  have hroom : Silmaril.Compile.Forks.CoreComp.Target.argBase + 4096 ≤ Silmaril.Compile.Forks.CoreComp.Target.memSize := by decide
  have hin : (a.lmem args).InBounds (a.argBase + 8 * i) .b8 := by
    simp only [Lir.Memory.InBounds, Lir.Width.bytes, Artifact.lmem, hsize]; rw [hbase] at *; omega
  have hW : slotWord a.argBase args i < 2 ^ 64 := by
    have := slotWord_lt ha a.argBase i
    rw [hbase] at this ⊢; have : Silmaril.Compile.Forks.CoreComp.Target.argBase < 2 ^ 32 := by decide
    omega
  have hbytes : ∀ k : Fin 8, (a.lmem args).bytes (a.argBase + 8 * i + k) =
      BitVec.ofNat 8 ((slotWord a.argBase args i >>> (8 * (k : Nat))) % 256) := by
    intro k
    have hk := k.isLt
    rw [lmem_block (by omega) (by omega), show a.argBase + 8 * i + k - a.argBase = 8 * i + k by omega]
    have hs := congrArg (fun l => l[(k : Nat)]?) (slot_bytes ha a.argBase hi)
    simp only [List.getElem?_take, hk, ↓reduceIte, List.getElem?_drop] at hs
    rw [List.getElem!_eq_getElem?_getD, hs]
    simp [le8, ArgvReloc.toNat_toUInt8 (Nat.mod_lt _ (by norm_num : 0 < 256))]
  unfold Lir.Memory.load
  simp only [hin, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [Lir.extend, Lir.Width.bytes]
  rw [X86.Backend.readLE_toNat _ 8 _ (by norm_num)]
  rw [show (List.ofFn fun k : Fin 8 => (a.lmem args).bytes (a.argBase + 8 * i + k)) =
    List.ofFn fun k : Fin 8 => BitVec.ofNat 8 ((slotWord a.argBase args i >>> (8 * (k : Nat))) % 256) from
    List.ofFn_inj.mpr (funext hbytes), leValue_digits]
  simp

theorem byte_load {lm : Lir.Memory} {x : Nat} (hin : lm.InBounds x .b1) {c : Nat} (hc : c < 256)
    (hb : lm.bytes x = BitVec.ofNat 8 c) : lm.load .b1 .zero x = some (BitVec.ofNat 64 c) := by
  unfold Lir.Memory.load
  simp only [hin, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [Lir.extend, Lir.Width.bytes]
  rw [X86.Backend.readLE_toNat _ 1 _ (by norm_num)]
  simp [X86.Ext.leValue, hb, Nat.mod_eq_of_lt hc]
  exact (Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)).symm

/-- **The character load** of `argv[i][j]`: the byte of the string, its terminator, or `0` from the
null slot (`charOfArgs`). -/
theorem load_char {a : Artifact} (hbase : a.argBase = Silmaril.Compile.Forks.CoreComp.Target.argBase) (hsize : a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize)
    (himg : a.image = .empty) {args : List String} (ha : ArgsOk args) {i j : Nat} (hi : i ≤ args.length)
    (hj : ∀ h : i < args.length, j ≤ args[i].length) (hj0 : j < 4096) :
    (a.lmem args).load .b1 .zero (slotWord a.argBase args i + j) =
      some (BitVec.ofNat 64 (ArgvChar.charOfArgs args i j).toNat) := by
  have hroom : Silmaril.Compile.Forks.CoreComp.Target.argBase + 4096 ≤ Silmaril.Compile.Forks.CoreComp.Target.memSize := by decide
  have hsl := slotWord_lt ha a.argBase i
  have hin : (a.lmem args).InBounds (slotWord a.argBase args i + j) .b1 := by
    simp only [Lir.Memory.InBounds, Lir.Width.bytes, Artifact.lmem, hsize]; rw [hbase] at hsl ⊢
    have := (block_length ha a.argBase).2
    unfold slotWord at hsl ⊢; split
    · rename_i hlt
      have := strAddr_lt ha a.argBase hlt
      have := hj hlt
      have := ArgvReloc.le_strAddr a.argBase args i
      rw [hbase] at *; omega
    · omega
  rcases Nat.lt_or_ge i args.length with hlt | hge
  · have hsw : slotWord a.argBase args i = strAddr a.argBase args i := by simp [slotWord, hlt]
    rw [hsw] at hin ⊢
    have hle := ArgvReloc.le_strAddr a.argBase args i
    have hl := strAddr_lt ha a.argBase hlt
    have hjl := hj hlt
    rcases Nat.lt_or_ge j args[i].length with hj' | hj'
    · have hjl' : j < args[i].toList.length := by rw [String.length_toList]; exact hj'
      obtain ⟨h0, h1, -⟩ := ArgvReloc.chars_of_argsOk ha _ (List.getElem_mem hlt) _
        (args[i].toList.getElem_mem hjl')
      rw [ArgvChar.charOfArgs_lt hlt hj']
      refine byte_load hin (c := (args[i].toList[j]'hjl').toNat) (by omega) ?_
      rw [lmem_block (by omega) (by omega), show strAddr a.argBase args i + j - a.argBase =
        strAddr a.argBase args i - a.argBase + j by omega, List.getElem!_eq_getElem?_getD,
        ArgBlock.argBlock_char a.argBase args (ArgBlock.ascii_of_argsOk ha) hlt hj']
      simp [ArgvReloc.toNat_toUInt8 (show (args[i].toList[j]'hjl').toNat < 256 by omega)]
    · obtain rfl : j = args[i].length := by omega
      rw [ArgvChar.charOfArgs_nul hlt]
      refine byte_load hin (c := 0) (by norm_num) ?_
      rw [lmem_block (by omega) (by omega), show strAddr a.argBase args i + args[i].length - a.argBase =
        strAddr a.argBase args i - a.argBase + args[i].length by omega, List.getElem!_eq_getElem?_getD,
        ArgBlock.argBlock_nul a.argBase args (ArgBlock.ascii_of_argsOk ha) hlt]
      rfl
  · have hsw : slotWord a.argBase args i = 0 := by simp [slotWord]; omega
    have hc : ArgvChar.charOfArgs args i j = 0 := by simp [ArgvChar.charOfArgs]; omega
    rw [hsw] at hin ⊢
    rw [hc]
    simp only [Nat.zero_add] at hin ⊢
    have h4 : 4096 ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase := by decide
    refine byte_load hin (c := 0) (by norm_num) ?_
    rw [ConstLink.lmem_bytes_empty himg args j (by rw [hbase]; omega)]
    rfl

/-! ## Runs -/

theorem charOfArgs_nonneg (args : List String) (i j : Nat) : 0 ≤ ArgvChar.charOfArgs args i j := by
  unfold ArgvChar.charOfArgs
  split
  · cases h : ((args[i].toList.map fun c => (c.toNat : Int)) ++ [0])[j]? with
    | none => simp
    | some x =>
      simp only [Option.getD_some]
      have hx := List.mem_of_getElem? h
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
      rcases hx with ⟨c, -, rfl⟩ | rfl <;> omega
  · exact le_rfl

theorem ofInt_eq_one {v : Int} (hv : ConvInt.IsInt v) : (BitVec.ofInt 64 v == 1) = decide (v = 1) := by
  by_cases h : v = 1
  · subst h; rfl
  · have : BitVec.ofInt 64 v ≠ 1 := by
      intro e
      have := congrArg BitVec.toInt e
      rw [BitVec.toInt_ofInt] at this
      obtain ⟨h0, h1⟩ := hv
      simp [Int.bmod] at this
      omega
    simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    exact this

/-- **The entry block**: the character in register 3 and, when the test is in range, whether it is
`1` in register 8. -/
theorem entry_exec {P : Plan} {a : Artifact} (hbase : a.argBase = Silmaril.Compile.Forks.CoreComp.Target.argBase)
    (hsize : a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize) (himg : a.image = .empty) {args : List String} (ha : ArgsOk args)
    (hi : P.ij.1 ≤ args.length) (hj : ∀ h : P.ij.1 < args.length, P.ij.2 ≤ args[P.ij.1].length)
    (hj0 : P.ij.2 < 4096) :
    ∃ fr, Lir.execOps (entryOps P) (LoopLink.entryState a args).frame (a.lmem args) = some (fr, a.lmem args) ∧
      fr.get 3 = some (BitVec.ofInt 64 (ArgvChar.charOfArgs args P.ij.1 P.ij.2)) ∧
      (P.test.Ok (ArgvChar.charOfArgs args P.ij.1 P.ij.2) →
        fr.get 8 = some (Lir.ofBool (decide (P.test.val (ArgvChar.charOfArgs args P.ij.1 P.ij.2) = 1)))) := by
  have hofs : BitVec.ofNat 64 (ArgvChar.charOfArgs args P.ij.1 P.ij.2).toNat =
      BitVec.ofInt 64 (ArgvChar.charOfArgs args P.ij.1 P.ij.2) := by
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (charOfArgs_nonneg args P.ij.1 P.ij.2)
    rw [hn]; simp
  let ch := ArgvChar.charOfArgs args P.ij.1 P.ij.2
  have hb64 : a.argBase < 2 ^ 64 := by rw [hbase]; decide
  let fr0 := (LoopLink.entryState a args).frame
  have h2 : fr0.get 2 = some (BitVec.ofNat 64 a.argBase) := by simp [fr0, LoopLink.entryState]
  have hW : slotWord a.argBase args P.ij.1 < 2 ^ 64 := by
    have := slotWord_lt ha a.argBase P.ij.1; rw [hbase] at this ⊢
    have : Silmaril.Compile.Forks.CoreComp.Target.argBase < 2 ^ 32 := by decide
    omega
  let fr₁ := (fr0.set 5 (BitVec.ofNat 64 (slotWord a.argBase args P.ij.1))).set 3 (BitVec.ofInt 64 ch)
  have hx₁ : Lir.execOps [.load .b8 .zero 5 2 (8 * P.ij.1), .load .b1 .zero 3 5 P.ij.2] fr0 (a.lmem args) =
      some (fr₁, a.lmem args) := by
    simp only [Lir.execOps, Lir.Op.exec, h2, Option.bind_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64,
      load_slot hbase hsize ha hi, Option.map_some, Lir.Frame.get_set, ite_true, Nat.mod_eq_of_lt hW,
      load_char hbase hsize himg ha hi hj hj0, hofs]
    rfl
  have h3 : fr₁.get 3 = some (BitVec.ofInt 64 ch) := by simp [fr₁]
  obtain ⟨fr₂, w, hx₂, hg₂, hv₂, hbelow⟩ := Term.ops_exec (n := ch) P.test 6 (by decide) fr₁ (a.lmem args) h3
  refine ⟨(fr₂.set 7 1).set 8 (Lir.ofBool (w == 1)), ?_, ?_, fun ok => ?_⟩
  · rw [entryOps, Lir.execOps_append, Lir.execOps_append, hx₁]
    simp only [Option.bind_some, hx₂]
    simp [Lir.execOps, Lir.Op.exec, hg₂, Lir.Binop.eval, Lir.Cond.eval]
  · simp [hbelow 3 (by decide), h3]
    rfl
  · simp only [Lir.Frame.get_set, ↓reduceIte, hv₂ ok]
    exact congrArg (fun x => some (Lir.ofBool x)) (ofInt_eq_one (Term.int_of_ok P.test ok))

theorem run_block {P : Plan} {l : Nat} {ops : List (Lir.Op Mir.Reg)} {t : Lir.Term Mir.Reg}
    (hb : (link P).prog.block? 0 l = some ⟨ops.map .op, t⟩) {fr fr' : Lir.Frame Mir.Reg}
    {m m' : Lir.Memory} (hx : Lir.execOps ops fr m = some (fr', m')) :
    Lir.Steps (link P).prog ⟨⟨0, l, 0⟩, fr, [], m⟩ ⟨⟨0, l, ops.length⟩, fr', [], m'⟩ ∧
      (link P).prog.fetch ⟨0, l, ops.length⟩ = some (.term t) := by
  refine ⟨?_, Lir.Prog.fetch_eq_term (pt := ⟨0, l, ops.length⟩) hb (by simp)⟩
  have := Lir.steps_execOps (p := (link P).prog) (os := ops) (s := ⟨⟨0, l, 0⟩, fr, [], m⟩) (rest := []) hb
    (by rw [List.append_nil]; rfl) hx
  simpa using this

/-- The abort store: control word 5 := 2. -/
theorem abort_exec (fr : Lir.Frame Mir.Reg) {m : Lir.Memory} (hm : m.size = Silmaril.Compile.Forks.CoreComp.Target.memSize) :
    ∃ fr' m', Lir.execOps abortOps fr m = some (fr', m') ∧
      m.store .b8 (ctlAddr + 40) (BitVec.ofNat 64 2) = some m' := by
  have hin : m.InBounds (ctlAddr + 40) .b8 := by
    simp only [Lir.Memory.InBounds, Lir.Width.bytes, hm]; decide
  refine ⟨(fr.set 9 0).set 10 2, _, ?_, by simp [Lir.Memory.store, hin]; rfl⟩
  simp [abortOps, Lir.execOps, Lir.Op.exec, Lir.Memory.store, hin]

theorem block0 (P : Plan) : (link P).prog.block? 0 0 = some ⟨(entryOps P).map .op, .branch 8 2 1⟩ := rfl
theorem block1 (P : Plan) : (link P).prog.block? 0 1 = some ⟨abortOps.map .op, .trap⟩ := rfl
theorem block2 (P : Plan) : (link P).prog.block? 0 2 = some ⟨(retOps P).map .op, .ret [.reg 0]⟩ := rfl

/-- The hypotheses on the artifact and the arguments that every run below takes. -/
structure Setup (P : Plan) (a : Artifact) (args : List String) : Prop where
  base : a.argBase = Silmaril.Compile.Forks.CoreComp.Target.argBase
  size : a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize
  img : a.image = .empty
  ok : ArgsOk args
  i : P.ij.1 ≤ args.length
  j : ∀ h : P.ij.1 < args.length, P.ij.2 ≤ args[P.ij.1].length
  j0 : P.ij.2 < 4096

/-- **The abort**: when the test is in range and not `1`, the run records `abort` and traps. -/
theorem abort_behaves {P : Plan} {a : Artifact} {args : List String} (st : Setup P a args)
    (ok : P.test.Ok (ArgvChar.charOfArgs args P.ij.1 P.ij.2))
    (ne : P.test.val (ArgvChar.charOfArgs args P.ij.1 P.ij.2) ≠ 1) :
    ∃ m', (a.lmem args).store .b8 (ctlAddr + 40) (BitVec.ofNat 64 2) = some m' ∧
      Lir.Behaves (link P).prog (LoopLink.entryState a args) (.trapped m') := by
  obtain ⟨fr, hx, -, h8⟩ := entry_exec st.base st.size st.img st.ok st.i st.j st.j0
  have h8 := h8 ok
  simp only [ne, decide_false] at h8
  obtain ⟨s₀, hf₀⟩ := run_block (block0 P) hx
  obtain ⟨fr', m', hx', hst⟩ := abort_exec fr (m := a.lmem args) (by simp [Artifact.lmem, st.size])
  obtain ⟨s₁, hf₁⟩ := run_block (block1 P) hx'
  refine ⟨m', hst, _, s₀.trans (Relation.ReflTransGen.head ?_ s₁), ?_⟩
  · show Lir.step _ _ = _
    simp [Lir.step, hf₀, h8, Lir.ofBool]
  · simp [Lir.step, hf₁]

/-- **The return**: when the test is `1` and the return expression is in range, the run returns
its value. -/
theorem ret_behaves {P : Plan} {a : Artifact} {args : List String} (st : Setup P a args)
    (ok : P.test.Ok (ArgvChar.charOfArgs args P.ij.1 P.ij.2))
    (eq : P.test.val (ArgvChar.charOfArgs args P.ij.1 P.ij.2) = 1)
    (okr : P.ret.Ok (ArgvChar.charOfArgs args P.ij.1 P.ij.2)) :
    Lir.Behaves (link P).prog (LoopLink.entryState a args)
      (.returned [BitVec.ofInt 64 (P.ret.val (ArgvChar.charOfArgs args P.ij.1 P.ij.2))] (a.lmem args)) := by
  obtain ⟨fr, hx, h3, h8⟩ := entry_exec st.base st.size st.img st.ok st.i st.j st.j0
  have h8 := h8 ok
  simp only [eq, decide_true] at h8
  obtain ⟨s₀, hf₀⟩ := run_block (block0 P) hx
  obtain ⟨fr₂, w, hx₂, hg₂, hv₂, -⟩ := Term.ops_exec P.ret 11 (by decide) fr (a.lmem args) h3
  have hx' : Lir.execOps (retOps P) fr (a.lmem args) = some (fr₂.set 0 w, a.lmem args) := by
    rw [retOps, Lir.execOps_append, hx₂]
    simp [Lir.execOps, Lir.Op.exec, hg₂]
  obtain ⟨s₁, hf₁⟩ := run_block (block2 P) hx'
  refine ⟨_, s₀.trans (Relation.ReflTransGen.head ?_ s₁), ?_⟩
  · show Lir.step _ _ = _
    simp [Lir.step, hf₀, h8, Lir.ofBool]
  · simp [Lir.step, hf₁, Lir.Frame.readAll, Lir.Frame.read, hv₂ okr]

/-- **The link is correct**: every observation is exhaustion, `abort` with no output when the test
is in range and not `1`, or the exit with the return expression's value when the test is `1` and
the return expression is in range. -/
theorem link_sound {P : Plan} {a : Artifact} (h : artifactOf (link P) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String} (ha : ArgsOk args)
    (hij : P.ij.1 ≤ 1 ∧ P.ij.2 = 0) {o : Obs} (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨
      ((P.test.Ok (ArgvChar.charOfArgs args P.ij.1 P.ij.2) →
          P.test.val (ArgvChar.charOfArgs args P.ij.1 P.ij.2) ≠ 1 → o = .abort []) ∧
        (P.test.Ok (ArgvChar.charOfArgs args P.ij.1 P.ij.2) →
          P.test.val (ArgvChar.charOfArgs args P.ij.1 P.ij.2) = 1 →
          P.ret.Ok (ArgvChar.charOfArgs args P.ij.1 P.ij.2) →
          o = .exit ((BitVec.ofInt 64 (P.ret.val (ArgvChar.charOfArgs args P.ij.1 P.ij.2))).toNat % 256) [])) := by
  obtain ⟨hbase, -, himg⟩ := ConstLink.artifact_layout h
  have hlen : 1 ≤ args.length := List.length_pos_iff.mpr ha.1
  have st : Setup P a args := ⟨hbase, artifact_memSize h, by simpa [link, LoopLink.link] using himg, ha,
    by omega, fun _ => by omega, by omega⟩
  have hzero (addr : Nat) (hi : addr + 8 ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase) : memWord (a.lmem args) addr = 0 := by
    apply ConstLink.memWord_zero
    intro i
    apply ConstLink.lmem_bytes_empty st.img
    rw [hbase]
    have := i.isLt
    omega
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link, LoopLink.link_funcs] at hstart
  cases hstart
  rw [link, LoopLink.link_start] at hs
  cases hs
  rcases ho with ho | hstuck | ⟨b, hb', hobs⟩
  · exact .inl ho
  · right
    refine ⟨fun ok ne => ?_, fun ok eq okr => ?_⟩
    · obtain ⟨m', -, hab⟩ := abort_behaves st ok ne
      cases Lir.Behaves.unique hstuck hab
    · cases Lir.Behaves.unique hstuck (ret_behaves st ok eq okr)
  · right
    refine ⟨fun ok ne => ?_, fun ok eq okr => ?_⟩
    · obtain ⟨m', hst, hab⟩ := abort_behaves st ok ne
      cases Lir.Behaves.unique hb' hab
      obtain ⟨out, rfl, hout⟩ := hobs
      have h40 : memWord m' (ctlAddr + 40) = 2 := by
        rw [PrintLink.memWord_store hst]; rfl
      have h24 : memWord m' (ctlAddr + 24) = 0 := by
        rw [PrintLink.memWord_outside hst (by left; decide)]; exact hzero _ (by decide)
      have h48 : memWord m' (ctlAddr + 48) = 0 := by
        rw [PrintLink.memWord_outside hst (by right; decide)]; exact hzero _ (by decide)
      rw [ConstLink.stdoutOf_zero h24 h48 hout]
      simp [trapObs, h40]
    · cases Lir.Behaves.unique hb' (ret_behaves st ok eq okr)
      exact LoopLink.exit_obs (blocks := blocks P) h hobs

end Silmaril.Compile.Core.Verified.ArgvAbortLink
