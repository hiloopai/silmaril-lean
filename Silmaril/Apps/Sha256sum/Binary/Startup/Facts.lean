module

public import Silmaril.Apps.Sha256sum.Binary.Startup.Code
public import Silmaril.X86.SegVC.Ext8
public import Silmaril.Apps.Sha256sum.Lift.Ro
public meta import Lean

/-! # Memory facts for the startup segments of `sha256sum-min`

* `Ro m`: the headers, `.text` and `.rodata` (`[0x400000, 0x408010)`) are not writable. A
  successful store keeps the mapping (`Ro.of_wb`, `Ro.of_st`), so it keeps `Ro`, and it changes
  no byte that is not writable, so it keeps every code region of `Startup.Code` loaded
  (`loaded_of_wb`, `loaded_of_st`): no disjointness argument per store.
* `and16`: `and $-16, %rsp` on an aligned stack pointer.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN storeN)

/-- The image below `.data` is not writable. -/
def Ro (m : Memory) : Prop :=
  ∀ a, 0x400000 ≤ a → a < 0x408010 → m.permits .write a = false

theorem Ro.of_wb {m m' : Memory} {a : Nat} {bs : List Byte} (hw : m.writeBytes a bs = some m')
    (h : Ro m) : Ro m' := by
  intro x lo hi
  rw [(Silmaril.X86.Ext.writeBytes_ro hw).permits]
  exact h x lo hi

theorem Ro.of_st {m m' : Memory} {a : Word} {k : Nat} {v : Word} (hw : storeN m a k v = some m')
    (h : Ro m) : Ro m' := Ro.of_wb hw h

/-- A store keeps a region of the read-only image loaded. -/
theorem loaded_of_wb {m m' : Memory} {a : Nat} {bs : List Byte} {base : Word} {code : List Byte}
    (hw : m.writeBytes a bs = some m') (h : Ro m) (hl : Loaded m base code)
    (lo : 0x400000 ≤ base.toNat) (hi : base.toNat + code.length ≤ 0x408010) :
    Loaded m' base code := by
  have ro := Silmaril.X86.Ext.writeBytes_ro hw
  have ww : Memory.WritesWithin m m' (fun x => m.permits .write x = true) :=
    ⟨ro.1, fun x hx => ro.2 x (by simpa using hx)⟩
  unfold Loaded at hl ⊢
  rw [ww.fetchBytes (fun o ho => by rw [h _ (by omega) (by omega)]; decide)]
  exact hl

theorem loaded_of_st {m m' : Memory} {a : Word} {k : Nat} {v : Word} {base : Word}
    {code : List Byte} (hw : storeN m a k v = some m') (h : Ro m) (hl : Loaded m base code)
    (lo : 0x400000 ≤ base.toNat) (hi : base.toNat + code.length ≤ 0x408010) :
    Loaded m' base code := loaded_of_wb hw h hl lo hi

theorem setWidth_8_64 (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  simp [BitVec.setWidth_setWidth_of_le]

theorem ofNat_shl (a k : Nat) : (BitVec.ofNat 64 a) <<< k = BitVec.ofNat 64 (a <<< k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod]

theorem setWidth_8_64_32 (b : BitVec 8) : ((b.setWidth 32).setWidth 64).setWidth 8 = b := by
  simp [BitVec.setWidth_setWidth_of_le]

theorem setWidth_64_32 (b : BitVec 8) : (b.setWidth 32).setWidth 64 = b.setWidth 64 := by
  simp

/-- `op r8, r/m8` (an `Ext8` new form `seg_vc8` does not cover): the source is read, then
the 8-bit ALU step. -/
theorem execNew_aluR (op : Silmaril.X86.AluOp) (d : Silmaril.X86.Ext8.BReg)
    (src : Silmaril.X86.Ext8.RM8) (s : Silmaril.X86.State) (m : Memory) (next : Word) :
    Silmaril.X86.Ext8.execNew (.aluR op d src) s m next =
      match src.read s m next with
      | none => .dataFault
      | some y => Silmaril.X86.Ext.retire next
          (if op = .cmp then some ({ s with flags := Silmaril.X86.Ext.AluOp.flagsN op (d.read s) y }, m)
           else some ({ d.write s (Silmaril.X86.Ext.AluOp.resultN op (d.read s) y) with
             flags := Silmaril.X86.Ext.AluOp.flagsN op (d.read s) y }, m)) := by
  simp only [Silmaril.X86.Ext8.execNew]
  cases src.read s m next with
  | none => rfl
  | some y =>
    simp only [Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write]
    split <;> rfl

theorem rm8_read_mem (a : Silmaril.X86.Ext.Mem) (s : Silmaril.X86.State) (m : Memory) (next : Word) :
    (Silmaril.X86.Ext8.RM8.mem a).read s m next = (loadN m (a.addr s next) 1).map fun v => v.setWidth 8 := rfl

/-- `.data` and `.bss` (`[0x409010, 0x413150)`) are readable and writable. -/
theorem data_perm {m : Memory} (h : Image.image.Mapped m) (acc : Silmaril.Process.Access)
    (hacc : acc ≠ .execute) : m.Permitted acc 0x409010 0xa140 := by
  have hs : Image.seg3 ∈ Image.image.segments := by simp [Image.image]
  have := readWith_segment h hs Image.image_wf (acc := acc)
    (by cases acc <;> first | rfl | exact absurd rfl hacc) 0 0xa140 (by decide) (by decide)
  exact Memory.readWith_permitted this

/-- `and $-16, %rsp` leaves an aligned stack pointer unchanged. -/
theorem and16 (x : Word) (h : x.toNat % 16 = 0) : x &&& 18446744073709551600#64 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have hx := x.isLt
  have e : (18446744073709551600#64).toNat = 2^64 - 16 := rfl
  rw [e]
  obtain ⟨k, hk⟩ : ∃ k, x.toNat = 16 * k := ⟨x.toNat / 16, by omega⟩
  rw [hk, Nat.and_comm, show 2^64 - 16 = (2^60 - 1) * 16 by norm_num,
    show 16 * k = k * 2^4 by ring, show (16:Nat) = 2^4 by rfl]
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_and_distrib]
  rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_eq_of_lt (by omega)]

open Silmaril.X86 (State) in
/-- A `push`: the write permission of the slot, and every memory the push may produce (named
by its `writeBytes` equation), as for `Silmaril.X86.SegVC.onOk_call`. -/
theorem onOk_retire_push {P : State → Memory → Prop} {next : Word} {s : State} {m : Memory}
    {v : Word} :
    Silmaril.X86.SegVC.onOk P (Silmaril.X86.Ext.retire next (Silmaril.X86.pushWord s m v)) ↔
      m.Permitted .write (s.read .rsp - 8#64).toNat 8 ∧
        ∀ after, m.writeBytes (s.read .rsp - 8#64).toNat
            (Silmaril.Machine.LittleEndian.encodeWords [v]) = some after →
          P { s.write .rsp (s.read .rsp - 8#64) with rip := next } after := by
  simp only [Silmaril.X86.pushWord]
  cases hw : m.writeBytes (s.read .rsp - 8#64).toNat
      (Silmaril.Machine.LittleEndian.encodeWords [v]) with
  | none =>
    simp only [Option.map_none, Silmaril.X86.SegVC.retire_none, Silmaril.X86.SegVC.onOk_dataFault, false_iff, not_and]
    intro hp
    have hc : m.checkSpan .write (s.read .rsp - 8#64).toNat 8 = true := hp
    unfold Memory.writeBytes at hw
    rw [Silmaril.X86.length_encodeWords_singleton, ite_eq_left hc] at hw
    cases hw
  | some after =>
    simp only [Option.map_some, Silmaril.X86.SegVC.retire_some, Silmaril.X86.SegVC.onOk_ok]
    constructor
    · intro h
      refine ⟨?_, fun a ha => ?_⟩
      · have := Memory.writeBytes_permitted hw
        simpa [Silmaril.X86.length_encodeWords_singleton] using this
      · cases ha; exact h
    · rintro ⟨_, h⟩; exact h after rfl

/-! ## Through the stores of a path

`seg_vc` names the memory after each store by its `writeBytes` (push, call) or `storeN` (mov)
equation. These lemmas carry a fact about a memory across one such store. -/

open Silmaril.Process (Access) in
theorem perm_wb {m m' : Memory} {a : Nat} {bs : List Byte} (hw : m.writeBytes a bs = some m')
    {acc : Access} {x n : Nat} (h : m.Permitted acc x n) : m'.Permitted acc x n := by
  have w := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp (Memory.writeBytes_writesOnly hw)
  exact (w.permitted_iff acc x n).mpr h

open Silmaril.Process (Access) in
theorem perm_st {m m' : Memory} {a : Word} {k : Nat} {v : Word} (hw : storeN m a k v = some m')
    {acc : Access} {x n : Nat} (h : m.Permitted acc x n) : m'.Permitted acc x n := perm_wb hw h

theorem loadN_wb_disj {m m' : Memory} {a : Nat} {bs : List Byte} (hw : m.writeBytes a bs = some m')
    {b : Word} {n : Nat} (hd : b.toNat + n ≤ a ∨ a + bs.length ≤ b.toNat) :
    loadN m' b n = loadN m b n := by
  have w := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp (Memory.writeBytes_writesOnly hw)
  have e : m'.readWith .read b.toNat n = m.readWith .read b.toNat n :=
    w.readWith (address := b.toNat) (length := n) (fun off hoff hin => by
      omega)
  simp only [loadN, Memory.readBytes, e]

theorem loadN_st_disj {m m' : Memory} {a : Word} {k : Nat} {v : Word} (hw : storeN m a k v = some m')
    {b : Word} {n : Nat} (hd : b.toNat + n ≤ a.toNat ∨ a.toNat + k ≤ b.toNat) :
    loadN m' b n = loadN m b n := loadN_wb_disj hw (by simpa using hd)

/-- A pushed word reads back. -/
theorem loadN_wb_word {m m' : Memory} {a : Word} {v : Word}
    (hw : m.writeBytes a.toNat (Silmaril.Machine.LittleEndian.encodeWords [v]) = some m')
    (hp : m.Permitted .read a.toNat 8) : loadN m' a 8 = some v :=
  Silmaril.X86.Ext.loadN_storeN_eight (v := v) (by
    unfold storeN; rw [← hw, Silmaril.X86.Ext.leBytes_eight]) hp

theorem loadN_st_same {m m' : Memory} {a : Word} {k : Nat} {v : Word}
    (hw : storeN m a k v = some m') (hp : m.Permitted .read a.toNat k) :
    loadN m' a k = some (BitVec.ofNat 64 (v.toNat % 2 ^ (8 * k))) :=
  Silmaril.X86.Ext.loadN_storeN hw hp

theorem ww_wb {m0 m m' : Memory} {W : Nat → Prop} {a : Nat} {bs : List Byte}
    (hw : m.writeBytes a bs = some m') (h : Memory.WritesWithin m0 m W)
    (hin : ∀ i < bs.length, W (a + i)) : Memory.WritesWithin m0 m' W :=
  h.step (Silmaril.X86.Ext.Stored.of_writeBytes hw) hin

theorem ww_st {m0 m m' : Memory} {W : Nat → Prop} {a : Word} {k : Nat} {v : Word}
    (hw : storeN m a k v = some m') (h : Memory.WritesWithin m0 m W)
    (hin : ∀ i < k, W (a.toNat + i)) : Memory.WritesWithin m0 m' W :=
  ww_wb hw h (by simpa using hin)

theorem sub_sub_lit (x : Word) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

open Silmaril.X86 (State Reg) in
theorem write_write_same (s : State) (r : Reg) (v w : Word) :
    (s.write r v).write r w = s.write r w := by
  cases s; simp only [State.write, State.mk.injEq, and_true]
  funext q; unfold Silmaril.Machine.RegisterFile.write; split <;> rfl

end Silmaril.Apps.Sha256sum.Binary.Startup

/-- `Ro` of the current memory, through the stores that produced it. -/
macro "st_ro" : tactic => `(tactic| repeat (first | with_reducible assumption | refine Silmaril.Apps.Sha256sum.Binary.Startup.Ro.of_wb (by assumption) ?_ | refine Silmaril.Apps.Sha256sum.Binary.Startup.Ro.of_st (by assumption) ?_))

/-- A code region of `Startup.Code` lies in the read-only image. -/
macro "region_ro" : tactic => `(tactic| (simp only [Silmaril.Apps.Sha256sum.Binary.Startup.Start.code_length, Silmaril.Apps.Sha256sum.Binary.Startup.Main.code_length, Silmaril.Apps.Sha256sum.Binary.Startup.Call.code_length, Silmaril.Apps.Sha256sum.Binary.Startup.Digest.code_length, Silmaril.Apps.Sha256sum.Binary.Startup.Start.base_toNat, Silmaril.Apps.Sha256sum.Binary.Startup.Main.base_toNat, Silmaril.Apps.Sha256sum.Binary.Startup.Call.base_toNat, Silmaril.Apps.Sha256sum.Binary.Startup.Digest.base_toNat]; decide))

/-- A code region of the read-only image stays loaded through the stores. -/
macro "st_loaded" : tactic => `(tactic| repeat (first | with_reducible assumption | refine Silmaril.Apps.Sha256sum.Binary.Startup.loaded_of_wb (by assumption) (by st_ro) ?_ (by region_ro) (by region_ro) | refine Silmaril.Apps.Sha256sum.Binary.Startup.loaded_of_st (by assumption) (by st_ro) ?_ (by region_ro) (by region_ro)))


/-- `sv [lemmas]`: `seg_vc8` with pushes (`onOk_retire_push`) and stack-pointer arithmetic
in the normal form `x - lit`. -/
macro "sv " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| seg_vc8 [Silmaril.Apps.Sha256sum.Binary.Startup.onOk_retire_push,
    Silmaril.Apps.Sha256sum.Binary.Startup.sub_sub_lit, BitVec.sub_sub, BitVec.reduceAnd,
    BitVec.reduceBEq, BitVec.and_self, Silmaril.Apps.Sha256sum.Binary.Startup.setWidth_8_64,
    Silmaril.Apps.Sha256sum.Binary.Startup.setWidth_8_64_32,
    Silmaril.Apps.Sha256sum.Binary.Startup.setWidth_64_32, false_implies,
    Silmaril.Apps.Sha256sum.Binary.Startup.ofNat_shl, Nat.reduceShiftLeft,
    Silmaril.Apps.Sha256sum.Binary.Startup.execNew_aluR, Silmaril.Apps.Sha256sum.Binary.Startup.rm8_read_mem,
    Silmaril.X86.Ext.Base.value_rip, Silmaril.X86.Ext.Base.value_none, Silmaril.X86.Ext.Mem.ofRip,
    Silmaril.X86.Ext.Mem.ofIndex, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Lift.ix,
    Silmaril.Apps.Sha256sum.Binary.Startup.write_write_same, $ls,*])

/-- Span arithmetic over the context. -/
macro "sv_disj" : tactic => `(tactic| ((try simp only [Silmaril.Apps.Sha256sum.Binary.Startup.Start.base_toNat, Silmaril.Apps.Sha256sum.Binary.Startup.Main.base_toNat, Silmaril.Apps.Sha256sum.Binary.Startup.Call.base_toNat, Silmaril.Apps.Sha256sum.Binary.Startup.Digest.base_toNat, Silmaril.Machine.LittleEndian.encodeWords_length,
  Silmaril.X86.length_encodeWords_singleton, Silmaril.X86.Ext.length_leBytes, List.length_cons,
  List.length_nil, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
  Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd]) <;> omega))

namespace Silmaril.Apps.Sha256sum.Binary.Startup

open Lean Elab Tactic Meta

/-- The store hypothesis that produced memory `e`: `X.writeBytes _ _ = some e` or
`storeN X _ _ _ = some e`, with `true` for a `storeN`. -/
meta def findProducer (e : Lean.Expr) : TacticM (Option (Lean.Expr × Bool)) := withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isAppOfArity ``Option.some 2 do continue
    let isWb := lhs.isAppOfArity ``Silmaril.Process.Memory.writeBytes 3
    let isSt := lhs.isAppOfArity ``Silmaril.X86.Ext.storeN 4
    unless isWb || isSt do continue
    if ← withReducible (isDefEq (rhs.getArg! 1) e) then return some (d.toExpr, isSt)
  return none

/-- The memory a goal is about: `Permitted` (0), `loadN _ = _` (1), `WritesWithin` (2). -/
meta def goalMem (g : Lean.Expr) : Option (Nat × Lean.Expr) :=
  if g.isAppOfArity ``Silmaril.Process.Memory.Permitted 4 then some (0, g.getArg! 0)
  else if g.isAppOfArity ``Silmaril.Process.Memory.WritesWithin 3 then some (2, g.getArg! 1)
  else match g.eq? with
    | some (_, lhs, _) =>
      if lhs.isAppOfArity ``Silmaril.X86.Ext.loadN 3 then some (1, lhs.getArg! 0) else none
    | none => none

end Silmaril.Apps.Sha256sum.Binary.Startup

open Lean Elab Tactic Meta in
/-- `sv_perm`: a permission of the current memory, through the stores that produced it, as a
sub-span of a context hypothesis (bounds by `sv_disj`). -/
elab "sv_perm" : tactic => do
  for _ in [0:200] do
    let progress ← withMainContext do
      let g ← instantiateMVars (← getMainTarget)
      unless g.isAppOfArity ``Silmaril.Process.Memory.Permitted 4 do return false
      let some (h, isSt) ← Silmaril.Apps.Sha256sum.Binary.Startup.findProducer (g.getArg! 0)
        | return false
      let hs ← Term.exprToSyntax h
      if isSt then
        evalTactic (← `(tactic| refine Silmaril.Apps.Sha256sum.Binary.Startup.perm_st $hs ?_))
      else
        evalTactic (← `(tactic| refine Silmaril.Apps.Sha256sum.Binary.Startup.perm_wb $hs ?_))
      return true
    unless progress do break
  withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  unless g.isAppOfArity ``Silmaril.Process.Memory.Permitted 4 do
    throwError "sv_perm: not a permission goal"
  let mem := g.getArg! 0
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Silmaril.Process.Memory.Permitted 4 then
      if ← withReducible (isDefEq (ty.getArg! 0) mem) then
        if ← withReducible (isDefEq (ty.getArg! 1) (g.getArg! 1)) then
          let hs ← Term.exprToSyntax d.toExpr
          let ok ← (Term.withoutErrToSorry <| withoutRecover do
            evalTactic (← `(tactic|
              (refine Silmaril.X86.Ext.Memory.Permitted.sub $hs (by decide) ?_ ?_ <;> sv_disj)))
            pure true) <|> pure false
          if ok then return
  throwError "sv_perm: no hypothesis covers the span"

open Lean Elab Tactic Meta in
/-- `sv_mem`: carry a fact about the current memory (a permission, a load, a footprint) back
through the stores that produced it, down to a memory the context knows about; span side
conditions by `sv_disj`. A load through a store to the same span is read back
(`loadN_wb_word`, `loadN_st_same`, the read permission by `sv_mem`). Then a permission is a
sub-span of a context hypothesis, anything else an assumption. -/
elab "sv_mem" : tactic => do
  for _ in [0:200] do
    let progress ← withMainContext do
      let g ← instantiateMVars (← getMainTarget)
      let some (kind, mem) := Silmaril.Apps.Sha256sum.Binary.Startup.goalMem g | return false
      let some (h, isSt) ← Silmaril.Apps.Sha256sum.Binary.Startup.findProducer mem | return false
      let hs ← Term.exprToSyntax h
      match kind with
      | 0 =>
        if isSt then
          evalTactic (← `(tactic| refine Silmaril.Apps.Sha256sum.Binary.Startup.perm_st $hs ?_))
        else
          evalTactic (← `(tactic| refine Silmaril.Apps.Sha256sum.Binary.Startup.perm_wb $hs ?_))
        return true
      | 2 =>
        if isSt then
          evalTactic (← `(tactic|
            refine Silmaril.Apps.Sha256sum.Binary.Startup.ww_st $hs ?_ ?_))
        else
          evalTactic (← `(tactic|
            refine Silmaril.Apps.Sha256sum.Binary.Startup.ww_wb $hs ?_ ?_))
        return true
      | _ =>
        let ok ← (Term.withoutErrToSorry <| withoutRecover do
          if isSt then
            evalTactic (← `(tactic|
              rw [Silmaril.Apps.Sha256sum.Binary.Startup.loadN_st_disj $hs (by sv_disj)]))
          else
            evalTactic (← `(tactic|
              rw [Silmaril.Apps.Sha256sum.Binary.Startup.loadN_wb_disj $hs (by sv_disj)]))
          pure true) <|> pure false
        if ok then return true
        let ok ← (Term.withoutErrToSorry <| withoutRecover do
          if isSt then
            evalTactic (← `(tactic|
              rw [Silmaril.Apps.Sha256sum.Binary.Startup.loadN_st_same $hs (by sv_perm)]))
          else
            evalTactic (← `(tactic|
              rw [Silmaril.Apps.Sha256sum.Binary.Startup.loadN_wb_word $hs (by sv_perm)]))
          pure true) <|> pure false
        return ok
    unless progress do break
  withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  if g.isAppOfArity ``Silmaril.Process.Memory.Permitted 4 then
    evalTactic (← `(tactic| sv_perm))
  else
    try evalTactic (← `(tactic| with_reducible assumption)) catch _ => pure ()

open Lean Elab Tactic Meta in
/-- Close a leaf of the VC by its head: a loaded code region (`st_loaded`), a permission
(`sv_perm`), `Ro` (`st_ro`); anything else is left. -/
elab "sv_close" : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  if g.isAppOfArity ``Silmaril.X86.Ext.Loaded 3 then
    try evalTactic (← `(tactic| (st_loaded; done))) catch _ => pure ()
  else if g.isAppOfArity ``Silmaril.Process.Memory.Permitted 4 then
    try evalTactic (← `(tactic| sv_perm)) catch _ => pure ()
  else if g.isAppOfArity ``Silmaril.Apps.Sha256sum.Binary.Startup.Ro 1 then
    try evalTactic (← `(tactic| (st_ro; done))) catch _ => pure ()

open Lean Elab Tactic Meta in
/-- One structural step of `sv_split`: split a syntactic `And`, introduce a store's
`∀ after, _ = some after → _` or a branch condition `(_ : Bool) = _ → _`. Definitions (a
postcondition, a cut invariant, a footprint) are not unfolded. -/
elab "sv_split1" : tactic => withMainContext do
  let g := (← instantiateMVars (← getMainTarget)).consumeMData
  if g.isAppOfArity ``And 2 then
    evalTactic (← `(tactic| refine And.intro ?_ ?_))
  else if g.isForall then
    let .forallE _ ty body _ := g | throwError "sv_split1"
    let ty := ty.consumeMData
    if ty.isConstOf ``Silmaril.Process.Memory then
      evalTactic (← `(tactic| intro _ _))
    else if !body.hasLooseBVars && (ty.eq?.map (fun (t, _, _) => t.isConstOf ``Bool)).getD false then
      evalTactic (← `(tactic| intro _))
    else throwError "sv_split1: not a store or a branch"
  else throwError "sv_split1: nothing to split"

/-- After `sv`: split the conjunctions, the stores' `∀ after` and the branch conditions of
the remaining VC, and close the code-loaded goals, the permissions and `Ro` (`sv_close`). -/
macro "sv_split" : tactic => `(tactic| ((repeat' sv_split1) <;> sv_close))

namespace Silmaril.Apps.Sha256sum.Binary.Startup

open Lean Elab Tactic Meta

/-- The first `loadN M a k` of `e` (closed) whose memory `M` satisfies `ok`. -/
meta def findLoad (e : Lean.Expr) (ok : Lean.Expr → Bool) : Option Lean.Expr :=
  e.find? fun t => t.isAppOfArity ``Silmaril.X86.Ext.loadN 3 && !t.hasLooseBVars &&
    ok (t.getArg! 0)

end Silmaril.Apps.Sha256sum.Binary.Startup

open Lean Elab Tactic Meta in
/-- `sv_ld`: resolve the loads of the goal: each `loadN M a k` whose memory was produced by a
store is carried back through that store (`loadN_wb_disj`/`loadN_st_disj` for a disjoint
span, `loadN_wb_word`/`loadN_st_same` for the same span), and a load of a memory without a
producer is rewritten by a context fact `loadN M a k = _`, if there is one. -/
elab "sv_ld" : tactic => do
  let mut fuel := 400
  while fuel > 0 do
    fuel := fuel - 1
    let progress ← withMainContext do
      let g ← instantiateMVars (← getMainTarget)
      -- loads of produced memories
      let lctx ← getLCtx
      let mut prods : Array (Lean.Expr × Lean.Expr × Bool) := #[]
      for d in lctx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        let some (_, lhs, rhs) := ty.eq? | continue
        unless rhs.isAppOfArity ``Option.some 2 do continue
        let isWb := lhs.isAppOfArity ``Silmaril.Process.Memory.writeBytes 3
        let isSt := lhs.isAppOfArity ``Silmaril.X86.Ext.storeN 4
        unless isWb || isSt do continue
        prods := prods.push (rhs.getArg! 1, d.toExpr, isSt)
      let isProduced := fun (m : Lean.Expr) => prods.any fun p => p.1 == m
      if let some ld := Silmaril.Apps.Sha256sum.Binary.Startup.findLoad g isProduced then
        let some (_, h, isSt) := prods.find? fun p => p.1 == ld.getArg! 0 | return false
        let hs ← Term.exprToSyntax h
        let lds ← Term.exprToSyntax ld
        let tryRw (t : TSyntax `term) : TacticM Bool := do
          let ok ← (Term.withoutErrToSorry <| withoutRecover do
            evalTactic (← `(tactic| (have e : $lds = _ := $t; rw [e]; clear e)))
            pure true) <|> pure false
          if ok then return true
          (Term.withoutErrToSorry <| withoutRecover do
              evalTactic (← `(tactic| (have e : $lds = _ := $t; simp only [e]; clear e)))
              pure true) <|> pure false
        if isSt then
          if ← tryRw (← `(Silmaril.Apps.Sha256sum.Binary.Startup.loadN_st_disj $hs (by sv_disj))) then return true
          if ← tryRw (← `(Silmaril.Apps.Sha256sum.Binary.Startup.loadN_st_same $hs (by sv_perm))) then return true
        else
          if ← tryRw (← `(Silmaril.Apps.Sha256sum.Binary.Startup.loadN_wb_disj $hs (by sv_disj))) then return true
          if ← tryRw (← `(Silmaril.Apps.Sha256sum.Binary.Startup.loadN_wb_word $hs (by sv_perm))) then return true
        throwError m!"sv_ld: cannot carry {ld} through its store"
      -- loads with a context fact
      for d in lctx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        let some (_, lhs, _) := ty.eq? | continue
        unless lhs.isAppOfArity ``Silmaril.X86.Ext.loadN 3 do continue
        if (g.find? fun t => t == lhs).isSome then
          let hs ← Term.exprToSyntax d.toExpr
          let ok ← (Term.withoutErrToSorry <| withoutRecover do evalTactic (← `(tactic| rw [$hs:term])); pure true) <|>
            (Term.withoutErrToSorry <| withoutRecover do evalTactic (← `(tactic| simp only [$hs:term])); pure true) <|> pure false
          if ok then return true
      return false
    unless progress do break

namespace Silmaril.Apps.Sha256sum.Binary.Startup

open Silmaril.X86 (Word)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (loadN)

/-- A load outside a footprint reads what the earlier memory held. -/
theorem loadN_ww {m0 m : Memory} {W : Nat → Prop} (h : Memory.WritesWithin m0 m W) {a : Word}
    {k : Nat} (hout : ∀ i < k, ¬ W (a.toNat + i)) : loadN m a k = loadN m0 a k := by
  simp only [loadN, Memory.readBytes, h.readWith hout]


end Silmaril.Apps.Sha256sum.Binary.Startup

/-- `sv_go [lemmas]`: `sv`, `sv_split`, `sv_ld`, repeated (at most 40 rounds) until the paths
are through: a load of a memory produced by a store is resolved between two rounds. -/
macro "sv_go " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (sv [$ls,*]; sv_split; all_goals (try sv_ld); iterate 40 (all_goals (try (sv [$ls,*]; sv_split; all_goals (try sv_ld))))))

open Lean Elab Tactic Meta in
/-- `sv_split1` that also substitutes a branch condition `(x == y) = true` (an equality of a
byte with a literal) into the goal, so a later test of the same byte is decided. -/
elab "sv_split1'" : tactic => withMainContext do
  let g := (← instantiateMVars (← getMainTarget)).consumeMData
  if g.isForall then
    let .forallE _ ty body _ := g | throwError "sv_split1'"
    let ty := ty.consumeMData
    if !body.hasLooseBVars && (ty.eq?.map (fun (t, _, _) => t.isConstOf ``Bool)).getD false then
      let h := mkIdent (← mkFreshUserName `hb)
      evalTactic (← `(tactic| intro $h:ident))
      try evalTactic (← `(tactic| (simp only [Bool.not_eq_false', Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne] at $h:ident; simp only [$h:ident])))
      catch _ => pure ()
      return
  evalTactic (← `(tactic| sv_split1))

/-- `sv_go` whose branch conditions are substituted (`sv_split1'`). -/
macro "sv_go' " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (sv [$ls,*]; ((repeat' sv_split1') <;> sv_close); all_goals (try sv_ld); iterate 40 (all_goals (try (sv [$ls,*]; ((repeat' sv_split1') <;> sv_close); all_goals (try sv_ld))))))
