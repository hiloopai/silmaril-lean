module

public import Silmaril.Wasm.LimeCompile.PassiveData.Defs
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInit
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryAux

/-!
# The passive-data container: single-instruction runs

Small `Steps` facts in the shape `vals vs ++ (instr :: rest)` → `vals vs' ++ rest`. Every one is a
single Core 3.0 rule lifted through `ctxt-instrs`. The emulation proof (`Emu.lean`) chains them
along the helper's straight-line code.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.PassiveData

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation Silmaril.Wasm.LimeCompile.PassiveData

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- An `i32` value. -/
abbrev I32 (b : BitVec 32) : Val := .num ⟨.int .i32, b⟩

/-- An `i64` value. -/
abbrev I64 (b : BitVec 64) : Val := .num ⟨.int .i64, b⟩

/-- A step of a small code lifted under a value prefix and a suffix. -/
theorem run1 {t t' : Store H} {F F' : Frame} {vs : List Val} {is is' rest : List Admin}
    (h : Step P host ⟨t, F, is⟩ ⟨t', F', is'⟩) :
    Steps P host ⟨t, F, vals vs ++ is ++ rest⟩ ⟨t', F', vals vs ++ is' ++ rest⟩ :=
  Steps.ctxtInstrs h.steps

theorem vals_snoc (vs : List Val) (v : Val) (rest : List Admin) :
    vals vs ++ (v.toAdmin :: rest) = vals (vs ++ [v]) ++ rest := by
  simp [vals]

/-- A constant is a value: pushing it takes no step. -/
theorem r_const {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} (it : IntType)
    (c : BitVec it.width) :
    Steps P host ⟨t, F, vals vs ++ (.plain (.intConst it c) :: rest)⟩
      ⟨t, F, vals (vs ++ [.num ⟨.int it, c⟩]) ++ rest⟩ := by
  rw [← vals_snoc]
  exact .refl

theorem r_localGet {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} {x : LocalIdx}
    {v : Val} (hx : F.local? x = some (some v)) :
    Steps P host ⟨t, F, vals vs ++ (.plain (.localGet x) :: rest)⟩
      ⟨t, F, vals (vs ++ [v]) ++ rest⟩ := by
  have h := run1 (vs := vs) (rest := rest)
    (Step.variable (P := P) (host := host) (.localGet (s := t) hx))
  simpa [vals] using h

theorem r_binop {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} {it : IntType}
    {op : IntBinOp} {x y z : BitVec it.width} (h : intBinOp it op x y = .ok z) :
    Steps P host ⟨t, F, vals (vs ++ [.num ⟨.int it, x⟩, .num ⟨.int it, y⟩]) ++
        (.plain (.intBinOp it op) :: rest)⟩
      ⟨t, F, vals (vs ++ [.num ⟨.int it, z⟩]) ++ rest⟩ := by
  have h' := run1 (vs := vs) (rest := rest)
    (Step.numeric (P := P) (host := host) (s := t) (f := F) (.intBinOp h))
  simpa [vals, Val.toAdmin] using h'

theorem r_relop {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} {it : IntType}
    (op : IntRelOp) (x y : BitVec it.width) :
    Steps P host ⟨t, F, vals (vs ++ [.num ⟨.int it, x⟩, .num ⟨.int it, y⟩]) ++
        (.plain (.intRelOp it op) :: rest)⟩
      ⟨t, F, vals (vs ++ [I32 (intRelOp it op x y)]) ++ rest⟩ := by
  have h' := run1 (vs := vs) (rest := rest)
    (Step.numeric (P := P) (host := host) (s := t) (f := F) (.intRelOp (op := op) (x := x) (y := y)))
  simpa [vals, Val.toAdmin, constI32, Val.i32] using h'

theorem r_extend {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} (x : BitVec 32) :
    Steps P host ⟨t, F, vals (vs ++ [I32 x]) ++ (.plain (.convert (.extend .unsigned)) :: rest)⟩
      ⟨t, F, vals (vs ++ [I64 (x.setWidth 64)]) ++ rest⟩ := by
  have hc : convertP P (.extend .unsigned) x (.ok (x.setWidth 64)) := by
    unfold convertP
    cases P.nan <;> rfl
  have h' : Steps P host ⟨t, F, vals vs ++ [(I32 x).toAdmin, .plain (.convert (.extend .unsigned))]
      ++ rest⟩ ⟨t, F, vals vs ++ [(I64 (x.setWidth 64)).toAdmin] ++ rest⟩ :=
    run1 (Step.numeric (.convert hc))
  simpa [vals] using h'

theorem r_select {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} (a b : Val)
    (c : BitVec 32) :
    Steps P host ⟨t, F, vals (vs ++ [a, b, I32 c]) ++ (.plain (.select none) :: rest)⟩
      ⟨t, F, vals (vs ++ [if c = 0 then b else a]) ++ rest⟩ := by
  by_cases hc : c = 0
  · subst hc
    have h' := run1 (vs := vs) (rest := rest)
      (Step.parametric (P := P) (host := host) (s := t) (f := F)
        (.selectFalse a b none))
    simpa [vals, constI32, Val.i32, I32] using h'
  · simp only [hc, ↓reduceIte]
    have h' := run1 (vs := vs) (rest := rest)
      (Step.parametric (P := P) (host := host) (s := t) (f := F)
        (.selectTrue (v₁ := a) (v₂ := b) (ts := none) hc))
    simpa [vals, constI32, Val.i32, I32, hc] using h'

theorem r_memorySize {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} {x : MemIdx}
    {ma : Nat} {mi : MemInst} (hm : t.mem? F x = some (ma, mi)) (ha : mi.type.address = .i32) :
    Steps P host ⟨t, F, vals vs ++ (.plain (.memorySize x) :: rest)⟩
      ⟨t, F, vals (vs ++ [I32 (BitVec.ofNat 32 mi.pages)]) ++ rest⟩ := by
  obtain ⟨⟨addr, lim⟩, bytes⟩ := mi
  simp only at ha
  subst ha
  have h' : Steps P host ⟨t, F, vals vs ++ [.plain (.memorySize x)] ++ rest⟩
      ⟨t, F, vals vs ++ [(I32 (BitVec.ofNat 32 (MemInst.pages ⟨⟨.i32, lim⟩, bytes⟩))).toAdmin] ++ rest⟩ :=
    run1 (Step.memory (.size hm))
  simpa [vals] using h'

theorem r_store8 {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} {ma : Nat}
    {mi : MemInst} {i c : BitVec 32} {b : ByteArray} (hm : t.mem? F (idx 0) = some (ma, mi))
    (hs : Memory.store mi.bytes (effAddr i.toNat memarg0) (count := PackSize.i8.width / 8)
      (c.setWidth _) = some b) :
    Steps P host ⟨t, F, vals (vs ++ [I32 i, I32 c]) ++
        (.plain store8I :: rest)⟩
      ⟨t.setMem ma { mi with bytes := b }, F, vals vs ++ rest⟩ := by
  have h' : Steps P host ⟨t, F, vals vs ++ [(I32 i).toAdmin, (I32 c).toAdmin,
      .plain (.intStore .i32 (some .i8) (idx 0) memarg0)] ++ rest⟩
      ⟨t.setMem ma { mi with bytes := b }, F, vals vs ++ [] ++ rest⟩ :=
    run1 (Step.memory (.storePackVal (t := .i32) (sz := .i8) (a := .i32) hm hs))
  simpa [vals, store8I, memarg0] using h'

theorem r_ifTrue {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} {c : BitVec 32}
    {bt : BlockType} {b₁ b₂ : List Instr} (hc : c ≠ 0) :
    Steps P host ⟨t, F, vals (vs ++ [I32 c]) ++ (.plain (.if_ bt b₁ b₂) :: rest)⟩
      ⟨t, F, vals vs ++ (.plain (.block bt b₁) :: rest)⟩ := by
  have h' := run1 (vs := vs) (rest := rest)
    (Step.ifTrue (P := P) (host := host) (s := t) (f := F) (bt := bt) (b₁ := b₁) (b₂ := b₂) hc)
  simpa [vals, constI32, Val.i32, I32] using h'

theorem r_ifFalse {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin}
    {bt : BlockType} {b₁ b₂ : List Instr} :
    Steps P host ⟨t, F, vals (vs ++ [I32 0]) ++ (.plain (.if_ bt b₁ b₂) :: rest)⟩
      ⟨t, F, vals vs ++ (.plain (.block bt b₂) :: rest)⟩ := by
  have h' := run1 (vs := vs) (rest := rest)
    (Step.ifFalse (P := P) (host := host) (s := t) (f := F) (bt := bt) (b₁ := b₁) (b₂ := b₂))
  simpa [vals, constI32, Val.i32, I32] using h'

theorem r_block {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin}
    {body : List Instr} :
    Steps P host ⟨t, F, vals vs ++ (.plain (.block .empty body) :: rest)⟩
      ⟨t, F, vals vs ++ (.label 0 [] (expression body) :: rest)⟩ := by
  have h' := run1 (vs := vs) (rest := rest)
    (Step.block (P := P) (host := host) (s := t) (f := F) (vs := []) (body := body)
      (bt := .empty) (t₁ := []) (t₂ := []) rfl rfl)
  simpa [vals] using h'

theorem r_label {t t' : Store H} {F F' : Frame} {vs : List Val} {rest : List Admin} {n : Nat}
    {cont : List Instr} {is is' : List Admin} (h : Steps P host ⟨t, F, is⟩ ⟨t', F', is'⟩) :
    Steps P host ⟨t, F, vals vs ++ (.label n cont is :: rest)⟩
      ⟨t', F', vals vs ++ (.label n cont is' :: rest)⟩ := by
  simpa using Steps.ctxtInstrs (vs := vs) (rest := rest) (Steps.label (n := n) (cont := cont) h)

theorem r_labelVals {t : Store H} {F : Frame} {vs us : List Val} {rest : List Admin} {n : Nat}
    {cont : List Instr} :
    Steps P host ⟨t, F, vals vs ++ (.label n cont (vals us) :: rest)⟩
      ⟨t, F, vals (vs ++ us) ++ rest⟩ := by
  have h' := run1 (vs := vs) (rest := rest)
    (Step.labelVals (P := P) (host := host) (s := t) (f := F) (n := n) (cont := cont) (vs := us))
  simpa [vals] using h'

theorem r_trapLabel {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} {n : Nat}
    {cont : List Instr} :
    Steps P host ⟨t, F, vals vs ++ (.label n cont [.trap] :: rest)⟩
      ⟨t, F, vals vs ++ (.trap :: rest)⟩ := by
  have h' := run1 (vs := vs) (rest := rest)
    (Step.trapLabel (P := P) (host := host) (s := t) (f := F) (n := n) (cont := cont))
  simpa using h'

theorem r_trap {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} :
    Steps P host ⟨t, F, vals vs ++ (.trap :: rest)⟩ ⟨t, F, [.trap]⟩ := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · simpa using (Step.trapInstrs (P := P) (host := host) (s := t) (f := F) hne).steps
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    exact .refl

theorem r_frame {t t' : Store H} {F Fi Fi' : Frame} {vs : List Val} {rest : List Admin} {n : Nat}
    {is is' : List Admin} (h : Steps P host ⟨t, Fi, is⟩ ⟨t', Fi', is'⟩) :
    Steps P host ⟨t, F, vals vs ++ (.frame n Fi is :: rest)⟩
      ⟨t', F, vals vs ++ (.frame n Fi' is' :: rest)⟩ := by
  simpa using Steps.ctxtInstrs (vs := vs) (rest := rest) (Steps.frame (f := F) (n := n) h)

theorem r_frameNil {t : Store H} {F Fi : Frame} {vs : List Val} {rest : List Admin} :
    Steps P host ⟨t, F, vals vs ++ (.frame 0 Fi [] :: rest)⟩ ⟨t, F, vals vs ++ rest⟩ := by
  have h' := run1 (vs := vs) (rest := rest)
    (Step.frameVals (P := P) (host := host) (s := t) (f := F) (fi := Fi) (vs := []) rfl)
  simpa [vals] using h'

theorem r_trapFrame {t : Store H} {F Fi : Frame} {vs : List Val} {rest : List Admin} {n : Nat} :
    Steps P host ⟨t, F, vals vs ++ (.frame n Fi [.trap] :: rest)⟩
      ⟨t, F, vals vs ++ (.trap :: rest)⟩ := by
  have h' := run1 (vs := vs) (rest := rest)
    (Step.trapFrame (P := P) (host := host) (s := t) (f := F) (fi := Fi) (n := n))
  simpa using h'

theorem r_call {t : Store H} {F : Frame} {vs args : List Val} {rest : List Admin} {x : FuncIdx}
    {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func}
    (hx : F.module.funcs[x.toNat]? = some a) (hf : t.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : args.length = ps.length)
    (hcode : fi.code = .wasm code) :
    Steps P host ⟨t, F, vals (vs ++ args) ++ (.plain (.call x) :: rest)⟩
      ⟨t, F, vals vs ++ (.frame rs.length (Frame.forCall fi.module args code.locals)
        [.label rs.length [] (expression code.body)] :: rest)⟩ := by
  have h1 := run1 (vs := vs ++ args) (rest := rest)
    (Step.call (P := P) (host := host) (s := t) (f := F) hx hf)
  have h2 := run1 (vs := vs) (rest := rest)
    (Step.callRefFunc (P := P) (host := host) (s := t) (f := F) (c := .callRefType fi.type)
      (vs := args) trivial hf he hn hcode)
  refine (by simpa using h1 : Steps P host _ _).trans ?_
  simpa [vals] using h2

end Silmaril.Proofs.Wasm.LimeCompile.PassiveData
