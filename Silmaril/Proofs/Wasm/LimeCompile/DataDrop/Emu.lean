module

public import Silmaril.Wasm.LimeCompile.DataDrop.Defs
public import Silmaril.Wasm.LimeCompile.PassiveData.Thms

/-!
# The container with `data.drop`: the emulation

* `wrap_emulation`: one `memory.init 0 y` against a call of the dispatcher of `y`. The dispatcher
  reads the dropped flag and calls the empty helper (flag set) or the full helper (flag clear);
  the source's data instance holds the full bytes exactly when the flag is clear. The inner call
  is an earlier `memoryInit_emulation`, at the dispatcher's frame.
* `drop_emulation`: one `data.drop y` (the source empties the data instance) against a call of
  `$drop_y` (the target sets the flag).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.DataDrop

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.PassiveData (idx helperBody)
open Silmaril.Wasm.LimeCompile.DataDrop
open Silmaril.Proofs.Wasm.LimeCompile.PassiveData (I32 MemOk HelperAt hframe r_localGet r_ifTrue
  r_ifFalse r_block r_label r_labelVals r_trapLabel r_frame r_frameNil r_call run1 frame_trap)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The function at address `aw` of `t` is the dispatcher over the helpers at indices `full` and
`empty` and the flag at index `flag`, which its module resolves to `a1`, `a0` and `ga`. -/
def WrapAt (t : Store H) (aw full empty flag a1 a0 ga : Nat) : Prop :=
  ∃ (fi : FuncInst H) (code : Func) (ps rs : Ty (.list .val)),
    t.funcs[aw]? = some fi ∧ Expand fi.type (.func ps rs) ∧ ps.length = 3 ∧ rs.length = 0 ∧
    fi.code = .wasm code ∧ code.locals = [] ∧ code.body = wrapBody full empty flag ∧
    fi.module.funcs[(idx full : FuncIdx).toNat]? = some a1 ∧
    fi.module.funcs[(idx empty : FuncIdx).toNat]? = some a0 ∧
    fi.module.globals[(idx flag : GlobalIdx).toNat]? = some ga

/-- The function at address `ad` of `t` is `$drop` for the flag at index `flag`, which its
module resolves to `ga`. -/
def DropAt (t : Store H) (ad flag ga : Nat) : Prop :=
  ∃ (fi : FuncInst H) (code : Func) (ps rs : Ty (.list .val)),
    t.funcs[ad]? = some fi ∧ Expand fi.type (.func ps rs) ∧ ps.length = 0 ∧ rs.length = 0 ∧
    fi.code = .wasm code ∧ code.locals = [] ∧ code.body = dropBody flag ∧
    fi.module.globals[(idx flag : GlobalIdx).toNat]? = some ga

theorem r_globalGet {t : Store H} {F : Frame} {vs : List Val} {rest : List Admin} {x : GlobalIdx}
    {ga : Nat} {gi : GlobalInst} (hx : t.global? F x = some (ga, gi)) :
    Steps P host ⟨t, F, vals vs ++ (.plain (.globalGet x) :: rest)⟩
      ⟨t, F, vals (vs ++ [gi.value]) ++ rest⟩ := by
  have h := run1 (P := P) (host := host) (vs := vs) (rest := rest)
    (Step.variable (P := P) (host := host) (.globalGet (s := t) hx))
  simpa [vals] using h

/-- Calling the dispatcher: its frame around its body. -/
theorem wrap_enter {t : Store H} {g : Frame} {aw full empty flag a1 a0 ga hw : Nat}
    (hW : WrapAt t aw full empty flag a1 a0 ga)
    (hg : g.module.funcs[(idx hw : FuncIdx).toNat]? = some aw) (i j n : BitVec 32) :
    ∃ mod : ModuleInst, mod.funcs[(idx full : FuncIdx).toNat]? = some a1 ∧
      mod.funcs[(idx empty : FuncIdx).toNat]? = some a0 ∧
      mod.globals[(idx flag : GlobalIdx).toNat]? = some ga ∧
      Steps P host ⟨t, g, vals [I32 i, I32 j, I32 n] ++ [.plain (.call (idx hw))]⟩
        ⟨t, g, [.frame 0 (hframe mod i j n) [.label 0 [] (expression (wrapBody full empty flag))]]⟩ := by
  obtain ⟨fi, code, ps, rs, hf, he, hps, hrs, hcode, hloc, hbody, h1, h0, hgl⟩ := hW
  refine ⟨fi.module, h1, h0, hgl, ?_⟩
  have s := r_call (P := P) (host := host) (t := t) (F := g) (vs := []) (rest := [])
    (args := [I32 i, I32 j, I32 n]) hg hf he (by simp [hps]) hcode
  rw [hrs, hloc, hbody] at s
  simpa [Frame.forCall, vals] using s

/-- The two branches of the dispatcher. -/
abbrev branch (k : Nat) : List Instr :=
  [.localGet (idx 0), .localGet (idx 1), .localGet (idx 2), .call (idx k)]

/-- A branch pushes `i j n` and reaches its call. -/
theorem branch_run {t : Store H} {mod : ModuleInst} {i j n : BitVec 32} (k : Nat) :
    Steps P host ⟨t, hframe mod i j n, [.label 0 [] (expression (branch k))]⟩
      ⟨t, hframe mod i j n, [.label 0 [] (vals [I32 i, I32 j, I32 n] ++ [.plain (.call (idx k))])]⟩ := by
  have l0 : Steps P host ⟨t, hframe mod i j n, vals [] ++ (.plain (.localGet (idx 0)) ::
      [.plain (.localGet (idx 1)), .plain (.localGet (idx 2)), .plain (.call (idx k))])⟩
      ⟨t, hframe mod i j n, vals [I32 i] ++
        [.plain (.localGet (idx 1)), .plain (.localGet (idx 2)), .plain (.call (idx k))]⟩ :=
    r_localGet (x := idx 0) (v := I32 i) rfl
  have l1 : Steps P host ⟨t, hframe mod i j n, vals [I32 i] ++ (.plain (.localGet (idx 1)) ::
      [.plain (.localGet (idx 2)), .plain (.call (idx k))])⟩
      ⟨t, hframe mod i j n, vals [I32 i, I32 j] ++ [.plain (.localGet (idx 2)), .plain (.call (idx k))]⟩ :=
    r_localGet (x := idx 1) (v := I32 j) rfl
  have l2 : Steps P host ⟨t, hframe mod i j n, vals [I32 i, I32 j] ++
      (.plain (.localGet (idx 2)) :: [.plain (.call (idx k))])⟩
      ⟨t, hframe mod i j n, vals [I32 i, I32 j, I32 n] ++ [.plain (.call (idx k))]⟩ :=
    r_localGet (x := idx 2) (v := I32 n) rfl
  have l : Steps P host ⟨t, hframe mod i j n, expression (branch k)⟩
      ⟨t, hframe mod i j n, vals [I32 i, I32 j, I32 n] ++ [.plain (.call (idx k))]⟩ := by
    simpa [expression, vals] using l0.trans (l1.trans l2)
  exact r_label (vs := []) (rest := []) (n := 0) (cont := []) l |>.trans (by simp [vals]; exact .refl)

/-- The `if` on the flag enters the empty branch if the flag is set, else the full one. -/
theorem if_run {t : Store H} {F : Frame} (v : BitVec 32) (b₁ b₂ : List Instr) :
    Steps P host ⟨t, F, vals [I32 v] ++ [.plain (.if_ .empty b₁ b₂)]⟩
      ⟨t, F, [.label 0 [] (expression (if v = 0 then b₂ else b₁))]⟩ := by
  by_cases h0 : v = 0
  · have s2 : Steps P host ⟨t, F, vals ([] ++ [I32 v]) ++ (.plain (.if_ .empty b₁ b₂) :: [])⟩
        ⟨t, F, vals [] ++ (.plain (.block .empty b₂) :: [])⟩ := h0 ▸ r_ifFalse
    have s3 : Steps P host ⟨t, F, vals [] ++ (.plain (.block .empty b₂) :: [])⟩
        ⟨t, F, vals [] ++ (.label 0 [] (expression b₂) :: [])⟩ := r_block
    rw [ite_eq_left h0]
    simpa using s2.trans s3
  · have s2 : Steps P host ⟨t, F, vals ([] ++ [I32 v]) ++ (.plain (.if_ .empty b₁ b₂) :: [])⟩
        ⟨t, F, vals [] ++ (.plain (.block .empty b₁) :: [])⟩ := r_ifTrue h0
    have s3 : Steps P host ⟨t, F, vals [] ++ (.plain (.block .empty b₁) :: [])⟩
        ⟨t, F, vals [] ++ (.label 0 [] (expression b₁) :: [])⟩ := r_block
    rw [ite_eq_right h0]
    simpa using s2.trans s3

/-- The dispatcher's body up to the inner call: read the flag and enter the chosen branch. -/
theorem wrap_branch {t : Store H} {mod : ModuleInst} {full empty flag ga : Nat} {gi : GlobalInst}
    {v : BitVec 32} {i j n : BitVec 32} (hgl : mod.globals[(idx flag : GlobalIdx).toNat]? = some ga)
    (hgi : t.globals[ga]? = some gi) (hv : gi.value = I32 v) :
    Steps P host ⟨t, hframe mod i j n, expression (wrapBody full empty flag)⟩
      ⟨t, hframe mod i j n, [.label 0 [] (vals [I32 i, I32 j, I32 n] ++
        [.plain (.call (idx (if v = 0 then full else empty)))])]⟩ := by
  have hx : t.global? (hframe mod i j n) (idx flag) = some (ga, gi) := by
    simp [Store.global?, hgl, hgi]
  have s1 : Steps P host ⟨t, hframe mod i j n, expression (wrapBody full empty flag)⟩
      ⟨t, hframe mod i j n, vals [I32 v] ++ [.plain (.if_ .empty (branch empty) (branch full))]⟩ := by
    have := r_globalGet (P := P) (host := host) (vs := [])
      (rest := [.plain (.if_ .empty (branch empty) (branch full))]) hx
    simpa [wrapBody, expression, hv] using this
  have s2 : Steps P host ⟨t, hframe mod i j n,
      vals [I32 v] ++ [.plain (.if_ .empty (branch empty) (branch full))]⟩
      ⟨t, hframe mod i j n, [.label 0 [] (expression (branch (if v = 0 then full else empty)))]⟩ := by
    have h := if_run (P := P) (host := host) (t := t) (F := hframe mod i j n) v (branch empty)
      (branch full)
    by_cases h0 : v = 0
    · rw [ite_eq_left h0] at h ⊢
      exact h
    · rw [ite_eq_right h0] at h ⊢
      exact h
  exact s1.trans (s2.trans (branch_run _))

/-- **`memory.init 0 y` against a call of the dispatcher of `y`.** The source's data instance
holds the full bytes `bs` if the flag `v` is clear and nothing if it is set. -/
theorem wrap_emulation {y : DataIdx} {da ma aw a1 a0 ga hw full empty flag : Nat} {di : DataInst}
    {mi : MemInst} {bs : List UInt8} {s t : Store H} {f g : Frame} {i j n : BitVec 32}
    {gi : GlobalInst} {v : BitVec 32}
    (hm : s.mem? f (idx 0) = some (ma, mi)) (hmi : MemOk mi) (hd : s.data? f y = some (da, di))
    (hbs : bs.length ≤ 2 ^ 32) (hdi : di.bytes.data.toList = if v = 0 then bs else [])
    (htm : t.mems = s.mems) (hW : WrapAt t aw full empty flag a1 a0 ga)
    (hF : HelperAt t a1 full ma bs) (hE : HelperAt t a0 empty ma [])
    (hgi : t.globals[ga]? = some gi) (hv : gi.value = I32 v)
    (hg : g.module.funcs[(idx hw : FuncIdx).toNat]? = some aw) :
    (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size →
      ∃ s', Steps P host ⟨s, f, [constI32 i, constI32 j, constI32 n, .plain (.memoryInit (idx 0) y)]⟩
          ⟨s', f, []⟩ ∧
        Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n, .plain (.call (idx hw))]⟩
          ⟨{ t with mems := s'.mems }, g, []⟩) ∧
    (¬ (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size) →
      Step P host ⟨s, f, [constI32 i, constI32 j, constI32 n, .plain (.memoryInit (idx 0) y)]⟩
          ⟨s, f, [.trap]⟩ ∧
        Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n, .plain (.call (idx hw))]⟩
          ⟨t, g, [.trap]⟩) := by
  obtain ⟨mod, h1, h0, hgl, hent⟩ := wrap_enter (P := P) (host := host) hW hg i j n
  have hbr := wrap_branch (P := P) (host := host) (full := full) (empty := empty) (i := i)
    (j := j) (n := n) hgl hgi hv
  -- the chosen helper, at the dispatcher's frame
  have hH : HelperAt t (if v = 0 then a1 else a0) (if v = 0 then full else empty) ma
      (if v = 0 then bs else []) := by
    by_cases h : v = 0 <;> simp only [h, ↓reduceIte] <;> assumption
  have hmod : (hframe mod i j n).module.funcs[(idx (if v = 0 then full else empty) :
      FuncIdx).toNat]? = some (if v = 0 then a1 else a0) := by
    by_cases h : v = 0 <;> simp only [h, ↓reduceIte] <;> assumption
  have hbs' : (if v = 0 then bs else []).length ≤ 2 ^ 32 := by
    by_cases h : v = 0 <;> simp only [h, ↓reduceIte] <;> simp_all
  obtain ⟨hok, hoob⟩ := Silmaril.Wasm.LimeCompile.PassiveData.memoryInit_emulation (P := P)
    (host := host) (i := i) (j := j) (n := n) hm hmi hd hdi hbs' htm hH hmod
  -- the code around the inner call
  have hin : ∀ (t' : Store H) (r : List Admin),
      Steps P host ⟨t, hframe mod i j n, [constI32 i, constI32 j, constI32 n,
        .plain (.call (idx (if v = 0 then full else empty)))]⟩ ⟨t', hframe mod i j n, r⟩ →
      Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n, .plain (.call (idx hw))]⟩
        ⟨t', g, [.frame 0 (hframe mod i j n) [.label 0 [] [.label 0 [] r]]]⟩ := by
    intro t' r hr
    have l1 := r_label (P := P) (host := host) (vs := []) (rest := []) (n := 0) (cont := []) hr
    have l2 := r_label (P := P) (host := host) (vs := []) (rest := []) (n := 0) (cont := [])
      (hbr.trans (by simpa [vals, constI32, Val.i32] using l1))
    have l3 := r_frame (P := P) (host := host) (F := g) (vs := []) (rest := []) (n := 0) l2
    simp only [vals, List.map_nil, List.nil_append] at hent l3
    simpa [vals, constI32, Val.i32] using hent.trans l3
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · obtain ⟨s', hs', ht'⟩ := hok hb
    refine ⟨s', hs', (hin _ _ ht').trans ?_⟩
    have e1 := r_labelVals (P := P) (host := host) (t := { t with mems := s'.mems })
      (F := hframe mod i j n) (vs := []) (us := []) (rest := []) (n := 0) (cont := [])
    have e2 := r_labelVals (P := P) (host := host) (t := { t with mems := s'.mems })
      (F := hframe mod i j n) (vs := []) (us := []) (rest := []) (n := 0) (cont := [])
    have e12 := r_frame (P := P) (host := host) (F := g) (vs := []) (rest := []) (n := 0)
      (r_label (P := P) (host := host) (vs := []) (rest := []) (n := 0) (cont := [])
        (by simpa [vals] using e1))
    have e3 := r_frame (P := P) (host := host) (F := g) (vs := []) (rest := []) (n := 0)
      (by simpa [vals] using e2)
    have e4 := r_frameNil (P := P) (host := host) (t := { t with mems := s'.mems }) (F := g)
      (Fi := hframe mod i j n) (vs := []) (rest := [])
    simp only [vals, List.map_nil, List.nil_append, List.append_nil] at e12 e3 e4
    exact e12.trans (e3.trans e4)
  · obtain ⟨hs, ht⟩ := hoob hb
    refine ⟨hs, ?_⟩
    have hx := hin _ _ ht
    have e1 := r_trapLabel (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
      (rest := []) (n := 0) (cont := [])
    have hbody : Steps P host ⟨t, hframe mod i j n, [.label 0 [] [.trap]]⟩
        ⟨t, hframe mod i j n, [.trap]⟩ := by simpa [vals] using e1
    exact hx.trans (frame_trap hbody)

/-- **`data.drop y` against a call of `$drop_y`.** The source empties the data instance, the
target sets the flag. -/
theorem drop_emulation {y : DataIdx} {da ad ga hdrop flag : Nat} {di : DataInst} {s t : Store H}
    {f g : Frame} {gi : GlobalInst} (hd : s.data? f y = some (da, di))
    (hD : DropAt t ad flag ga) (hgi : t.globals[ga]? = some gi)
    (hg : g.module.funcs[(idx hdrop : FuncIdx).toNat]? = some ad) :
    Step P host ⟨s, f, [.plain (.dataDrop y)]⟩ ⟨s.setData da ByteArray.empty, f, []⟩ ∧
      Steps P host ⟨t, g, [.plain (.call (idx hdrop))]⟩ ⟨t.setGlobal ga (I32 1), g, []⟩ := by
  refine ⟨Step.memory (.dataDrop hd), ?_⟩
  obtain ⟨fi, code, ps, rs, hf, he, hps, hrs, hcode, hloc, hbody, hgl⟩ := hD
  let F : Frame := Frame.forCall fi.module [] []
  have s1 : Steps P host ⟨t, g, [.plain (.call (idx hdrop))]⟩
      ⟨t, g, [.frame 0 F [.label 0 [] (expression (dropBody flag))]]⟩ := by
    have := r_call (P := P) (host := host) (t := t) (F := g) (vs := []) (rest := []) (args := [])
      hg hf he (by simp [hps]) hcode
    simpa [hrs, hloc, hbody, vals, F] using this
  have hx : t.global? F (idx flag) = some (ga, gi) := by
    simp [Store.global?, F, Frame.forCall, hgl, hgi]
  have s2 : Steps P host ⟨t, F, expression (dropBody flag)⟩ ⟨t.setGlobal ga (I32 1), F, []⟩ :=
    (Step.variable (.globalSet (v := I32 1) hx)).steps
  have s3 : Steps P host ⟨t, F, [.label 0 [] (expression (dropBody flag))]⟩
      ⟨t.setGlobal ga (I32 1), F, []⟩ := by
    have l := r_label (P := P) (host := host) (vs := []) (rest := []) (n := 0) (cont := []) s2
    have e := r_labelVals (P := P) (host := host) (t := t.setGlobal ga (I32 1)) (F := F) (vs := [])
      (us := []) (rest := []) (n := 0) (cont := [])
    simpa [vals] using l.trans e
  have s4 : Steps P host ⟨t, g, [.frame 0 F [.label 0 [] (expression (dropBody flag))]]⟩
      ⟨t.setGlobal ga (I32 1), g, []⟩ := by
    have l := r_frame (P := P) (host := host) (F := g) (vs := []) (rest := []) (n := 0) s3
    have e := r_frameNil (P := P) (host := host) (t := t.setGlobal ga (I32 1)) (F := g) (Fi := F)
      (vs := []) (rest := [])
    simpa [vals] using l.trans e
  exact s1.trans s4

end Silmaril.Proofs.Wasm.LimeCompile.DataDrop
