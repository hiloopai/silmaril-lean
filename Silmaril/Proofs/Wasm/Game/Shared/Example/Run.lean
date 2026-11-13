module

public import Silmaril.Proofs.Wasm.Game.Shared.Example.Instance
public import Silmaril.Proofs.Wasm.Game.Shared.Host

/-!
# The memory-writing example: the host and the run

* `poke_ok`, `pokeMem_load`: writing byte `42` keeps the store typed, extends it,
  keeps its functions, and is read back by a one-byte load (silmaril-lean's
  `Memory.load_store`).
* `logHost_ok`, `logHost_keeps`: the host satisfies `HostOk` and `HostKeeps`.
* `run_get`: for every profile, `$invoke(get)` runs under `logHost` to the value
  `i32 42`, in the store `poke s₀`: `call 0` reaches the host call, whose
  answer continues in the written store, and `i32.load8_u` reads the byte.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SharedExample

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.SharedExample Silmaril.Proofs.Wasm.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-! ### Writing the byte -/

theorem pokeMem_ok {mi : MemInst} (hok : MemInstOk mi) :
    MemInstOk (pokeMem mi) ∧ ExtendMem mi (pokeMem mi) := by
  unfold pokeMem
  split
  · rename_i b hb
    have hsz : b.size = mi.bytes.size := Memory.store_size hb
    exact ⟨⟨hok.1, hsz.trans hok.2⟩, ⟨rfl, rfl, Nat.le_refl _, hsz.ge⟩⟩
  · exact ⟨hok, ExtendMem.refl mi⟩

theorem poke_ok {s : Store Nat} (hs : StoreOk s) : StoreOk (poke s) ∧ Extend s (poke s) := by
  unfold poke
  split
  · rename_i mi hmi
    obtain ⟨h1, h2⟩ := pokeMem_ok (hs.mems mi (List.mem_of_getElem? hmi))
    exact StoreOk.setMem hs hmi h2 h1
  · exact ⟨hs, Extend.refl hs⟩

theorem poke_funcs (s : Store Nat) : (poke s).funcs = s.funcs := by
  unfold poke
  split <;> rfl

theorem poke_mem {s : Store Nat} {mi : MemInst} (hmi : s.mems[0]? = some mi) :
    (poke s).mems[0]? = some (pokeMem mi) := by
  have hlt : 0 < s.mems.length := (List.getElem?_eq_some_iff.mp hmi).1
  unfold poke
  rw [hmi]
  simp [Store.setMem, hlt]

theorem pokeMem_load {mi : MemInst} (hsz : 1 ≤ mi.bytes.size) :
    Silmaril.Wasm.Execution.Memory.load (pokeMem mi).bytes 0 1 = some 42 := by
  obtain ⟨b, hb⟩ := Memory.store_of_le (start := 0) (count := 1) (42 : BitVec (8 * 1))
    (by simpa using hsz)
  unfold pokeMem
  rw [hb]
  exact Silmaril.Wasm.Execution.Memory.load_store _ _ _ _ _ hb

/-! ### The host -/

theorem imports_get (i : Fin exLogI.imports.length) : exLogI.imports.get i = ⟨[], []⟩ := by
  obtain ⟨i, hi⟩ := i
  have h0 : i = 0 := by simp [exLogI] at hi; omega
  subst h0
  rfl

/-- At stores whose host functions are the imports, a host function returns no values. -/
theorem results_nil {s : Store Nat} (ht : exLogI.HostsTyped s) {fi : FuncInst Nat} {h : Nat}
    (hfi : fi ∈ s.funcs) (hcode : fi.code = .host h) {ps rs : Ty (.list .val)}
    (hexp : Expand fi.type (.func ps rs)) : rs = Ty.ofList [] := by
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hfi
  obtain ⟨hlt, hexp'⟩ := ht a fi h ha hcode
  rw [imports_get] at hexp'
  have hboth : ps = Ty.ofList [] ∧ rs = Ty.ofList [] := by
    simpa only [FnType.toComp, List.map_nil, Ty.func.injEq] using Expand.func_eq hexp hexp'
  exact hboth.2

/-- **The memory-writing host satisfies Core's host contract.** -/
theorem logHost_ok : HostOk logHost := by
  intro s fi h vs ps rs hs hfi hcode hexp _
  by_cases hc : h = 0 ∧ vs = [] ∧ exLogI.HostsTyped s
  · refine ⟨⟨_, .inl ⟨hc.1, hc.2.1, hc.2.2, rfl⟩⟩, ?_⟩
    rintro out (⟨-, -, -, rfl⟩ | ⟨hn, -⟩)
    · obtain ⟨hok, hext⟩ := poke_ok hs
      have hrs : rs = Ty.ofList [] := results_nil hc.2.2 hfi hcode hexp
      refine ⟨hok, hext, ?_⟩
      rw [hrs, Ty.toList_ofList]
      exact .nil
    · exact absurd hc hn
  · refine ⟨⟨_, .inr ⟨hc, rfl⟩⟩, ?_⟩
    rintro out (⟨h1, h2, h3, -⟩ | ⟨-, rfl⟩)
    · exact absurd ⟨h1, h2, h3⟩ hc
    · trivial

/-- The host keeps the functions of the store. -/
theorem logHost_keeps : exLogI.HostKeeps logHost := by
  refine Silmaril.Proofs.Wasm.Game.Shared.hostKeeps_of_funcs fun hh s vs s' r hr => ?_
  rcases hr with ⟨-, -, -, h⟩ | ⟨-, h⟩
  · cases h
    exact poke_funcs s
  · cases h

/-! ### The run -/

/-- Reading `isHost0`. -/
theorem isHost0_code {fi : FuncInst Nat} (h : isHost0 fi = true) : fi.code = .host 0 := by
  unfold isHost0 at h
  split at h
  · assumption
  · cases h

/-- Reading `isGetBody`. -/
theorem isGetBody_code {fi : FuncInst Nat} (h : isGetBody fi = true) :
    ∃ (t : TypeIdx) (x : FuncIdx) (y : MemIdx), fi.code = .wasm ⟨t, [], [.call x,
      .intConst .i32 0, .intLoad .i32 (some (.i8, .unsigned)) y memarg0]⟩ ∧
      x.toNat = 0 ∧ y.toNat = 0 := by
  unfold isGetBody at h
  split at h
  · rename_i t x k y arg hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hx, rfl⟩, hy⟩, rfl⟩ := h
    exact ⟨t, x, y, hc, hx, hy⟩
  · cases h

/-- A step of a head of the code, in front of a non-empty rest. -/
theorem step_head {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics Nat}
    {s s' : Store Nat} {f f' : Frame} {is is' rest : List Admin}
    (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (hr : rest ≠ []) :
    Step P host ⟨s, f, is ++ rest⟩ ⟨s', f', is' ++ rest⟩ := by
  simpa [vals] using Step.ctxtInstrs (vs := []) (rest := rest) h (.inr hr)

/-- The shape of the instance's store. -/
structure Shape (fi₀ fi₁ : FuncInst Nat) (t : TypeIdx) (x : FuncIdx) (y : MemIdx)
    (mi : MemInst) : Prop where
  funcs : exLogI.store.funcs = [fi₀, fi₁]
  code₀ : fi₀.code = .host 0
  ty₀ : FnType.ofDefType? fi₀.type = some ⟨[], []⟩
  code₁ : fi₁.code = .wasm ⟨t, [], [.call x, .intConst .i32 0,
    .intLoad .i32 (some (.i8, .unsigned)) y memarg0]⟩
  ty₁ : FnType.ofDefType? fi₁.type = some ⟨[], [.num (.int .i32)]⟩
  hx : x.toNat = 0
  hy : y.toNat = 0
  mod₁ : fi₁.module.funcs = [0, 1]
  mems₁ : fi₁.module.mems = [0]
  mem : exLogI.store.mems[0]? = some mi
  size : 1 ≤ mi.bytes.size

/-- The store has this shape. -/
theorem shape : ∃ fi₀ fi₁ t x y mi, Shape fi₀ fi₁ t x y mi := by
  obtain ⟨fi₀, fi₁, hf⟩ := exFuncs
  have hhost := t_host
  have hbody := t_body
  have hty := t_ty
  have hmod := t_mod
  have hmems := t_mems
  rw [hf] at hhost hbody hty hmod hmems
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hhost hbody hty hmod hmems
  obtain ⟨t, x, y, hc₁, hx, hy⟩ := isGetBody_code hbody.2.1
  obtain ⟨mi, hmi, hmt⟩ := List.map_eq_singleton_iff.mp t_memty
  have hok : MemInstOk mi :=
    exLogI_wellFormed.storeOk.mems mi (by show mi ∈ exLogPrep.1.store.mems; simp [hmi])
  have hsz : 1 ≤ mi.bytes.size := by
    rw [hok.2, hmt]
    decide
  exact ⟨fi₀, fi₁, t, x, y, mi, ⟨hf, isHost0_code hhost.1, hty.1, hc₁, hty.2.1, hx, hy,
    hmod.2.1, hmems.2.1, by show exLogPrep.1.store.mems[0]? = _; simp [hmi], hsz⟩⟩


section Run

variable {P : Silmaril.Wasm.Numerics.Profile} {fi₀ fi₁ : FuncInst Nat} {t : TypeIdx}
  {x : FuncIdx} {y : MemIdx} {mi : MemInst}

/-- The value `i32 42`. -/
abbrev v42 : Val := .num ⟨.int .i32, 42⟩

/-- The body of `get`, as administrative code. -/
abbrev getCode (x : FuncIdx) (y : MemIdx) : List Admin :=
  [.plain (.call x), .plain (.intConst .i32 0),
    .plain (.intLoad .i32 (some (.i8, .unsigned)) y memarg0)]

/-- Entering `get`. -/
theorem run_enter (h : Shape fi₀ fi₁ t x y mi) :
    Step P logHost (invoke exLogI.store 1 [])
      ⟨exLogI.store, {}, [.frame 1 (Frame.forCall fi₁.module [] []) [.label 1 [] (getCode x y)]]⟩ := by
  have hf : exLogI.store.funcs[1]? = some fi₁ := by rw [h.funcs]; rfl
  have he : Expand fi₁.type (.func (Ty.ofList []) (Ty.ofList [.num (.int .i32)])) :=
    FnType.expand_of_ofDefType? h.ty₁
  have hs := Step.callRefFunc (P := P) (host := logHost) (s := exLogI.store) (f := {})
    (c := .callRefType ((exLogI.store.funcs[1]?.map FuncInst.type).getD default)) (vs := [])
    trivial hf he rfl h.code₁
  exact hs

/-- `call 0` reaches the host call. -/
theorem run_call (h : Shape fi₀ fi₁ t x y mi) :
    Step P logHost ⟨exLogI.store, Frame.forCall fi₁.module [] [], getCode x y⟩
      ⟨exLogI.store, Frame.forCall fi₁.module [] [], [.ref (.func 0), .callRefType fi₀.type,
        .plain (.intConst .i32 0), .plain (.intLoad .i32 (some (.i8, .unsigned)) y memarg0)]⟩ := by
  have hf0 : exLogI.store.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  have hx : (Frame.forCall fi₁.module [] []).module.funcs[x.toNat]? = some 0 := by
    simp [Frame.forCall, h.mod₁, h.hx]
  exact step_head (Step.call hx hf0) (by simp)

/-- **The host call continues in the written store.** -/
theorem run_host (h : Shape fi₀ fi₁ t x y mi) :
    Step P logHost ⟨exLogI.store, Frame.forCall fi₁.module [] [], [.ref (.func 0),
        .callRefType fi₀.type, .plain (.intConst .i32 0),
        .plain (.intLoad .i32 (some (.i8, .unsigned)) y memarg0)]⟩
      ⟨poke exLogI.store, Frame.forCall fi₁.module [] [], [.plain (.intConst .i32 0),
        .plain (.intLoad .i32 (some (.i8, .unsigned)) y memarg0)]⟩ := by
  have hf0 : exLogI.store.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  have hh : logHost 0 exLogI.store [] (.returned (poke exLogI.store) (.values [])) :=
    .inl ⟨rfl, rfl, exLogI_wellFormed.host_type, rfl⟩
  have he : Expand fi₀.type (.func (Ty.ofList []) (Ty.ofList [])) :=
    FnType.expand_of_ofDefType? h.ty₀
  have hs := Step.callRefHost (P := P) (host := logHost) (s := exLogI.store)
    (f := Frame.forCall fi₁.module [] []) (c := .callRefType fi₀.type) (vs := []) trivial hf0 he
    rfl h.code₀ hh
  have hs' : Step P logHost ⟨exLogI.store, Frame.forCall fi₁.module [] [],
      [.ref (.func 0), .callRefType fi₀.type]⟩ ⟨poke exLogI.store, Frame.forCall fi₁.module [] [], []⟩ := by
    simpa [vals, Result.toAdmin] using hs
  exact step_head hs' (by simp)

/-- **`i32.load8_u` reads the byte the host wrote.** -/
theorem run_load (h : Shape fi₀ fi₁ t x y mi) :
    Step P logHost ⟨poke exLogI.store, Frame.forCall fi₁.module [] [], [.plain (.intConst .i32 0),
        .plain (.intLoad .i32 (some (.i8, .unsigned)) y memarg0)]⟩
      ⟨poke exLogI.store, Frame.forCall fi₁.module [] [], vals [v42]⟩ := by
  have hm : (poke exLogI.store).mem? (Frame.forCall fi₁.module [] []) y = some (0, pokeMem mi) := by
    simp [Store.mem?, Frame.forCall, h.mems₁, h.hy, poke_mem h.mem]
  have hl : Silmaril.Wasm.Execution.Memory.load (pokeMem mi).bytes
      (effAddr (0 : BitVec 32).toNat memarg0) (PackSize.i8.width / 8) = some 42 :=
    pokeMem_load h.size
  exact Step.memory (MemoryStep.loadPackVal (t := .i32) (a := .i32) (i := 0) (sx := .unsigned) hm hl)

/-- **The run of `get`**, every profile: the value `i32 42` in the written store. -/
theorem run_get (h : Shape fi₀ fi₁ t x y mi) :
    Steps P logHost (invoke exLogI.store 1 []) ⟨poke exLogI.store, {}, vals [v42]⟩ := by
  have h₁ := run_enter (P := P) h
  have h₂ := Step.ctxtFrame (f := {}) (n := 1) (Step.ctxtLabel (n := 1) (cont := []) (run_call (P := P) h))
  have h₃ := Step.ctxtFrame (f := {}) (n := 1) (Step.ctxtLabel (n := 1) (cont := []) (run_host (P := P) h))
  have h₄ := Step.ctxtFrame (f := {}) (n := 1) (Step.ctxtLabel (n := 1) (cont := []) (run_load (P := P) h))
  have h₅ : Step P logHost ⟨poke exLogI.store, {}, [.frame 1 (Frame.forCall fi₁.module [] [])
      [.label 1 [] (vals [v42])]]⟩ ⟨poke exLogI.store, {}, [.frame 1 (Frame.forCall fi₁.module [] [])
      (vals [v42])]⟩ := Step.ctxtFrame Step.labelVals
  have h₆ : Step P logHost ⟨poke exLogI.store, {}, [.frame 1 (Frame.forCall fi₁.module [] [])
      (vals [v42])]⟩ ⟨poke exLogI.store, {}, vals [v42]⟩ := Step.frameVals rfl
  exact h₁.steps.trans (h₂.steps.trans (h₃.steps.trans (h₄.steps.trans (h₅.steps.trans h₆.steps))))

end Run

end Silmaril.Proofs.Wasm.Game.SharedExample
