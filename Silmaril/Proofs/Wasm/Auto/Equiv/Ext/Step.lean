module

public import Silmaril.Proofs.Wasm.Auto.Equiv.Ext.Store
public import Silmaril.Proofs.Wasm.Auto.Equiv.Ctl.Loop
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Memory.Thms

/-!
# One step of the extended executor

`wp_xstep`: for one symbolic step `xstep mem S i = some S'`, the every-run weakest
precondition (both readings, every profile and host relation) of the concrete configuration of
`S` followed by `i` is that of `S'`, or, when the step added a guard that fails, the trap
postcondition at the state of `S`. Each case gives the concrete head step of the instruction
(silmaril-lean's `Det.Head`) and uses `wp_det_iff`: a deterministic head step does not change
the weakest precondition (forward by `Wp.det`, backward by the step).

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Deterministic head steps -/

theorem wp_det_iff {m : Corr} {s : Store H} {f : Frame} {us args : List Val} {i : Instr}
    {rest : List Admin} {Q : Post H} {c₁ : Config H}
    (hfam : famOf (.plain i) ≠ .control) (hpf : ProfileFree i) (h₁ : Head P s f args (.plain i) c₁) :
    Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q ↔
      Wp m P host c₁.store c₁.frame (vals us ++ c₁.code ++ rest) Q := by
  constructor
  · intro h
    have h₂ : Step P host ⟨s, f, vals args ++ [.plain i]⟩ c₁ := Step.of_noHost host h₁.toStep
    have hst : Step P host ⟨s, f, vals (us ++ args) ++ .plain i :: rest⟩
        ⟨c₁.store, c₁.frame, vals us ++ c₁.code ++ rest⟩ := by
      simpa using Sim.Step.append_right (Sim.Step.vals_left h₂ us) rest
    exact Silmaril.Proofs.Wasm.Auto.Equiv.wp_step_inv h hst
  · exact Wp.det hfam hpf h₁

theorem wp_detVals_iff {m : Corr} {s s' : Store H} {f f' : Frame} {us args res : List Val}
    {i : Instr} {rest : List Admin} {Q : Post H}
    (hfam : famOf (.plain i) ≠ .control) (hpf : ProfileFree i)
    (h₁ : Head P s f args (.plain i) ⟨s', f', vals res⟩) :
    Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q ↔
      Wp m P host s' f' (vals (us ++ res) ++ rest) Q := by
  rw [wp_det_iff hfam hpf h₁]
  simp

theorem wp_trap_iff {m : Corr} {s : Store H} {f : Frame} {us : List Val} {rest : List Admin}
    {Q : Post H} : Wp m P host s f (vals us ++ [.trap] ++ rest) Q ↔ Q s f .trap := by
  constructor
  · intro h
    exact Silmaril.Proofs.Wasm.Auto.Equiv.wp_exit_post h ⟨us, rest, by simp⟩
  · intro hq
    simpa using Wp.trap (m := m) (P := P) (host := host) (us := us) (rest := rest) hq

theorem wp_detTrap_iff {m : Corr} {s : Store H} {f : Frame} {us args : List Val}
    {i : Instr} {rest : List Admin} {Q : Post H}
    (hfam : famOf (.plain i) ≠ .control) (hpf : ProfileFree i)
    (h₁ : Head P s f args (.plain i) ⟨s, f, [.trap]⟩) :
    Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q ↔ Q s f .trap := by
  rw [wp_det_iff hfam hpf h₁]
  exact wp_trap_iff

/-! ## The outcome of a symbolic step -/

theorem xstepOut_noGuard {m : Corr} {c : XCtx H} {mem : Bool} {S S' : XState} {us : List Val}
    {rest : List Admin} {Q : Post H} (hg : S'.guards = S.guards) :
    XStepOut m P host c mem S S' us rest Q ↔
      Wp m P host (c.storeOf mem S') (c.frameOf S') (vals (us ++ (c.stackOf S').reverse) ++ rest) Q := by
  simp [XStepOut, hg]

theorem xstepOut_guard {m : Corr} {c : XCtx H} {mem : Bool} {S S' : XState} {us : List Val}
    {rest : List Admin} {Q : Post H} {g : Guard} (hg : S'.guards = S.guards ++ [(g, { S with guards := [] })]) :
    XStepOut m P host c mem S S' us rest Q ↔
      (if g.holds c.ρ c.mi.bytes = true then
        Wp m P host (c.storeOf mem S') (c.frameOf S') (vals (us ++ (c.stackOf S').reverse) ++ rest) Q
      else Q (c.storeOf mem S) (c.frameOf S) .trap) := by
  simp [XStepOut, hg]

/-! ## Stacks -/

theorem stackOf_cons (c : XCtx H) (S : XState) (p : IntType × XT) (st : List (IntType × XT))
    (h : S.stack = p :: st) :
    (c.stackOf S).reverse = (st.map (denX c.ρ c.mi.bytes)).reverse ++ [denX c.ρ c.mi.bytes p] := by
  simp [XCtx.stackOf, h]

theorem denX_eq (ρ : Env) (B0 : ByteArray) (t : IntType) (e : XT) :
    denX ρ B0 (t, e) = .num ⟨.int t, evX ρ B0 t e⟩ := rfl

/-! ## The instructions, one by one -/

section Cases

variable {m : Corr} {mem : Bool} {c : XCtx H} {S : XState} {us : List Val} {rest : List Admin}
  {Q : Post H}


theorem case_nop :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain .nop :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c S us rest) Q := by
  have := wp_detVals_iff (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (c.stackOf S).reverse) (args := []) (res := []) (rest := rest) (Q := Q)
    (by simp [famOf]) (by trivial) (.parametric .nop)
  simpa [cfg] using this

theorem case_drop {p : IntType × XT} {st : List (IntType × XT)} (hs : S.stack = p :: st) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain .drop :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c { S with stack := st } us rest) Q := by
  rw [stackOf_cons c S p st hs, ← List.append_assoc]
  have := wp_detVals_iff (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse) (args := [denX c.ρ c.mi.bytes p]) (res := []) (rest := rest) (Q := Q)
    (by simp [famOf]) (by trivial) (.parametric (.drop _))
  simpa [cfg, XCtx.stackOf] using this

theorem case_const {t : IntType} {k : BitVec t.width} :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.intConst t k) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c { S with stack := (t, .const k.toNat) :: S.stack } us rest) Q := by
  have e : denX c.ρ c.mi.bytes (t, .const k.toNat) = .num ⟨.int t, k⟩ := by
    simp [denX, evX]
  simp [cfg, XCtx.stackOf, e, vals, Val.toAdmin]

theorem case_localGet {x : LocalIdx} {p : IntType × XT} (hp : S.locals[x.toNat]? = some p) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.localGet x) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c { S with stack := p :: S.stack } us rest) Q := by
  have hv : (c.frameOf S).local? x = some (some (denX c.ρ c.mi.bytes p)) := by rw [local?_frameOf, hp]; rfl
  have := wp_detVals_iff (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (c.stackOf S).reverse) (args := []) (res := [denX c.ρ c.mi.bytes p]) (rest := rest) (Q := Q)
    (by simp [famOf]) (by trivial) (.variable (.localGet hv))
  simpa [cfg, XCtx.stackOf] using this

theorem case_localSet {x : LocalIdx} {p : IntType × XT} {st : List (IntType × XT)}
    (hs : S.stack = p :: st) (hx : x.toNat < S.locals.length) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.localSet x) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf { S with locals := S.locals.set x.toNat p, stack := st })
        (cfg c { S with locals := S.locals.set x.toNat p, stack := st } us rest) Q := by
  rw [stackOf_cons c S p st hs, ← List.append_assoc]
  have hx' : x.toNat < (c.frameOf S).locals.length := by rw [locals_length_frameOf]; exact hx
  have := wp_detVals_iff (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse) (args := [denX c.ρ c.mi.bytes p]) (res := []) (rest := rest) (Q := Q)
    (by simp [famOf]) (by trivial) (.variable (.localSet hx'))
  rw [this, frameOf_setLocal]
  simp [cfg, XCtx.stackOf]

theorem case_localTee {x : LocalIdx} {p : IntType × XT} {st : List (IntType × XT)}
    (hs : S.stack = p :: st) (hx : x.toNat < S.locals.length) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.localTee x) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf { S with locals := S.locals.set x.toNat p, stack := p :: st })
        (cfg c { S with locals := S.locals.set x.toNat p, stack := p :: st } us rest) Q := by
  rw [stackOf_cons c S p st hs, ← List.append_assoc]
  have h₁ := wp_det_iff (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse) (args := [denX c.ρ c.mi.bytes p]) (rest := rest) (Q := Q)
    (by simp [famOf]) (by trivial) (.variable (.localTee (s := c.storeOf mem S) (f := c.frameOf S) (x := x) (v := (denX c.ρ c.mi.bytes) p)))
  rw [h₁]
  have hx' : x.toNat < (c.frameOf S).locals.length := by rw [locals_length_frameOf]; exact hx
  have h₂ := wp_detVals_iff (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse ++ [denX c.ρ c.mi.bytes p]) (args := [denX c.ρ c.mi.bytes p]) (res := []) (rest := rest) (Q := Q)
    (by simp [famOf]) (by trivial) (.variable (.localSet hx'))
  have e : vals (us ++ (st.map (denX c.ρ c.mi.bytes)).reverse) ++ [(denX c.ρ c.mi.bytes p).toAdmin, (denX c.ρ c.mi.bytes p).toAdmin, .plain (.localSet x)] ++ rest =
      vals (us ++ (st.map (denX c.ρ c.mi.bytes)).reverse ++ [denX c.ρ c.mi.bytes p] ++ [denX c.ρ c.mi.bytes p]) ++ .plain (.localSet x) :: rest := by
    simp [vals]
  simp only [e, h₂, frameOf_setLocal]
  simp [cfg, XCtx.stackOf]

theorem stackOf_cons2 (c : XCtx H) (S : XState) (p q : IntType × XT) (st : List (IntType × XT))
    (h : S.stack = q :: p :: st) :
    (c.stackOf S).reverse = (st.map (denX c.ρ c.mi.bytes)).reverse ++
      [denX c.ρ c.mi.bytes p, denX c.ρ c.mi.bytes q] := by
  simp [XCtx.stackOf, h]

theorem stackOf_cons3 (c : XCtx H) (S : XState) (p q r : IntType × XT) (st : List (IntType × XT))
    (h : S.stack = r :: q :: p :: st) :
    (c.stackOf S).reverse = (st.map (denX c.ρ c.mi.bytes)).reverse ++
      [denX c.ρ c.mi.bytes p, denX c.ρ c.mi.bytes q, denX c.ρ c.mi.bytes r] := by
  simp [XCtx.stackOf, h]

theorem case_globalGet (hc : c.Good mem) (hl : S.globs.length = c.ga.length) {x : GlobalIdx}
    {p : IntType × XT} (hp : S.globs[x.toNat]? = some p) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.globalGet x) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c { S with stack := p :: S.stack } us rest) Q := by
  have hx : x.toNat < c.ga.length := by
    have := (List.getElem?_eq_some_iff.mp hp).1; omega
  obtain ⟨g, hg, hv⟩ := global?_storeOf hc S hl x hx
  have hp' : S.globs[x.toNat] = p := (List.getElem?_eq_some_iff.mp hp).2
  have := wp_detVals_iff (i := (.globalGet x)) (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (c.stackOf S).reverse) (args := []) (res := [g.value]) (rest := rest) (Q := Q)
    (by simp [famOf]) (by trivial) (.variable (.globalGet hg))
  rw [hv, hp'] at this
  simpa [cfg, XCtx.stackOf] using this

theorem case_globalSet (hc : c.Good mem) (hl : S.globs.length = c.ga.length) {x : GlobalIdx}
    {p : IntType × XT} {st : List (IntType × XT)} (hs : S.stack = p :: st)
    (hx : x.toNat < S.globs.length) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.globalSet x) :: rest) Q ↔
      Wp m P host (c.storeOf mem { S with globs := S.globs.set x.toNat p, stack := st }) (c.frameOf S)
        (cfg c { S with globs := S.globs.set x.toNat p, stack := st } us rest) Q := by
  have hx' : x.toNat < c.ga.length := by omega
  obtain ⟨g, hg, -⟩ := global?_storeOf hc S hl x hx'
  rw [stackOf_cons c S p st hs, ← List.append_assoc]
  have := wp_detVals_iff (i := (.globalSet x)) (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse) (args := [denX c.ρ c.mi.bytes p]) (res := [])
    (rest := rest) (Q := Q) (by simp [famOf]) (by trivial) (.variable (.globalSet hg))
  rw [this, setGlobal_storeOf hc S hl x hx' p st]
  simp [cfg, XCtx.stackOf]

theorem case_unOp {t : IntType} {op : IntUnOp} {a : XT} {st : List (IntType × XT)}
    (hs : S.stack = (t, a) :: st) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.intUnOp t op) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c { S with stack := (t, .un op a) :: st } us rest) Q := by
  rw [stackOf_cons c S _ st hs, ← List.append_assoc]
  have := wp_detVals_iff (i := (.intUnOp t op)) (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse) (args := [denX c.ρ c.mi.bytes (t, a)])
    (res := [.num ⟨.int t, intUnOp t op (evX c.ρ c.mi.bytes t a)⟩])
    (rest := rest) (Q := Q) (by simp [famOf]) (by trivial)
    (.numeric (.intUnOp (op := op) (x := evX c.ρ c.mi.bytes t a)))
  simpa [cfg, XCtx.stackOf, denX, evX] using this

theorem case_binOk {t : IntType} {op : IntBinOp} {a b : XT} {st : List (IntType × XT)}
    {z : BitVec t.width} (hs : S.stack = (t, b) :: (t, a) :: st)
    (hz : intBinOp t op (evX c.ρ c.mi.bytes t a) (evX c.ρ c.mi.bytes t b) = .ok z) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.intBinOp t op) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c { S with stack := (t, .bin op a b) :: st } us rest) Q := by
  rw [stackOf_cons2 c S _ _ st hs, ← List.append_assoc]
  have := wp_detVals_iff (i := (.intBinOp t op)) (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
    (args := [denX c.ρ c.mi.bytes (t, a), denX c.ρ c.mi.bytes (t, b)]) (res := [.num ⟨.int t, z⟩])
    (rest := rest) (Q := Q) (by simp [famOf]) (by trivial) (.numeric (.intBinOp hz))
  have hb : binV t op (evX c.ρ c.mi.bytes t a) (evX c.ρ c.mi.bytes t b) = z := by simp [binV, hz]
  simpa [cfg, XCtx.stackOf, denX, evX, hb] using this

theorem case_binTrap {t : IntType} {op : IntBinOp} {a b : XT} {st : List (IntType × XT)}
    {e : IntTrap} (hs : S.stack = (t, b) :: (t, a) :: st)
    (he : intBinOp t op (evX c.ρ c.mi.bytes t a) (evX c.ρ c.mi.bytes t b) = .error e) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.intBinOp t op) :: rest) Q ↔
      Q (c.storeOf mem S) (c.frameOf S) .trap := by
  rw [stackOf_cons2 c S _ _ st hs, ← List.append_assoc]
  exact wp_detTrap_iff (i := (.intBinOp t op)) (by simp [famOf]) (by trivial) (.numeric (.intBinOpTrap he))

theorem case_testOp {t : IntType} {op : IntTestOp} {a : XT} {st : List (IntType × XT)}
    (hs : S.stack = (t, a) :: st) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.intTestOp t op) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S)
        (cfg c { S with stack := (.i32, .rel t .eq a (.const 0)) :: st } us rest) Q := by
  rw [stackOf_cons c S _ st hs, ← List.append_assoc]
  have := wp_detVals_iff (i := (.intTestOp t op)) (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse) (args := [denX c.ρ c.mi.bytes (t, a)])
    (res := [Val.i32 (intTestOp t op (evX c.ρ c.mi.bytes t a))])
    (rest := rest) (Q := Q) (by simp [famOf]) (by trivial)
    (.numeric (.intTestOp (op := op) (x := evX c.ρ c.mi.bytes t a)))
  have e : Val.i32 (intTestOp t op (evX c.ρ c.mi.bytes t a)) =
      denX c.ρ c.mi.bytes (.i32, .rel t .eq a (.const 0)) := by
    cases op
    simp only [denX, evX, Val.i32, intTestOp, intRelOp]
    rfl
  rw [e] at this
  simpa [cfg, XCtx.stackOf] using this

theorem case_relOp {t : IntType} {op : IntRelOp} {a b : XT} {st : List (IntType × XT)}
    (hs : S.stack = (t, b) :: (t, a) :: st) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.intRelOp t op) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c { S with stack := (.i32, .rel t op a b) :: st } us rest) Q := by
  rw [stackOf_cons2 c S _ _ st hs, ← List.append_assoc]
  have := wp_detVals_iff (i := (.intRelOp t op)) (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
    (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
    (args := [denX c.ρ c.mi.bytes (t, a), denX c.ρ c.mi.bytes (t, b)])
    (res := [Val.i32 (intRelOp t op (evX c.ρ c.mi.bytes t a) (evX c.ρ c.mi.bytes t b))])
    (rest := rest) (Q := Q) (by simp [famOf]) (by trivial)
    (.numeric (.intRelOp (op := op) (x := evX c.ρ c.mi.bytes t a) (y := evX c.ρ c.mi.bytes t b)))
  have e : Val.i32 (intRelOp t op (evX c.ρ c.mi.bytes t a) (evX c.ρ c.mi.bytes t b)) =
      denX c.ρ c.mi.bytes (.i32, .rel t op a b) := by
    simp only [denX, evX, Val.i32]
    rfl
  rw [e] at this
  simpa [cfg, XCtx.stackOf] using this

theorem case_select {t : IntType} {ts : Option (List ValType)} {cnd a b : XT}
    {st : List (IntType × XT)} (hs : S.stack = (.i32, cnd) :: (t, b) :: (t, a) :: st) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.select ts) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c { S with stack := (t, .sel cnd a b) :: st } us rest) Q := by
  rw [stackOf_cons3 c S _ _ _ st hs, ← List.append_assoc]
  by_cases h0 : evX c.ρ c.mi.bytes .i32 cnd = 0
  · have hd : denX c.ρ c.mi.bytes (.i32, cnd) = Val.i32 0 := by
      simp only [denX, Val.i32]
      rw [h0]
      rfl
    rw [hd]
    have := wp_detVals_iff (i := (.select ts)) (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
      (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
      (args := [denX c.ρ c.mi.bytes (t, a), denX c.ρ c.mi.bytes (t, b), Val.i32 0])
      (res := [denX c.ρ c.mi.bytes (t, b)])
      (rest := rest) (Q := Q) (by simp [famOf]) (by trivial)
      (.parametric (.selectFalse (denX c.ρ c.mi.bytes (t, a)) (denX c.ρ c.mi.bytes (t, b)) ts))
    have hv : denX c.ρ c.mi.bytes (t, .sel cnd a b) = denX c.ρ c.mi.bytes (t, b) := by
      simp only [denX, evX]
      rw [ite_eq_right (not_not.mpr h0)]
    rw [this]
    simp [cfg, XCtx.stackOf, hv]
  · have hd : denX c.ρ c.mi.bytes (.i32, cnd) = Val.i32 (evX c.ρ c.mi.bytes .i32 cnd) := rfl
    rw [hd]
    have := wp_detVals_iff (i := (.select ts)) (m := m) (P := P) (host := host) (s := c.storeOf mem S) (f := c.frameOf S)
      (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
      (args := [denX c.ρ c.mi.bytes (t, a), denX c.ρ c.mi.bytes (t, b),
        Val.i32 (evX c.ρ c.mi.bytes .i32 cnd)]) (res := [denX c.ρ c.mi.bytes (t, a)])
      (rest := rest) (Q := Q) (by simp [famOf]) (by trivial)
      (.parametric (.selectTrue (v₁ := denX c.ρ c.mi.bytes (t, a)) (v₂ := denX c.ρ c.mi.bytes (t, b))
        (ts := ts) h0))
    have hv : denX c.ρ c.mi.bytes (t, .sel cnd a b) = denX c.ρ c.mi.bytes (t, a) := by
      simp only [denX, evX]
      rw [ite_eq_left h0]
    rw [this]
    simp [cfg, XCtx.stackOf, hv]

theorem convertP_ok {op : ConvertOp} (hop : op = .wrap ∨ ∃ sx, op = .extend sx)
    {x : BitVec op.source.width} {r : Except FloatTrap (NumValue op.target)} :
    convertP P op x r ↔ r = Numerics.convert op x := by
  rcases hop with rfl | ⟨sx, rfl⟩ <;> unfold convertP <;> split <;> simp [convertRel]

/-- A head step forward, without determinism. -/
theorem wp_head_step {s : Store H} {f : Frame} {us args : List Val} {i : Instr}
    {rest : List Admin} {Q : Post H} {c₁ : Config H} (h₁ : Head P s f args (.plain i) c₁)
    (h : Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q) :
    Wp m P host c₁.store c₁.frame (vals us ++ c₁.code ++ rest) Q := by
  have h₂ : Step P host ⟨s, f, vals args ++ [.plain i]⟩ c₁ := Step.of_noHost host h₁.toStep
  have hst : Step P host ⟨s, f, vals (us ++ args) ++ .plain i :: rest⟩
      ⟨c₁.store, c₁.frame, vals us ++ c₁.code ++ rest⟩ := by
    simpa using Sim.Step.append_right (Sim.Step.vals_left h₂ us) rest
  exact Silmaril.Proofs.Wasm.Auto.Equiv.wp_step_inv h hst

theorem wp_convert_iff {op : ConvertOp} (hop : op = .wrap ∨ ∃ sx, op = .extend sx)
    {s : Store H} {f : Frame} {us : List Val} {rest : List Admin} {Q : Post H}
    {x : BitVec op.source.width} {z : BitVec op.target.width} (hz : Numerics.convert op x = .ok z) :
    Wp m P host s f (vals (us ++ [.num ⟨op.source, x⟩]) ++ .plain (.convert op) :: rest) Q ↔
      Wp m P host s f (vals (us ++ [.num ⟨op.target, z⟩]) ++ rest) Q := by
  constructor
  · intro h
    have hc : convertP P op x (.ok z) := (convertP_ok hop).mpr hz.symm
    have := wp_head_step (m := m) (us := us) (rest := rest) (Q := Q) (.numeric (.convert hc)) h
    simpa using this
  · intro h
    refine Wp.convert (fun z' hz' => ?_) (fun e he => ?_)
    · have : (Except.ok z' : Except FloatTrap _) = .ok z := ((convertP_ok hop).mp hz').trans hz
      cases this
      exact h
    · have : (Except.error e : Except FloatTrap (NumValue op.target)) = .ok z :=
        ((convertP_ok hop).mp he).trans hz
      cases this

theorem case_wrap {a : XT} {st : List (IntType × XT)} (hs : S.stack = (.i64, a) :: st) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.convert .wrap) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c { S with stack := (.i32, .wrap a) :: st } us rest) Q := by
  rw [stackOf_cons c S _ st hs, ← List.append_assoc]
  have := wp_convert_iff (m := m) (P := P) (host := host) (op := .wrap) (Or.inl rfl)
    (s := c.storeOf mem S) (f := c.frameOf S) (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
    (rest := rest) (Q := Q) (x := evX c.ρ c.mi.bytes .i64 a)
    (z := (evX c.ρ c.mi.bytes .i64 a).setWidth 32) rfl
  rw [show cfg c { S with stack := (.i32, .wrap a) :: st } us rest =
    vals (us ++ (st.map (denX c.ρ c.mi.bytes)).reverse ++ [denX c.ρ c.mi.bytes (.i32, .wrap a)]) ++ rest by
      simp [cfg, XCtx.stackOf]]
  exact this

theorem case_extend {sx : Signedness} {a : XT} {st : List (IntType × XT)} (hs : S.stack = (.i32, a) :: st) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.convert (.extend sx)) :: rest) Q ↔
      Wp m P host (c.storeOf mem S) (c.frameOf S) (cfg c { S with stack := (.i64, .ext sx a) :: st } us rest) Q := by
  rw [stackOf_cons c S _ st hs, ← List.append_assoc]
  cases sx
  · have := wp_convert_iff (m := m) (P := P) (host := host) (op := .extend .signed) (Or.inr ⟨_, rfl⟩)
      (s := c.storeOf mem S) (f := c.frameOf S) (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
      (rest := rest) (Q := Q) (x := evX c.ρ c.mi.bytes .i32 a)
      (z := (evX c.ρ c.mi.bytes .i32 a).signExtend 64) rfl
    rw [show cfg c { S with stack := (.i64, .ext .signed a) :: st } us rest =
      vals (us ++ (st.map (denX c.ρ c.mi.bytes)).reverse ++ [denX c.ρ c.mi.bytes (.i64, .ext .signed a)]) ++ rest by
        simp [cfg, XCtx.stackOf]]
    exact this
  · have := wp_convert_iff (m := m) (P := P) (host := host) (op := .extend .unsigned) (Or.inr ⟨_, rfl⟩)
      (s := c.storeOf mem S) (f := c.frameOf S) (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
      (rest := rest) (Q := Q) (x := evX c.ρ c.mi.bytes .i32 a)
      (z := (evX c.ρ c.mi.bytes .i32 a).setWidth 64) rfl
    rw [show cfg c { S with stack := (.i64, .ext .unsigned a) :: st } us rest =
      vals (us ++ (st.map (denX c.ρ c.mi.bytes)).reverse ++ [denX c.ρ c.mi.bytes (.i64, .ext .unsigned a)]) ++ rest by
        simp [cfg, XCtx.stackOf]]
    exact this

theorem holds_inb (a : XT) (arg : MemArg) (n : Nat) :
    (Guard.inb a arg n).holds c.ρ c.mi.bytes = true ↔
      effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + n ≤ c.mi.bytes.size := by
  simp [Guard.holds]

theorem case_load (hc : c.Good true) {t : IntType} {p : Option (PackSize × Signedness)}
    {x : MemIdx} {arg : MemArg} {a : XT} {st : List (IntType × XT)} (hx : x.toNat = 0)
    (hs : S.stack = (.i32, a) :: st)
    (hb : effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + accBytes t (p.map Prod.fst) ≤ c.mi.bytes.size) :
    Wp m P host (c.storeOf true S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.intLoad t p x arg) :: rest) Q ↔
      Wp m P host (c.storeOf true S) (c.frameOf S) (cfg c { S with stack := (t, .load S.mem t p a arg) :: st } us rest) Q := by
  rw [stackOf_cons c S _ st hs, ← List.append_assoc]
  have hm := mem?_storeOf hc S hx
  have hsz := size_evM c.ρ c.mi.bytes S.mem
  rw [show cfg c { S with stack := (t, .load S.mem t p a arg) :: st } us rest =
    vals (us ++ (st.map (denX c.ρ c.mi.bytes)).reverse ++ [denX c.ρ c.mi.bytes (t, .load S.mem t p a arg)]) ++ rest by
      simp [cfg, XCtx.stackOf]]
  rcases p with _ | ⟨sz, sx⟩
  · have hb' : effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + t.width / 8 ≤ (evM c.ρ c.mi.bytes S.mem).size := by
      rw [hsz]; exact hb
    obtain ⟨cv, hl⟩ : ∃ cv, Memory.load (evM c.ρ c.mi.bytes S.mem) (effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg)
        (t.width / 8) = some cv := ⟨_, Silmaril.Wasm.Logic.Core.load_eq hb'⟩
    have := wp_detVals_iff (i := .intLoad t none x arg) (m := m) (P := P) (host := host)
      (s := c.storeOf true S) (f := c.frameOf S) (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
      (args := [denX c.ρ c.mi.bytes (.i32, a)]) (res := [.num ⟨.int t, cv.setWidth t.width⟩]) (rest := rest)
      (Q := Q) (by simp [famOf]) (by trivial)
      (.memory (.loadIntVal (a := .i32) (i := evX c.ρ c.mi.bytes .i32 a) hm hl))
    have hv : denX c.ρ c.mi.bytes (t, .load S.mem t none a arg) = .num ⟨.int t, cv.setWidth t.width⟩ := by
      simp only [denX, evX, loadV]
      split
      · rename_i cv' hcv'
        have e : cv' = cv := Option.some.inj (hcv'.symm.trans hl)
        subst e
        simp
      · rename_i hn
        cases hn.symm.trans hl
    rw [hv]
    exact this
  · have hb' : effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + sz.width / 8 ≤ (evM c.ρ c.mi.bytes S.mem).size := by
      rw [hsz]; exact hb
    obtain ⟨cv, hl⟩ : ∃ cv, Memory.load (evM c.ρ c.mi.bytes S.mem) (effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg)
        (sz.width / 8) = some cv := ⟨_, Silmaril.Wasm.Logic.Core.load_eq hb'⟩
    cases sx
    · have hv : denX c.ρ c.mi.bytes (t, .load S.mem t (some (sz, .signed)) a arg) =
          .num ⟨.int t, cv.signExtend t.width⟩ := by
        simp only [denX, evX, loadV]
        split
        · rename_i cv' hcv'
          have e : cv' = cv := Option.some.inj (hcv'.symm.trans hl)
          subst e
          simp
        · rename_i hn
          cases hn.symm.trans hl
      have := wp_detVals_iff (i := .intLoad t (some (sz, .signed)) x arg) (m := m) (P := P) (host := host)
        (s := c.storeOf true S) (f := c.frameOf S) (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
        (args := [denX c.ρ c.mi.bytes (.i32, a)])
        (res := [.num ⟨.int t, cv.signExtend t.width⟩]) (rest := rest)
        (Q := Q) (by simp [famOf]) (by trivial)
        (.memory (.loadPackVal (a := .i32) (i := evX c.ρ c.mi.bytes .i32 a) (sx := .signed) hm hl))
      rw [hv]
      exact this
    · have hv : denX c.ρ c.mi.bytes (t, .load S.mem t (some (sz, .unsigned)) a arg) =
          .num ⟨.int t, cv.setWidth t.width⟩ := by
        simp only [denX, evX, loadV]
        split
        · rename_i cv' hcv'
          have e : cv' = cv := Option.some.inj (hcv'.symm.trans hl)
          subst e
          simp
        · rename_i hn
          cases hn.symm.trans hl
      have := wp_detVals_iff (i := .intLoad t (some (sz, .unsigned)) x arg) (m := m) (P := P) (host := host)
        (s := c.storeOf true S) (f := c.frameOf S) (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
        (args := [denX c.ρ c.mi.bytes (.i32, a)])
        (res := [.num ⟨.int t, cv.setWidth t.width⟩]) (rest := rest)
        (Q := Q) (by simp [famOf]) (by trivial)
        (.memory (.loadPackVal (a := .i32) (i := evX c.ρ c.mi.bytes .i32 a) (sx := .unsigned) hm hl))
      rw [hv]
      exact this

theorem case_load_oob (hc : c.Good true) {t : IntType} {p : Option (PackSize × Signedness)}
    {x : MemIdx} {arg : MemArg} {a : XT} {st : List (IntType × XT)} (hx : x.toNat = 0)
    (hs : S.stack = (.i32, a) :: st)
    (hb : ¬ effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + accBytes t (p.map Prod.fst) ≤ c.mi.bytes.size) :
    Wp m P host (c.storeOf true S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.intLoad t p x arg) :: rest) Q ↔
      Q (c.storeOf true S) (c.frameOf S) .trap := by
  rw [stackOf_cons c S _ st hs, ← List.append_assoc]
  have hm := mem?_storeOf hc S hx
  have hsz := size_evM c.ρ c.mi.bytes S.mem
  rcases p with _ | ⟨sz, sx⟩
  · have hb' : (evM c.ρ c.mi.bytes S.mem).size < effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + t.width / 8 := by
      rw [hsz]; simp [accBytes] at hb; omega
    exact wp_detTrap_iff (i := .intLoad t none x arg) (args := [denX c.ρ c.mi.bytes (.i32, a)])
      (by simp [famOf]) (by trivial)
      (.memory (.loadIntOob (a := .i32) (i := evX c.ρ c.mi.bytes .i32 a) hm hb'))
  · have hb' : (evM c.ρ c.mi.bytes S.mem).size < effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + sz.width / 8 := by
      rw [hsz]; simp [accBytes] at hb; omega
    exact wp_detTrap_iff (i := .intLoad t (some (sz, sx)) x arg) (args := [denX c.ρ c.mi.bytes (.i32, a)])
      (by simp [famOf]) (by trivial)
      (.memory (.loadPackOob (t := t) (sx := sx) (a := .i32) (i := evX c.ρ c.mi.bytes .i32 a) hm hb'))

theorem case_store (hc : c.Good true) {t : IntType} {p : Option PackSize}
    {x : MemIdx} {arg : MemArg} {a v : XT} {st : List (IntType × XT)} (hx : x.toNat = 0)
    (hs : S.stack = (t, v) :: (.i32, a) :: st)
    (hb : effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + accBytes t p ≤ c.mi.bytes.size) :
    Wp m P host (c.storeOf true S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.intStore t p x arg) :: rest) Q ↔
      Wp m P host (c.storeOf true { S with mem := .mstore S.mem t p a arg v, stack := st }) (c.frameOf S)
        (cfg c { S with mem := .mstore S.mem t p a arg v, stack := st } us rest) Q := by
  rw [stackOf_cons2 c S _ _ st hs, ← List.append_assoc]
  have hm := mem?_storeOf hc S hx
  have hsz := size_evM c.ρ c.mi.bytes S.mem
  rw [show cfg c { S with mem := .mstore S.mem t p a arg v, stack := st } us rest =
    vals (us ++ (st.map (denX c.ρ c.mi.bytes)).reverse) ++ rest by simp [cfg, XCtx.stackOf]]
  rcases p with _ | sz
  · have hb' : effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + t.width / 8 ≤ (evM c.ρ c.mi.bytes S.mem).size := by
      rw [hsz]; exact hb
    obtain ⟨B', hB⟩ : ∃ B', Memory.store (evM c.ρ c.mi.bytes S.mem) (effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg)
        (count := t.width / 8) ((evX c.ρ c.mi.bytes t v).setWidth _) = some B' :=
      ⟨_, Silmaril.Wasm.Logic.Core.store_eq _ hb'⟩
    have := wp_detVals_iff (i := .intStore t none x arg) (m := m) (P := P) (host := host)
      (s := c.storeOf true S) (f := c.frameOf S) (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
      (args := [denX c.ρ c.mi.bytes (.i32, a), denX c.ρ c.mi.bytes (t, v)]) (res := []) (rest := rest)
      (Q := Q) (by simp [famOf]) (by trivial)
      (.memory (.storeIntVal (a := .i32) (i := evX c.ρ c.mi.bytes .i32 a) (c := evX c.ρ c.mi.bytes t v) hm hB))
    have hst := setMem_storeOf c S (.mstore S.mem t none a arg v) B' (by
      simp only [evM, storeM]
      exact congrArg (·.getD (evM c.ρ c.mi.bytes S.mem)) hB) st S.guards
    rw [this, hst]
    simp
  · have hb' : effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + sz.width / 8 ≤ (evM c.ρ c.mi.bytes S.mem).size := by
      rw [hsz]; exact hb
    obtain ⟨B', hB⟩ : ∃ B', Memory.store (evM c.ρ c.mi.bytes S.mem) (effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg)
        (count := sz.width / 8) ((evX c.ρ c.mi.bytes t v).setWidth _) = some B' :=
      ⟨_, Silmaril.Wasm.Logic.Core.store_eq _ hb'⟩
    have := wp_detVals_iff (i := .intStore t (some sz) x arg) (m := m) (P := P) (host := host)
      (s := c.storeOf true S) (f := c.frameOf S) (us := us ++ (st.map (denX c.ρ c.mi.bytes)).reverse)
      (args := [denX c.ρ c.mi.bytes (.i32, a), denX c.ρ c.mi.bytes (t, v)]) (res := []) (rest := rest)
      (Q := Q) (by simp [famOf]) (by trivial)
      (.memory (.storePackVal (a := .i32) (i := evX c.ρ c.mi.bytes .i32 a) (c := evX c.ρ c.mi.bytes t v) hm hB))
    have hst := setMem_storeOf c S (.mstore S.mem t (some sz) a arg v) B' (by
      simp only [evM, storeM]
      exact congrArg (·.getD (evM c.ρ c.mi.bytes S.mem)) hB) st S.guards
    rw [this, hst]
    simp

theorem case_store_oob (hc : c.Good true) {t : IntType} {p : Option PackSize}
    {x : MemIdx} {arg : MemArg} {a v : XT} {st : List (IntType × XT)} (hx : x.toNat = 0)
    (hs : S.stack = (t, v) :: (.i32, a) :: st)
    (hb : ¬ effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + accBytes t p ≤ c.mi.bytes.size) :
    Wp m P host (c.storeOf true S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain (.intStore t p x arg) :: rest) Q ↔
      Q (c.storeOf true S) (c.frameOf S) .trap := by
  rw [stackOf_cons2 c S _ _ st hs, ← List.append_assoc]
  have hm := mem?_storeOf hc S hx
  have hsz := size_evM c.ρ c.mi.bytes S.mem
  rcases p with _ | sz
  · have hb' : (evM c.ρ c.mi.bytes S.mem).size < effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + t.width / 8 := by
      rw [hsz]; simp [accBytes] at hb; omega
    exact wp_detTrap_iff (i := .intStore t none x arg)
      (args := [denX c.ρ c.mi.bytes (.i32, a), denX c.ρ c.mi.bytes (t, v)])
      (by simp [famOf]) (by trivial)
      (.memory (.storeIntOob (a := .i32) (i := evX c.ρ c.mi.bytes .i32 a) (c := evX c.ρ c.mi.bytes t v) hm hb'))
  · have hb' : (evM c.ρ c.mi.bytes S.mem).size < effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + sz.width / 8 := by
      rw [hsz]; simp [accBytes] at hb; omega
    exact wp_detTrap_iff (i := .intStore t (some sz) x arg)
      (args := [denX c.ρ c.mi.bytes (.i32, a), denX c.ρ c.mi.bytes (t, v)])
      (by simp [famOf]) (by trivial)
      (.memory (.storePackOob (a := .i32) (i := evX c.ρ c.mi.bytes .i32 a) (c := evX c.ρ c.mi.bytes t v) hm hb'))

end Cases

/-! ## Safe binary operators -/

theorem intBinOp_ok_of_safe {ρ : Env} {B0 : ByteArray} {t : IntType} {op : IntBinOp} {b : XT}
    (hs : safeBinX t op b = true) (x : BitVec t.width) :
    ∃ z, intBinOp t op x (evX ρ B0 t b) = .ok z := by
  unfold safeBinX at hs
  split at hs
  · rename_i b' hb'
    have := Silmaril.Proofs.Wasm.Auto.Equiv.safeBin_ok (ρ := ρ) t op b' hs x
    rw [toTerm?_eq hb', evX_ofTerm]
    exact this
  · rcases op with _ | _ | _ | s | s | _ | _ | _ | _ | s | _ | _ <;> simp at hs <;>
      first | exact ⟨_, rfl⟩ | (cases s <;> exact ⟨_, rfl⟩)

/-! ## One symbolic step -/

theorem xstep_globs {mem : Bool} {S S' : XState} {i : Instr} (h : xstep mem S i = some S') :
    S'.globs.length = S.globs.length := by
  rcases S with ⟨ls, st, gs, mm, G⟩
  cases i <;> simp only [xstep] at h <;> (try cases h) <;> (try rfl) <;>
    (repeat' (first | split at h | (cases h; rfl) | (cases h; simp) | simp at h)) <;>
    (obtain ⟨_, -, rfl⟩ := ‹∃ _, _ ∧ _›; rfl)

theorem xstep_guards {mem : Bool} {S S' : XState} {i : Instr} (h : xstep mem S i = some S') :
    S'.guards = S.guards ∨ ∃ g, S'.guards = S.guards ++ [(g, { S with guards := [] })] := by
  rcases S with ⟨ls, st, gs, mm, G⟩
  cases i
  case localGet x =>
    simp only [xstep] at h
    obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Or.inl rfl
  case globalGet x =>
    simp only [xstep] at h
    obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Or.inl rfl
  case convert op =>
    rcases op with _ | sx | _ | _ | _ | _ | _ | _ | _ <;> simp only [xstep] at h
    all_goals (repeat' (first | split at h | (cases h; exact Or.inl rfl) | simp at h))
  all_goals simp only [xstep] at h
  all_goals
    (try cases h)
    (try exact Or.inl rfl)
    (repeat' (first | split at h | (cases h; exact Or.inl rfl) | (cases h; exact Or.inr ⟨_, rfl⟩) |
      simp at h))

end Silmaril.Proofs.Wasm.Auto.Equiv