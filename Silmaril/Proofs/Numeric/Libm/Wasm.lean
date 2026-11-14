module

public import Silmaril.Numeric.Libm.Wasm.Defs
public import Silmaril.Numeric.Libm.Lattice.Thms
public import Silmaril.Wasm.Logic.Core.Thms
public import Silmaril.WasmSpec.Common.Thms
public import Silmaril.Wasm.Binaryen.AdequacyModule

/-!
# libm problems for Wasm modules: proofs

* `Exports.mono`: a node of an export weakens along the lattice.
* `funcImplements_of_runs`: at a deterministic profile, a run of `$invoke` to `g x` on every
  input gives `BitExact g` (uniqueness of normal forms, `steps_det_nf`).
* `computes_unop`, `computes_binop`: the bodies `local.get 0; f64.op` and
  `local.get 0; local.get 1; f64.op` return the canonical result at every profile.
* `funcImplements_unop`, `funcImplements_call_binop`: functions with these bodies (the second
  through a forwarding `call`) are bit-exact with `floatUnOp64 op` and `floatBinOp64 op`.
-/

@[expose] public section

namespace Silmaril.Proofs.Numeric.Libm.WasmExport

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Libm Silmaril.Numeric.Libm.WasmExport
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.Logic.Core

/-! ## Monotonicity -/

theorem Exports.mono {α : Type} [WasmArgs α] {P : Numerics.Profile} {m : Module} {name : String}
    {N N' : (α → Outcome F64) → Prop} (h : Exports P m name N) (hN : ∀ i, N i → N' i) :
    Exports P m name N' := by
  obtain ⟨s, a, he, h₁, h₂, h₃⟩ := h
  exact ⟨s, a, he, h₁, h₂, fun impl hi => hN _ (h₃ impl hi)⟩

/-! ## Determinism -/

theorem f64v_inj {x y : F64} (h : f64v x = f64v y) : x = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  simp only [f64v, Val.num.injEq] at h
  injection h with _ h
  rw [UInt64.toBitVec_inj.mp h]

variable {o : GrowKind → Nat → Nat → Nat → Bool}

theorem stopped_vals {s : Store Nat} {f : Frame} {vs : List Val} :
    Stopped (Profile.deterministic o) ⟨s, f, vals vs⟩ :=
  fun _ h => Silmaril.Wasm.Binaryen.not_step_vals' h

/-- At a deterministic profile, one run to `g x` on every input is all there is. -/
theorem funcImplements_of_runs {α : Type} [WasmArgs α] {s : Store Nat} {a : Nat} {g : α → F64}
    (h : ∀ x : α, ∃ s', Steps (Profile.deterministic o) noHost (invoke s a (WasmArgs.args x))
      ⟨s', {}, vals [f64v (g x)]⟩) :
    FuncImplements (Profile.deterministic o) s a (BitExact · g) := by
  refine ⟨fun x => ?_, fun x c hc hs => ?_, fun impl himpl x => ?_⟩
  · obtain ⟨s', hs⟩ := h x
    exact ⟨g x, s', {}, hs⟩
  · obtain ⟨s', hs'⟩ := h x
    have e := Silmaril.Wasm.Binaryen.steps_det_nf hc hs' hs stopped_vals
    exact ⟨g x, by rw [e]⟩
  · obtain ⟨s', hs'⟩ := h x
    obtain ⟨s'', f'', hr⟩ := himpl x
    have e := Silmaril.Wasm.Binaryen.steps_det_nf hr hs' stopped_vals stopped_vals
    simp only [Config.mk.injEq, SingleThreaded.Det.vals_inj, List.cons.injEq, and_true] at e
    exact f64v_inj e.2.2

/-! ## Single-instruction bodies -/

theorem floatUnOpP_canonical (P : Numerics.Profile) (op : FloatUnOp) (b : BitVec 64) :
    floatUnOpP P .f64 op b (floatUnOp .f64 op b) := by
  unfold floatUnOpP
  split
  · exact floatUnOpRel_self .f64 op b
  · rfl

theorem floatBinOpP_canonical (P : Numerics.Profile) (op : FloatBinOp) (b c : BitVec 64) :
    floatBinOpP P .f64 op b c (floatBinOp .f64 op b c) := by
  unfold floatBinOpP
  split
  · exact floatBinOpRel_self .f64 op b c
  · rfl

/-- `local.get 0; f64.op` returns `floatUnOp64 op x`, at every profile. -/
theorem computes_unop (ty : TypeIdx) (op : FloatUnOp) (x : F64) :
    WasmSpec.Computes ⟨ty, [], [.localGet ⟨0⟩, .floatUnOp .f64 op]⟩ [f64v x]
      [f64v (floatUnOp64 op x)] := by
  intro H P host s m
  let F : Frame := Frame.forCall m [f64v x] []
  have h₁ : Step P host ⟨s, F, [.plain (.localGet ⟨0⟩), .plain (.floatUnOp .f64 op)]⟩
      ⟨s, F, [(f64v x).toAdmin, .plain (.floatUnOp .f64 op)]⟩ :=
    Step.ctxtInstrs (vs := []) (is := [.plain (.localGet ⟨0⟩)])
      (is' := [(f64v x).toAdmin]) (rest := [.plain (.floatUnOp .f64 op)])
      (Step.variable (VariableStep.localGet (v := f64v x) rfl)) (Or.inr (by simp))
  have h₂ : Step P host ⟨s, F, [(f64v x).toAdmin, .plain (.floatUnOp .f64 op)]⟩
      ⟨s, F, vals [f64v (floatUnOp64 op x)]⟩ :=
    Step.numeric (NumericStep.floatUnOp (floatUnOpP_canonical P op x.bits.toBitVec))
  exact WP.step h₁ (WP.step h₂ (wp_vals ⟨rfl, rfl, rfl⟩))

/-- `local.get 0; local.get 1; f64.op` returns `floatBinOp64 op x y`, at every profile. -/
theorem computes_binop (ty : TypeIdx) (op : FloatBinOp) (x y : F64) :
    WasmSpec.Computes ⟨ty, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .floatBinOp .f64 op]⟩
      [f64v x, f64v y] [f64v (floatBinOp64 op x y)] := by
  intro H P host s m
  let F : Frame := Frame.forCall m [f64v x, f64v y] []
  have h₁ : Step P host
      ⟨s, F, [.plain (.localGet ⟨0⟩), .plain (.localGet ⟨1⟩), .plain (.floatBinOp .f64 op)]⟩
      ⟨s, F, [(f64v x).toAdmin, .plain (.localGet ⟨1⟩), .plain (.floatBinOp .f64 op)]⟩ :=
    Step.ctxtInstrs (vs := []) (is := [.plain (.localGet ⟨0⟩)])
      (is' := [(f64v x).toAdmin]) (rest := [.plain (.localGet ⟨1⟩), .plain (.floatBinOp .f64 op)])
      (Step.variable (VariableStep.localGet (v := f64v x) rfl)) (Or.inr (by simp))
  have h₂ : Step P host
      ⟨s, F, [(f64v x).toAdmin, .plain (.localGet ⟨1⟩), .plain (.floatBinOp .f64 op)]⟩
      ⟨s, F, [(f64v x).toAdmin, (f64v y).toAdmin, .plain (.floatBinOp .f64 op)]⟩ :=
    Step.ctxtInstrs (vs := [f64v x]) (is := [.plain (.localGet ⟨1⟩)])
      (is' := [(f64v y).toAdmin]) (rest := [.plain (.floatBinOp .f64 op)])
      (Step.variable (VariableStep.localGet (v := f64v y) rfl)) (Or.inl (by simp))
  have h₃ : Step P host
      ⟨s, F, [(f64v x).toAdmin, (f64v y).toAdmin, .plain (.floatBinOp .f64 op)]⟩
      ⟨s, F, vals [f64v (floatBinOp64 op x y)]⟩ :=
    Step.numeric (NumericStep.floatBinOp
      (floatBinOpP_canonical P op x.bits.toBitVec y.bits.toBitVec))
  exact WP.step h₁ (WP.step h₂ (WP.step h₃ (wp_vals ⟨rfl, rfl, rfl⟩)))

/-! ## Functions -/

/-- A call of a function whose body computes `res` from `args` runs to `res` (any profile). -/
theorem invoke_of_computes {P : Numerics.Profile} {s : Store Nat} {a : Nat} {fi : FuncInst Nat}
    {fn : Func} {ps rs : Ty (.list .val)} {args res : List Val}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) (he : Expand fi.type (.func ps rs))
    (hargs : args.length = ps.length) (hres : res.length = rs.length)
    (h : WasmSpec.Computes fn args res) :
    ∃ s', Steps P noHost (invoke s a args) ⟨s', {}, vals res⟩ := by
  have hspec : WasmSpec.PureSpec P noHost a (fun s' => s' = s) (α := Unit) (fun _ => args)
      (fun _ => res) :=
    WasmSpec.Computes.funcSpec (fun _ => h) (by rintro _ rfl; exact hfi) hcode he
      (fun _ => hargs) (fun _ => hres)
  obtain ⟨s', res', hs, -, _, -, rfl⟩ := hspec.invoke ⟨rfl, (), rfl⟩
  exact ⟨s', hs⟩

/-- **A function whose body is `local.get 0; f64.op`** is bit-exact with `floatUnOp64 op`
at every deterministic profile. -/
theorem funcImplements_unop {s : Store Nat} {a : Nat} {fi : FuncInst Nat} {ty : TypeIdx}
    {op : FloatUnOp} {ps rs : Ty (.list .val)} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm ⟨ty, [], [.localGet ⟨0⟩, .floatUnOp .f64 op]⟩)
    (he : Expand fi.type (.func ps rs)) (hps : ps.length = 1) (hrs : rs.length = 1) :
    FuncImplements (α := F64) (Profile.deterministic o) s a (BitExact · (floatUnOp64 op)) :=
  funcImplements_of_runs fun x =>
    invoke_of_computes hfi hcode he hps.symm hrs.symm (computes_unop ty op x)

/-- **A function whose body forwards its two arguments to a function whose body is
`local.get 0; local.get 1; f64.op`** is bit-exact with `floatBinOp64 op` at every
deterministic profile. -/
theorem funcImplements_call_binop {s : Store Nat} {a b : Nat} {fi gi : FuncInst Nat}
    {ty ty' : TypeIdx} {k : FuncIdx} {op : FloatBinOp} {ps rs ps' rs' : Ty (.list .val)}
    (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm ⟨ty, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .call k]⟩)
    (he : Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hk : fi.module.funcs[k.toNat]? = some b) (hgi : s.funcs[b]? = some gi)
    (hcode' : gi.code = .wasm ⟨ty', [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .floatBinOp .f64 op]⟩)
    (he' : Expand gi.type (.func ps' rs')) (hps' : ps'.length = 2) (hrs' : rs'.length = 1) :
    FuncImplements (α := F64 × F64) (Profile.deterministic o) s a
      (BitExact · (fun p => floatBinOp64 op p.1 p.2)) := by
  refine funcImplements_of_runs fun p => ?_
  obtain ⟨x, y⟩ := p
  let z := floatBinOp64 op x y
  have hcallee : WasmSpec.PureSpec (Profile.deterministic o) noHost b (fun s' => s' = s)
      (α := Unit) (fun _ => [f64v x, f64v y]) (fun _ => [f64v z]) :=
    WasmSpec.Computes.funcSpec (fun _ => computes_binop ty' op x y) (by rintro _ rfl; exact hgi)
      hcode' he' (fun _ => hps'.symm) (fun _ => hrs'.symm)
  have hspec : FuncSpec (Profile.deterministic o) noHost a
      (fun s' args => s' = s ∧ args = [f64v x, f64v y])
      (fun _ _ s' res => s' = s ∧ res = [f64v z]) := by
    refine FuncSpec.of_body (by rintro _ _ ⟨rfl, -⟩; exact hfi) hcode he
      (by rintro _ _ ⟨-, rfl⟩; exact hps.symm) ?_
    intro s₀ args hpre
    obtain ⟨hs₀, hargs⟩ := hpre
    subst hargs
    rw [hs₀, hrs]
    let F : Frame := Frame.forCall fi.module [f64v x, f64v y] []
    have h₁ : Step (Profile.deterministic o) noHost
        ⟨s, F, [.plain (.localGet ⟨0⟩), .plain (.localGet ⟨1⟩), .plain (.call k)]⟩
        ⟨s, F, [(f64v x).toAdmin, .plain (.localGet ⟨1⟩), .plain (.call k)]⟩ :=
      Step.ctxtInstrs (vs := []) (is := [.plain (.localGet ⟨0⟩)])
        (is' := [(f64v x).toAdmin]) (rest := [.plain (.localGet ⟨1⟩), .plain (.call k)])
        (Step.variable (VariableStep.localGet (v := f64v x) rfl)) (Or.inr (by simp))
    have h₂ : Step (Profile.deterministic o) noHost
        ⟨s, F, [(f64v x).toAdmin, .plain (.localGet ⟨1⟩), .plain (.call k)]⟩
        ⟨s, F, vals ([] ++ [f64v x, f64v y]) ++ .plain (.call k) :: []⟩ :=
      Step.ctxtInstrs (vs := [f64v x]) (is := [.plain (.localGet ⟨1⟩)])
        (is' := [(f64v y).toAdmin]) (rest := [.plain (.call k)])
        (Step.variable (VariableStep.localGet (v := f64v y) rfl)) (Or.inl (by simp))
    refine WP.step h₁ (WP.step h₂ ?_)
    exact wp_call (vs := []) (rest := []) hk (by rw [hgi]; rfl) hcallee ⟨rfl, (), rfl⟩
      (by
        rintro s₁ _ ⟨hs₁, _, -, rfl⟩
        rw [hs₁]
        show WP _ _ s _ (vals [f64v z]) _
        exact wp_vals ⟨rfl, rfl, rfl⟩)
  obtain ⟨s', res, hs, rfl, rfl⟩ := hspec.invoke ⟨rfl, rfl⟩
  exact ⟨s', hs⟩

/-! ## Checkers -/

theorem idx_zero {kind : IndexKind} {i : Idx kind} (h : i.toNat = 0) : i = ⟨0⟩ :=
  Idx.toNat_injective (by rw [h]; rfl)

theorem idx_one {kind : IndexKind} {i : Idx kind} (h : i.toNat = 1) : i = ⟨1⟩ :=
  Idx.toNat_injective (by rw [h]; rfl)

theorem exportInst?_sound {m : Module} {name : String} {s : Store Nat} {a : Nat}
    {fi : FuncInst Nat} (h : exportInst? m name = some (s, a, fi)) :
    exportFunc? m name = some (s, a) ∧ s.funcs[a]? = some fi := by
  unfold exportInst? at h
  cases he : exportFunc? m name with
  | none => simp [he] at h
  | some p =>
    obtain ⟨s', a'⟩ := p
    cases hf : s'.funcs[a']? with
    | none => simp [he, hf] at h
    | some fi' =>
      simp only [he, hf, Option.bind_some, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hf⟩

theorem arity_sound {fi : FuncInst Nat} {n k : Nat} (h : arity fi = some (n, k)) :
    ∃ ps rs, Expand fi.type (.func ps rs) ∧ ps.length = n ∧ rs.length = k := by
  unfold arity at h
  split at h
  · rename_i ps rs he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨ps, rs, Expand.iff.mpr he, h.1, h.2⟩
  · exact absurd h (by simp)

theorem unopOf_sound {fi : FuncInst Nat} {op : FloatUnOp} (h : unopOf fi = some op) :
    ∃ ty, fi.code = .wasm ⟨ty, [], [.localGet ⟨0⟩, .floatUnOp .f64 op]⟩ := by
  unfold unopOf at h
  split at h
  · rename_i ty i op' hc
    split at h
    · rename_i hi
      cases h
      exact ⟨ty, by rw [hc, idx_zero hi]⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem binopOf_sound {fi : FuncInst Nat} {op : FloatBinOp} (h : binopOf fi = some op) :
    ∃ ty, fi.code = .wasm ⟨ty, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .floatBinOp .f64 op]⟩ := by
  unfold binopOf at h
  split at h
  · rename_i ty i j op' hc
    split at h
    · rename_i hi
      cases h
      exact ⟨ty, by rw [hc, idx_zero hi.1, idx_one hi.2]⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem callOf_sound {fi : FuncInst Nat} {k : FuncIdx} (h : callOf fi = some k) :
    ∃ ty, fi.code = .wasm ⟨ty, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .call k]⟩ := by
  unfold callOf at h
  split at h
  · rename_i ty i j k' hc
    split at h
    · rename_i hi
      cases h
      exact ⟨ty, by rw [hc, idx_zero hi.1, idx_one hi.2]⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem exports_unop {m : Module} {name : String} {op : FloatUnOp}
    (h : checkUnop m name op = true) :
    Exports (α := F64) (Profile.deterministic o) m name (BitExact · (floatUnOp64 op)) := by
  unfold checkUnop at h
  split at h
  · rename_i s a fi hi
    obtain ⟨hu, ha⟩ := of_decide_eq_true h
    obtain ⟨he, hf⟩ := exportInst?_sound hi
    obtain ⟨ty, hc⟩ := unopOf_sound hu
    obtain ⟨ps, rs, hx, hps, hrs⟩ := arity_sound ha
    exact ⟨s, a, he, funcImplements_unop hf hc hx hps hrs⟩
  · exact absurd h (by simp)

theorem exports_call_binop {m : Module} {name : String} {op : FloatBinOp}
    (h : checkCallBinop m name op = true) :
    Exports (α := F64 × F64) (Profile.deterministic o) m name
      (BitExact · (fun p => floatBinOp64 op p.1 p.2)) := by
  unfold checkCallBinop at h
  split at h
  · rename_i s a fi hi
    split at h
    · rename_i k hk
      split at h
      · rename_i b hb
        split at h
        · rename_i gi hg
          obtain ⟨hu, ha, ha'⟩ := of_decide_eq_true h
          obtain ⟨he, hf⟩ := exportInst?_sound hi
          obtain ⟨ty, hc⟩ := callOf_sound hk
          obtain ⟨ty', hc'⟩ := binopOf_sound hu
          obtain ⟨ps, rs, hx, hps, hrs⟩ := arity_sound ha
          obtain ⟨ps', rs', hx', hps', hrs'⟩ := arity_sound ha'
          exact ⟨s, a, he, funcImplements_call_binop hf hc hx hps hrs hb hg hc' hx' hps' hrs'⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end Silmaril.Proofs.Numeric.Libm.WasmExport

namespace Silmaril.Proofs.Numeric.Libm.WasmExport

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Libm Silmaril.Numeric.Libm.WasmExport
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-! ## Builds -/

theorem BuildExports.mono {α : Type} [WasmArgs α] {b : ByteArray} {name : String}
    {N N' : (α → Outcome F64) → Prop} (h : BuildExports b name N) (hN : ∀ i, N i → N' i) :
    BuildExports b name N' := by
  unfold BuildExports at h ⊢
  split at h
  · rename_i m hm
    exact fun o => Exports.mono (h o) hN
  · exact h.elim

theorem buildExports_unop {b : ByteArray} {name : String} {op : FloatUnOp}
    (h : checkUnopBytes b name op = true) :
    BuildExports (α := F64) b name (BitExact · (floatUnOp64 op)) := by
  unfold checkUnopBytes at h
  unfold BuildExports
  split at h
  · rename_i m hm
    exact fun _ => exports_unop h
  · exact absurd h (by simp)

theorem buildExports_call_binop {b : ByteArray} {name : String} {op : FloatBinOp}
    (h : checkCallBinopBytes b name op = true) :
    BuildExports (α := F64 × F64) b name (BitExact · (fun p => floatBinOp64 op p.1 p.2)) := by
  unfold checkCallBinopBytes at h
  unfold BuildExports
  split at h
  · rename_i m hm
    exact fun _ => exports_call_binop h
  · exact absurd h (by simp)

end Silmaril.Proofs.Numeric.Libm.WasmExport
