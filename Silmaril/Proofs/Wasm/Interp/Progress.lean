module

public import Silmaril.Proofs.Wasm.Interp.Control
public import Silmaril.Wasm.Execution.Core.Sim.TypedControlPrefix
public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped

@[expose] public section

/-!
# Native progress from Core typing (proofs)

On a Core configuration that is typed in some evaluation context (silmaril-lean's
`Sim.ContextTyped`), in a store of native-profile functions, a native flat instruction at the
focus does not get the native interpreter stuck: `evalFlat_progress`. Typed Core progress
(`ContextTyped.progress_nonexit`) gives a host-free step at the instruction
(`head_at_plain`), silmaril-lean's executable head step `interpHead` is complete for it
(`interpHead_exact`), and that head step computes what `Binaryen.evalFlat` computes. The same
argument gives the `i32` condition of an `if` (`truthy_progress`). New proofs. Used by
`Silmaril.Proofs.Wasm.Interp.Total`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
  Silmaril.Wasm.Execution.Core.Sim

variable {H : Type} {o : GrowOracle} {s : Store H} {f : Frame} {stk : List Val}
  {rest : List Admin}

/-! ## Typed fragments step host-free -/

theorem plug_store (E : ActiveCtx) (c : Config H) : (E.plug c).store = c.store := by
  induction E generalizing c with
  | hole => rfl
  | suffix _ _ ih => exact ih _
  | label _ _ _ _ _ ih => exact ih _
  | handler _ _ _ _ _ ih => exact ih _
  | frame _ _ _ _ _ ih => exact ih _

theorem ContextTyped.storeOk' {c : Config H} (h : ContextTyped c) : StoreOk c.store := by
  obtain ⟨E, ts, h⟩ := h
  have hs := ConfigOk.storeOk h
  rwa [plug_store] at hs

/-- In a native store, a step of any host is host-free. -/
theorem noHost_of_native {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hF : Binaryen.NativeFuncsOk c.store.funcs) (h : Step P host c c') :
    Step P Det.noHost c c' := by
  rcases Step.split_host h with h | ⟨E, a, hh, args, hd, -⟩
  · exact h
  · obtain ⟨fi, -, -, -, hfi, hcode, -⟩ := decompose?_sound hd
    obtain ⟨fn, hfn, -⟩ := hF fi (List.mem_of_getElem? hfi)
    rw [hcode] at hfn
    cases hfn

/-- The first non-value of a native fragment, as seen by `fnv`. -/
theorem fnv_plain {i : Instr} (hv : (Admin.plain i).val? = none) :
    fnv (vals stk.reverse ++ .plain i :: rest) = (stk.reverse, .plain i :: rest) := by
  simp [fnv_cons_of_none hv]

/-- **A typed fragment steps at its focus** `i` (a non-value, non-exit, non-throwing plain
instruction): there is a head step of `i` on the top values. -/
theorem head_at_plain {i : Instr} (ht : ContextTyped ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩)
    (hF : Binaryen.NativeFuncsOk s.funcs) (hv : (Admin.plain i).val? = none)
    (hb : ¬ Blocked (.plain i)) (htr : i ≠ .throwRef) :
    ∃ vs args c₀, stk.reverse = vs ++ args ∧ Head (profile o) s f args (.plain i) c₀ := by
  obtain ⟨c', hc'⟩ := ContextTyped.progress_nonexit (P := profile o) ht hv hb (by simp)
    (fun h => htr (by cases h; rfl))
  have hs : Step (profile o) Det.noHost ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩ c' :=
    noHost_of_native hF hc'
  have hfnv := fnv_plain (stk := stk) (rest := rest) hv
  rcases Step.decomp hs with hd | hbub
  · obtain ⟨vs, args, e, rest', c₀, hf, -, hh, -⟩ := fnv_headDec hd
    simp only at hf
    rw [hfnv, Prod.mk.injEq, List.cons.injEq] at hf
    obtain ⟨h1, rfl, -⟩ := hf
    exact ⟨vs, args, c₀, h1, hh⟩
  · obtain ⟨p, q, u, r, -, ⟨hf, -⟩ | ⟨a, hf, -⟩⟩ := fnv_bubble hbub <;> simp only at hf <;>
      rw [hfnv] at hf <;> simp at hf
    exact absurd (by rw [hf.2.1]) htr

/-- The executable head step is complete at a plain instruction. -/
theorem interpHead_of_head {vs args : List Val} {i : Instr} {c₀ : Config H} (hs : StoreOk s)
    (hinv : IHeadInv f (.plain i)) (hh : Head (profile o) s f args (.plain i) c₀) :
    ∃ x, interpHead o s f (vs ++ args) (.plain i) = some x := by
  rcases interpHead_exact hs f (vs ++ args) args (.plain i) c₀ hinv hh ⟨vs, rfl⟩ with
    h | ⟨-, ⟨_, _, _, _, _, _, h, -⟩ | ⟨_, _, _, _, _, _, h, -⟩ | ⟨_, _, _, _, _, _, h, -⟩⟩
  · exact ⟨_, h⟩
  all_goals cases h

/-! ## The head step computes the native step -/

theorem asInt_exec {t : IntType} {v : Val} {x : BitVec t.width} (h : Pure.asInt t v = some x) :
    ∃ y, Binaryen.asInt t v = some y := by
  rcases v with ⟨⟨ty, b⟩⟩ | _ | _ <;> (try rcases ty with ty | ty) <;> (try cases ty) <;> cases t <;>
    simp_all [Pure.asInt, Binaryen.asInt]
  all_goals exact ⟨_, rfl⟩

theorem top2_rev {a b : Val} (h : Pure.top2 stk.reverse = some (a, b)) :
    ∃ r, stk = b :: a :: r := by
  rcases stk with _ | ⟨y, _ | ⟨x, r⟩⟩ <;> simp [Pure.top2] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨r, rfl⟩

theorem top1_rev {a : Val} (h : Pure.top1 stk.reverse = some a) : ∃ r, stk = a :: r := by
  rcases stk with _ | ⟨y, r⟩ <;> simp [Pure.top1] at h
  exact ⟨r, by rw [h]⟩

theorem interp_intBinOp {t : IntType} {op : IntBinOp} {x : Nat × Config H}
    (h : interpHead o s f stk.reverse (.plain (.intBinOp t op)) = some x) :
    ∃ r, Binaryen.evalFlat s f stk (.intBinOp t op) = some r := by
  simp only [interpHead, famOf, numericStep?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨a, b⟩, h2, x₁, hx, y₁, hy, -⟩ := h
  obtain ⟨r, rfl⟩ := top2_rev h2
  obtain ⟨x', hx'⟩ := asInt_exec hx
  obtain ⟨y', hy'⟩ := asInt_exec hy
  simp only [Binaryen.evalFlat, hx', hy']
  rcases hz : intBinOp t op x' y' with e | z
  · exact ⟨(s, f, .trap), by simp [hz]⟩
  · exact ⟨(s, f, .normal (Binaryen.ofInt t z :: r)), by simp [hz]⟩

theorem interp_intRelOp {t : IntType} {op : IntRelOp} {x : Nat × Config H}
    (h : interpHead o s f stk.reverse (.plain (.intRelOp t op)) = some x) :
    ∃ r, Binaryen.evalFlat s f stk (.intRelOp t op) = some r := by
  simp only [interpHead, famOf, numericStep?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨a, b⟩, h2, x₁, hx, y₁, hy, -⟩ := h
  obtain ⟨r, rfl⟩ := top2_rev h2
  obtain ⟨x', hx'⟩ := asInt_exec hx
  obtain ⟨y', hy'⟩ := asInt_exec hy
  exact ⟨_, by simp [Binaryen.evalFlat, hx', hy']; rfl⟩

theorem interp_intUnOp {t : IntType} {op : IntUnOp} {x : Nat × Config H}
    (h : interpHead o s f stk.reverse (.plain (.intUnOp t op)) = some x) :
    ∃ r, Binaryen.evalFlat s f stk (.intUnOp t op) = some r := by
  simp only [interpHead, famOf, numericStep?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨a, h1, x₁, hx, -⟩ := h
  obtain ⟨r, rfl⟩ := top1_rev h1
  obtain ⟨x', hx'⟩ := asInt_exec hx
  exact ⟨_, by simp [Binaryen.evalFlat, hx']; rfl⟩

theorem interp_intTestOp {t : IntType} {op : IntTestOp} {x : Nat × Config H}
    (h : interpHead o s f stk.reverse (.plain (.intTestOp t op)) = some x) :
    ∃ r, Binaryen.evalFlat s f stk (.intTestOp t op) = some r := by
  simp only [interpHead, famOf, numericStep?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨a, h1, x₁, hx, -⟩ := h
  obtain ⟨r, rfl⟩ := top1_rev h1
  obtain ⟨x', hx'⟩ := asInt_exec hx
  exact ⟨_, by simp [Binaryen.evalFlat, hx']; rfl⟩

theorem interp_localGet {l : LocalIdx} {x : Nat × Config H}
    (h : interpHead o s f stk.reverse (.plain (.localGet l)) = some x) :
    ∃ r, Binaryen.evalFlat s f stk (.localGet l) = some r := by
  simp only [interpHead, famOf, variableStep?] at h
  split at h
  · rename_i v hv
    simp only [Frame.local?] at hv
    exact ⟨_, by simp [Binaryen.evalFlat, hv]; rfl⟩
  · cases h

theorem interp_globalGet {g : GlobalIdx} {x : Nat × Config H}
    (h : interpHead o s f stk.reverse (.plain (.globalGet g)) = some x) :
    ∃ r, Binaryen.evalFlat s f stk (.globalGet g) = some r := by
  simp only [interpHead, famOf, variableStep?] at h
  rcases hp : s.global? f g with _ | p
  · rw [hp] at h; cases h
  exact ⟨_, by simp [Binaryen.evalFlat, hp]; rfl⟩

theorem interp_globalSet {g : GlobalIdx} {x : Nat × Config H} (hne : stk ≠ [])
    (h : interpHead o s f stk.reverse (.plain (.globalSet g)) = some x) :
    ∃ r, Binaryen.evalFlat s f stk (.globalSet g) = some r := by
  simp only [interpHead, famOf, variableStep?] at h
  rcases hp : s.global? f g with _ | p
  · rw [hp] at h
    cases htop : VarTab.top1? stk.reverse <;> rw [htop] at h <;> simp at h
  rcases stk with _ | ⟨w, r⟩
  · exact absurd rfl hne
  · exact ⟨_, by simp [Binaryen.evalFlat, hp]; rfl⟩

theorem interp_brIf {l : LabelIdx} {x : Nat × Config H}
    (h : interpHead o s f stk.reverse (.plain (.brIf l)) = some x) :
    ∃ r, Binaryen.evalFlat s f stk (.brIf l) = some r := by
  simp only [interpHead, famOf] at h
  rcases Interp.orElse_some h with h | h
  · simp only [controlStep?, Admin.isCallRef, Ctl.plainStep?, Bool.false_eq_true,
      ↓reduceIte] at h
    split at h
    · rename_i c hc
      rw [List.getLast?_reverse] at hc
      rcases stk with _ | ⟨w, r⟩
      · cases hc
      · simp only [List.head?_cons, Option.some.injEq] at hc
        subst hc
        exact ⟨_, by simp [Binaryen.evalFlat, Binaryen.truthy, Binaryen.asInt]; exact ⟨_, rfl, rfl⟩⟩
    · cases h
  · simp [adminStep?] at h

theorem interp_select {t : Option (List ValType)} {x : Nat × Config H}
    (h : interpHead o s f stk.reverse (.plain (.select t)) = some x) :
    ∃ r, Binaryen.evalFlat s f stk (.select t) = some r := by
  simp only [interpHead, famOf, parametricStep?, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at h
  obtain ⟨⟨a, b, c⟩, h3, cv, hc, -⟩ := h
  rcases stk with _ | ⟨c', _ | ⟨b', _ | ⟨a', r⟩⟩⟩ <;> simp [Pure.top3] at h3
  have hc₀ : Pure.asI32 c' = some cv := by simpa [← h3.2.2] using hc
  have hc' : c' = .num ⟨.int .i32, cv⟩ := by
    rcases c' with ⟨⟨ty, bits⟩⟩ | _ | _ <;> (try rcases ty with ty | ty) <;> (try cases ty) <;>
      simp [Pure.asI32] at hc₀
    cases hc₀; rfl
  subst hc'
  exact ⟨_, rfl⟩

theorem interp_brTable {ls : List LabelIdx} {d : LabelIdx} {x : Nat × Config H}
    (h : interpHead o s f stk.reverse (.plain (.brTable ls d)) = some x) :
    ∃ r, Binaryen.evalFlat s f stk (.brTable ls d) = some r := by
  simp only [interpHead, famOf] at h
  rcases Interp.orElse_some h with h | h
  · simp only [controlStep?, Admin.isCallRef, Ctl.plainStep?, Bool.false_eq_true,
      ↓reduceIte] at h
    split at h
    · rename_i c hc
      rw [List.getLast?_reverse] at hc
      rcases stk with _ | ⟨w, r⟩
      · cases hc
      · simp only [List.head?_cons, Option.some.injEq] at hc
        subst hc
        exact ⟨_, rfl⟩
    · cases h
  · simp [adminStep?] at h

theorem interp_if {bt : BlockType} {b₁ b₂ : List Instr} {x : Nat × Config H}
    (h : interpHead o s f stk.reverse (.plain (.if_ bt b₁ b₂)) = some x) :
    ∃ cv r b, stk = cv :: r ∧ Binaryen.truthy cv = some b := by
  simp only [interpHead, famOf] at h
  rcases Interp.orElse_some h with h | h
  · simp only [controlStep?, Admin.isCallRef, Ctl.plainStep?, Bool.false_eq_true,
      ↓reduceIte] at h
    split at h
    · rename_i c hc
      rw [List.getLast?_reverse] at hc
      rcases stk with _ | ⟨w, r⟩
      · cases hc
      · simp only [List.head?_cons, Option.some.injEq] at hc
        subst hc
        exact ⟨_, r, _, rfl, by simp [Binaryen.truthy, Binaryen.asInt]; exact ⟨_, rfl, rfl⟩⟩
    · cases h
  · simp [adminStep?] at h

/-! ## Progress -/

theorem iHeadInv_of {i : Instr} (h₁ : ∀ rt, i ≠ .refTest rt ∧ i ≠ .refCast rt)
    (h₂ : ∀ l a b, i ≠ .brOnCast l a b ∧ i ≠ .brOnCastFail l a b) : IHeadInv f (.plain i) := by
  refine ⟨fun rt h => ?_, fun l a b h => ?_⟩
  · rcases h with h | h
    · exact absurd (Admin.plain.inj h) (h₁ rt).1
    · exact absurd (Admin.plain.inj h) (h₁ rt).2
  · rcases h with h | h
    · exact absurd (Admin.plain.inj h) (h₂ l a b).1
    · exact absurd (Admin.plain.inj h) (h₂ l a b).2

/-- The side conditions of `head_at_plain` and `interpHead_of_head` for an ordinary plain
instruction. -/
macro "plain_side" : tactic => `(tactic| first
  | rfl
  | (rintro (⟨_, h⟩ | h | h) <;> simp [Admin.IsReturnCallRef] at h)
  | (intro h; cases h)
  | exact iHeadInv_of (fun _ => ⟨(by intro h; cases h), (by intro h; cases h)⟩)
      (fun _ _ _ => ⟨(by intro h; cases h), (by intro h; cases h)⟩))

/-- The executable head step at a typed focus. -/
theorem interp_at {i : Instr} (ht : ContextTyped ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩)
    (hF : Binaryen.NativeFuncsOk s.funcs) (hv : (Admin.plain i).val? = none)
    (hb : ¬ Blocked (.plain i)) (htr : i ≠ .throwRef) (hinv : IHeadInv f (.plain i)) :
    ∃ x, interpHead o s f stk.reverse (.plain i) = some x := by
  obtain ⟨vs, args, c₀, heq, hh⟩ := head_at_plain (o := o) ht hF hv hb htr
  rw [heq]
  exact interpHead_of_head (ContextTyped.storeOk' ht) hinv hh

set_option linter.unusedTactic false in
/-- **Native progress at a flat instruction** of a typed fragment that passes the check. -/
theorem evalFlat_progress {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {o' : Option Nat} {i : Instr}
    (hc : flatChk F mi nl ret labels stk.length i = some o') (hi : ∀ x, i ≠ .call x)
    (ht : ContextTyped ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩)
    (hF : Binaryen.NativeFuncsOk s.funcs) : ∃ r, Binaryen.evalFlat s f stk i = some r := by
  let o : GrowOracle := fun _ _ _ _ => false
  cases i
  all_goals try first
    | exact absurd rfl (hi _)
    | (simp [flatChk, flatEff] at hc; done)
    | (exact ⟨_, rfl⟩)
  case intUnOp t op =>
    obtain ⟨x, hx⟩ : ∃ x, interpHead o s f stk.reverse (.plain (.intUnOp t op)) = some x :=
      interp_at (o := o) ht hF (by plain_side) (by plain_side) (by plain_side)
      (by plain_side)
    exact interp_intUnOp hx
  case intTestOp t op =>
    obtain ⟨x, hx⟩ : ∃ x, interpHead o s f stk.reverse (.plain (.intTestOp t op)) = some x :=
      interp_at (o := o) ht hF (by plain_side) (by plain_side) (by plain_side)
      (by plain_side)
    exact interp_intTestOp hx
  case intBinOp t op =>
    obtain ⟨x, hx⟩ : ∃ x, interpHead o s f stk.reverse (.plain (.intBinOp t op)) = some x :=
      interp_at (o := o) ht hF (by plain_side) (by plain_side) (by plain_side)
      (by plain_side)
    exact interp_intBinOp hx
  case intRelOp t op =>
    obtain ⟨x, hx⟩ : ∃ x, interpHead o s f stk.reverse (.plain (.intRelOp t op)) = some x :=
      interp_at (o := o) ht hF (by plain_side) (by plain_side) (by plain_side)
      (by plain_side)
    exact interp_intRelOp hx
  case localGet l =>
    obtain ⟨x, hx⟩ : ∃ x, interpHead o s f stk.reverse (.plain (.localGet l)) = some x :=
      interp_at (o := o) ht hF (by plain_side) (by plain_side) (by plain_side)
      (by plain_side)
    exact interp_localGet hx
  case globalGet g =>
    obtain ⟨x, hx⟩ : ∃ x, interpHead o s f stk.reverse (.plain (.globalGet g)) = some x :=
      interp_at (o := o) ht hF (by plain_side) (by plain_side) (by plain_side)
      (by plain_side)
    exact interp_globalGet hx
  case globalSet g =>
    obtain ⟨x, hx⟩ : ∃ x, interpHead o s f stk.reverse (.plain (.globalSet g)) = some x :=
      interp_at (o := o) ht hF (by plain_side) (by plain_side) (by plain_side)
      (by plain_side)
    have hne : stk ≠ [] := by
      rintro rfl
      simp [flatChk, flatEff] at hc
    exact interp_globalSet hne hx
  case select t =>
    obtain ⟨x, hx⟩ : ∃ x, interpHead o s f stk.reverse (.plain (.select t)) = some x :=
      interp_at (o := o) ht hF (by plain_side) (by plain_side) (by plain_side)
      (by plain_side)
    exact interp_select hx
  case brTable ls d =>
    obtain ⟨x, hx⟩ : ∃ x, interpHead o s f stk.reverse (.plain (.brTable ls d)) = some x :=
      interp_at (o := o) ht hF (by plain_side) (by plain_side) (by plain_side)
      (by plain_side)
    exact interp_brTable hx
  case brIf l =>
    obtain ⟨x, hx⟩ : ∃ x, interpHead o s f stk.reverse (.plain (.brIf l)) = some x :=
      interp_at (o := o) ht hF (by plain_side) (by plain_side) (by plain_side)
      (by plain_side)
    exact interp_brIf hx
  all_goals
    rcases stk with _ | ⟨v, r⟩
    · simp only [flatChk, flatEff] at hc
      split at hc <;> simp_all ; all_goals omega
    · exact ⟨_, rfl⟩

/-- **The condition of a typed `if` is an `i32`.** -/
theorem truthy_progress {bt : BlockType} {b₁ b₂ : List Instr}
    (ht : ContextTyped ⟨s, f, vals stk.reverse ++ .plain (.if_ bt b₁ b₂) :: rest⟩)
    (hF : Binaryen.NativeFuncsOk s.funcs) :
    ∃ cv r b, stk = cv :: r ∧ Binaryen.truthy cv = some b := by
  obtain ⟨x, hx⟩ := interp_at (o := fun _ _ _ _ => false) ht hF (by plain_side)
    (by plain_side) (by plain_side) (by plain_side)
  exact interp_if hx

end Silmaril.Wasm.Interp
