module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Roots.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms

/-!
# Round 7, the export swap: path updates and the swap set (round 3, pass 1)

* `allIn_pathGet`: reading through a path keeps `AllIn Q`.
* `allIn_pathSet`: **a path update keeps `AllIn Q` under `SafeWrites`**, the interface the `pathSet`
  member of the evaluator induction needs. `safeWrites_of_noExp`: it holds when no record the update
  writes into has an `EXPORTS` field.
* On a module-instance image (the only records of the swap set with an `EXPORTS` field):
  * `pathGet_modImg_absent`: a step `.A` at an atom that is not a field of `moduleinst` fails, so
    every update or extension through it fails (`pathSet_modImg_absent_idx`, `…_slice`);
  * `pathSet_modImg_dot`, `pathSet_modImg_dot_idx`, `pathSet_modImg_dot_slice`: a path
    `.A[e].B…` with `A` one of the address-list fields fails, because `.A[e]` is an address;
  * `pathSet_modImg_tables`, `pathSet_modImg_mems`: `.TABLES[0] = r` and `.MEMS[0] = r` with a record
    `r` succeed, and the result is no longer in the swap set (`not_allIn_QC_tables`,
    `not_allIn_QC_mems`), although the root was (`allIn_QC_modImg`).

So `AllIn (QC c)` is not an invariant of the evaluator on untyped scopes: the update roots of
`$with_tableinst` and `$with_meminst` (`$sof(z)[.TABLES[…] = ti]`, `$sof(z)[.MEMS[…] = mi]`) must be
known not to be module images. That is the typing half of item 2, still open.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Roots

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge (moduleInstToValue)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

variable {Q : Value → Prop} {env : Env} {ρ : VarEnv}

/-! ## Reading and writing through a path -/

theorem allIn_pathGet {v : Value} (hv : AllIn Q v) :
    ∀ (p : Path) (n : Nat) (u : Value), pathGet n env ρ v p = .ok u → AllIn Q u
  | _, 0, _, h => by simp [pathGet] at h
  | .rootP, _ + 1, u, h => by
    simp only [pathGet, Except.ok.injEq] at h
    exact h ▸ hv
  | .idxP p _, n + 1, u, h => by
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u₀, h₀, _, _, _, _, hi⟩ := h
    exact (allIn_pathGet hv p n u₀ h₀).idx? hi
  | .sliceP p _ _, n + 1, u, h => by
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u₀, h₀, _, _, _, _, _, _, _, _, hi⟩ := h
    exact (allIn_pathGet hv p n u₀ h₀).slice? hi
  | .dotP p _, n + 1, u, h => by
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u₀, h₀, hi⟩ := h
    exact (allIn_pathGet hv p n u₀ h₀).field? hi

/-- A field write keeps `AllIn Q` when the record has no `EXPORTS` field or stays in `Q`. -/
theorem allIn_setField {u w u' : Value} {a : AtomS} (hu : AllIn Q u) (hw : AllIn Q w)
    (hQ : ∀ gs, u = .struct gs → hasExp gs = true → Q (.struct (setF gs a w)))
    (h : u.setField a w = some u') : AllIn Q u' := by
  cases u with
  | struct gs =>
    cases hx : hasExp gs with
    | false => exact AllIn.setField hu hx hw h
    | true =>
      simp only [Value.setField_struct, Option.some.injEq] at h
      subst h
      exact ⟨fun _ => hQ gs rfl hx, allInf_map_set hw hu.2⟩
  | opt o => cases o <;> simp [Value.setField] at h
  | _ => simp [Value.setField] at h

/-- **A path update keeps `AllIn Q`** when its writes are safe. -/
theorem allIn_pathSet {v : Value} (hv : AllIn Q v) :
    ∀ (p : Path) (n : Nat) (w u : Value), AllIn Q w → SafeWrites Q env ρ v p →
      pathSet n env ρ v p w = .ok u → AllIn Q u
  | _, 0, _, _, _, _, h => by simp [pathSet] at h
  | .rootP, _ + 1, w, u, hw, _, h => by
    simp only [pathSet, Except.ok.injEq] at h
    exact h ▸ hw
  | .idxP p _, n + 1, w, u, hw, hs, h => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u₀, h₀, _, _, _, _, u', hi, hr⟩ := h
    exact allIn_pathSet hv p n u' u ((allIn_pathGet hv p n u₀ h₀).setIdx hw hi) hs hr
  | .sliceP p _ _, n + 1, w, u, hw, hs, h => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u₀, h₀, _, _, _, _, _, _, _, _, u', hi, hr⟩ := h
    exact allIn_pathSet hv p n u' u ((allIn_pathGet hv p n u₀ h₀).setSlice hw hi) hs hr
  | .dotP p a, n + 1, w, u, hw, hs, h => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u₀, h₀, u', hi, hr⟩ := h
    have hu' : AllIn Q u' :=
      allIn_setField (allIn_pathGet hv p n u₀ h₀) hw
        (fun gs he hx => hs.1 n gs (he ▸ h₀) hx w hw) hi
    exact allIn_pathSet hv p n u' u hu' hs.2 hr

/-- `SafeWrites` holds when no record that the update writes into has an `EXPORTS` field. -/
theorem safeWrites_of_noExp {v : Value} :
    ∀ p : Path, (∀ q a, IsWrite q a p → ∀ m gs, pathGet m env ρ v q = .ok (.struct gs) →
      hasExp gs = false) → SafeWrites Q env ρ v p
  | .rootP, _ => trivial
  | .idxP p _, h => safeWrites_of_noExp p fun q a hq => h q a (.idx hq)
  | .sliceP p _ _, h => safeWrites_of_noExp p fun q a hq => h q a (.slice hq)
  | .dotP p a, h => ⟨fun m gs hg hx => (by rw [h p a .here m gs hg] at hx; cases hx),
      safeWrites_of_noExp p fun q b hq => h q b (.dot hq)⟩

/-! ## Module-instance images -/

/-- A module-instance image. -/
abbrev modImg (m : ModuleInst) : Value := moduleInstToValue Sim.CT m

theorem field?_modImg_num {m : ModuleInst} {A : AtomS} (hA : A ∈ numAtoms) :
    ∃ ks : List Nat, (modImg m).field? A = some (.list (ks.map fun k => .num (.natN k))) := by
  simp only [numAtoms, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, by simp [modImg, moduleInstToValue, Value.field?]; rfl⟩

theorem field?_modImg_absent {m : ModuleInst} {A : AtomS} (hA : A ∉ modAtoms) :
    (modImg m).field? A = none := by
  simp only [modAtoms, numAtoms, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hA
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hA
  simp [modImg, moduleInstToValue, Value.field?, List.find?, Ne.symm h1, Ne.symm h2, Ne.symm h3,
    Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9]

/-- **A step at an atom that is not a field of `moduleinst` fails.** -/
theorem pathGet_modImg_absent {m : ModuleInst} {A : AtomS} (hA : A ∉ modAtoms) (n : Nat)
    (u : Value) : pathGet n env ρ (modImg m) (.dotP .rootP A) ≠ .ok u := by
  intro h
  cases n with
  | zero => simp [pathGet] at h
  | succ n =>
    cases n with
    | zero => simp [pathGet] at h
    | succ n => simp [pathGet, field?_modImg_absent hA] at h

theorem pathSet_modImg_absent_idx {m : ModuleInst} {A : AtomS} (hA : A ∉ modAtoms) (n : Nat)
    (e : Exp) (w u : Value) :
    pathSet n env ρ (modImg m) (.idxP (.dotP .rootP A) e) w ≠ .ok u := by
  intro h
  cases n with
  | zero => simp [pathSet] at h
  | succ n =>
    simp only [pathSet, Res.bind_eq_ok] at h
    obtain ⟨u₀, h₀, -⟩ := h
    exact pathGet_modImg_absent hA n u₀ h₀

theorem pathSet_modImg_absent_slice {m : ModuleInst} {A : AtomS} (hA : A ∉ modAtoms) (n : Nat)
    (e₁ e₂ : Exp) (w u : Value) :
    pathSet n env ρ (modImg m) (.sliceP (.dotP .rootP A) e₁ e₂) w ≠ .ok u := by
  intro h
  cases n with
  | zero => simp [pathSet] at h
  | succ n =>
    simp only [pathSet, Res.bind_eq_ok] at h
    obtain ⟨u₀, h₀, -⟩ := h
    exact pathGet_modImg_absent hA n u₀ h₀

/-- `.A[e]` of a module image, for an address-list field `A`, is an address. -/
theorem pathGet_modImg_idx {m : ModuleInst} {A : AtomS} (hA : A ∈ numAtoms) (e : Exp) :
    ∀ (n : Nat) (u : Value), pathGet n env ρ (modImg m) (.idxP (.dotP .rootP A) e) = .ok u →
      ∃ k : Nat, u = .num (.natN k) := by
  intro n u h
  obtain ⟨ks, hks⟩ := field?_modImg_num (m := m) hA
  cases n with
  | zero => simp [pathGet] at h
  | succ n =>
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u₀, h₀, _, _, i, _, hi⟩ := h
    cases n with
    | zero => simp [pathGet] at h₀
    | succ n =>
      cases n with
      | zero => simp [pathGet] at h₀
      | succ n =>
        simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok, Except.ok.injEq,
          exists_eq_left', hks, Option.some.injEq] at h₀
        subst h₀
        simp only [Value.idx?_list, List.getElem?_map, Option.map_eq_some_iff] at hi
        obtain ⟨k, -, rfl⟩ := hi
        exact ⟨k, rfl⟩

/-- **`.A[e].B = w` fails on a module image** for an address-list field `A`. -/
theorem pathSet_modImg_dot {m : ModuleInst} {A B : AtomS} (hA : A ∈ numAtoms) (e : Exp)
    (n : Nat) (w u : Value) :
    pathSet n env ρ (modImg m) (.dotP (.idxP (.dotP .rootP A) e) B) w ≠ .ok u := by
  intro h
  cases n with
  | zero => simp [pathSet] at h
  | succ n =>
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u₀, h₀, u', hi, -⟩ := h
    obtain ⟨k, rfl⟩ := pathGet_modImg_idx hA e n u₀ h₀
    simp [Value.setField] at hi

theorem pathGet_modImg_dot {m : ModuleInst} {A B : AtomS} (hA : A ∈ numAtoms) (e : Exp)
    (n : Nat) (u : Value) :
    pathGet n env ρ (modImg m) (.dotP (.idxP (.dotP .rootP A) e) B) ≠ .ok u := by
  intro h
  cases n with
  | zero => simp [pathGet] at h
  | succ n =>
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u₀, h₀, hi⟩ := h
    obtain ⟨k, rfl⟩ := pathGet_modImg_idx hA e n u₀ h₀
    simp [Value.field?] at hi

/-- **`.A[e].B[e'] = w` fails on a module image** for an address-list field `A`. -/
theorem pathSet_modImg_dot_idx {m : ModuleInst} {A B : AtomS} (hA : A ∈ numAtoms) (e e' : Exp)
    (n : Nat) (w u : Value) :
    pathSet n env ρ (modImg m) (.idxP (.dotP (.idxP (.dotP .rootP A) e) B) e') w ≠ .ok u := by
  intro h
  cases n with
  | zero => simp [pathSet] at h
  | succ n =>
    simp only [pathSet, Res.bind_eq_ok] at h
    obtain ⟨u₀, h₀, -⟩ := h
    exact pathGet_modImg_dot hA e n u₀ h₀

/-- **`.A[e].B[e₁ : e₂] = w` fails on a module image** for an address-list field `A`. -/
theorem pathSet_modImg_dot_slice {m : ModuleInst} {A B : AtomS} (hA : A ∈ numAtoms)
    (e e₁ e₂ : Exp) (n : Nat) (w u : Value) :
    pathSet n env ρ (modImg m) (.sliceP (.dotP (.idxP (.dotP .rootP A) e) B) e₁ e₂) w ≠ .ok u := by
  intro h
  cases n with
  | zero => simp [pathSet] at h
  | succ n =>
    simp only [pathSet, Res.bind_eq_ok] at h
    obtain ⟨u₀, h₀, -⟩ := h
    exact pathGet_modImg_dot hA e n u₀ h₀

/-! ## The two updates that leave the swap set -/

variable {H : Type}

/-- A module image of `c` is in the swap set. -/
theorem allIn_QC_modImg {c : Config H} {m : ModuleInst} (hm : m ∈ Round7.mods c) :
    AllIn (QC c) (modImg m) :=
  allIn_moduleInstToValue (Or.inl ⟨m, hm, rfl⟩)

/-- The image of `m` with the address list of field `A` replaced by `l`. -/
def modImgWith (m : ModuleInst) (A : AtomS) (l : List Value) : Value :=
  .struct (setF (match modImg m with | .struct gs => gs | _ => []) A (.list l))

/-- A record whose address-list field `A` holds a record is no module image. -/
theorem modImgWith_ne {m m' : ModuleInst} {A : AtomS} (hA : A = "TABLES" ∨ A = "MEMS")
    {gs : List (AtomS × Value)} {l : List Value} :
    modImgWith m A (.struct gs :: l) ≠ modImg m' := by
  intro h
  have hf := congrArg (fun v => Value.field? v A) h
  rcases hA with rfl | rfl
  · simp [modImgWith, modImg, moduleInstToValue, setF, Value.field?] at hf
    cases ht : m'.tables <;> simp [ht] at hf
  · simp [modImgWith, modImg, moduleInstToValue, setF, Value.field?] at hf
    cases ht : m'.mems <;> simp [ht] at hf

/-- A record with an `EXPORTS` field that is no module image is outside the swap set. -/
theorem not_allIn_QC_of_ne {c : Config H} {gs : List (AtomS × Value)} (hx : hasExp gs = true)
    (hne : ∀ m, Value.struct gs ≠ modImg m) : ¬ AllIn (QC c) (.struct gs) := by
  rintro ⟨hq, -⟩
  rcases hq hx with ⟨m, -, he⟩ | ⟨m, -, he, -⟩
  · exact hne m he
  · exact hne m he

theorem hasExp_modImgWith (m : ModuleInst) (A : AtomS) (l : List Value) (hA : A ≠ "EXPORTS") :
    hasExp (setF (match modImg m with | .struct gs => gs | _ => []) A (.list l)) = true := by
  simp [modImg, moduleInstToValue, setF, hasExp, Ne.symm hA]

/-- **`.TABLES[0] = r` on a module image succeeds**, and its result has `r` at `TABLES[0]`. -/
theorem pathSet_modImg_tables (m : ModuleInst) (t : Nat) (ts : List Nat) (ht : m.tables = t :: ts)
    (gs : List (AtomS × Value)) :
    pathSet 3 env ρ (modImg m) (.idxP (.dotP .rootP "TABLES") (.numE (.natN 0))) (.struct gs) =
      .ok (modImgWith m "TABLES" (.struct gs :: ts.map fun a => .num (.natN a))) := by
  simp [pathSet, pathGet, evalExp, modImg, moduleInstToValue, modImgWith, setF, Value.field?,
    Value.setIdx, Value.setField, Value.asNat?, ht]

/-- **`.MEMS[0] = r` on a module image succeeds**, and its result has `r` at `MEMS[0]`. -/
theorem pathSet_modImg_mems (m : ModuleInst) (t : Nat) (ts : List Nat) (ht : m.mems = t :: ts)
    (gs : List (AtomS × Value)) :
    pathSet 3 env ρ (modImg m) (.idxP (.dotP .rootP "MEMS") (.numE (.natN 0))) (.struct gs) =
      .ok (modImgWith m "MEMS" (.struct gs :: ts.map fun a => .num (.natN a))) := by
  simp [pathSet, pathGet, evalExp, modImg, moduleInstToValue, modImgWith, setF, Value.field?,
    Value.setIdx, Value.setField, Value.asNat?, ht]

/-- **`.TABLES[0] = r` leaves the swap set**: the result is not `AllIn (QC c)`, although the root
was (`allIn_QC_modImg`). -/
theorem not_allIn_QC_tables (c : Config H) (m : ModuleInst) (gs : List (AtomS × Value))
    (l : List Value) : ¬ AllIn (QC c) (modImgWith m "TABLES" (.struct gs :: l)) :=
  not_allIn_QC_of_ne (hasExp_modImgWith m _ _ (by decide))
    fun _ => modImgWith_ne (Or.inl rfl)

/-- **`.MEMS[0] = r` leaves the swap set.** -/
theorem not_allIn_QC_mems (c : Config H) (m : ModuleInst) (gs : List (AtomS × Value))
    (l : List Value) : ¬ AllIn (QC c) (modImgWith m "MEMS" (.struct gs :: l)) :=
  not_allIn_QC_of_ne (hasExp_modImgWith m _ _ (by decide))
    fun _ => modImgWith_ne (Or.inr rfl)

end Silmaril.Wasm.SpecTec.Sim.Round7.Roots
