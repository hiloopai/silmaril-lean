module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Instance

/-!
# The WIT binary round trip: worlds

`decWorld_encodeWorld`: the component type the encoder writes for a world
decodes to the world's normal form.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-- The imports (`imp`) or exports of a decoder state, and the others. -/
def CSt.outs (imp : Bool) (c : CSt) : List DItem := if imp then c.imports else c.exports
def CSt.others (imp : Bool) (c : CSt) : List DItem := if imp then c.exports else c.imports

theorem Interface.Valid.of_find {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) {j : IfaceName}
    {b : Interface} (h : env.find? j = some b) : j.Valid ∧ b.Valid := by
  induction env with
  | nil => cases h
  | cons x env ih =>
    obtain ⟨j', b'⟩ := x
    by_cases hj : j' = j
    · have hb : b' = b := by simpa [Env.find?, liveDeps.lookup', hj] using h
      have := henv (j', b') (by simp)
      exact ⟨hj ▸ this.1, hb ▸ this.2⟩
    · exact ih (fun ib hib => henv ib (by simp [hib]))
        (by simpa [Env.find?, liveDeps.lookup', hj] using h)

theorem modify_run (f : Enc → Enc) (e : Enc) : (modify f : EncM Unit).run e = .ok ((), f e) := rfl

theorem Inv.setImportTypes {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) (b : Bool) :
    Inv { e with importTypes := b } cst dst :=
  ⟨hI.outer, hI.olen, hI.ook, hI.otypes, hI.ilen, hI.inst, hI.inner⟩

/-- The result of one world item. -/
def ItemOK (imp : Bool) (cst cst' : CSt) (it : WorldItem) : Prop :=
  (cst'.outs imp).map DItem.toWorldItem = (cst.outs imp).map DItem.toWorldItem ++ [it.normalize] ∧
  cst'.others imp = cst.others imp

theorem addInst_outs (c : CSt) (b : Interface) (key : IfaceName ⊕ String) (imp : Bool) :
    (c.addInst b key imp).outs imp = c.outs imp ++ [.iface key b] ∧
      (c.addInst b key imp).others imp = c.others imp := by
  cases imp <;> exact ⟨rfl, rfl⟩

/-- A function import or export. -/
theorem funcItem_sim {e e' : Enc} {cst : CSt} (hI : Inv e cst none) {f : Func} (hf : f.Valid) (imp : Bool)
    (h : (do let k ← funcType f; emit (if imp then .import ↑f.mangled (.func k) else .inst (.export ↑f.mangled (.func k)))).run e = .ok ((), e')) :
    ∃ cst', Inv e' cst' none ∧ e'.importTypes = e.importTypes ∧ ItemOK imp cst cst' (.func f) := by
  obtain ⟨k, e₁, h₁, h₂⟩ := run_bind_ok h
  obtain ⟨c₁, d₁, hI₁, hG₁, hk⟩ := funcType_sim hI f h₁
  have hd : d₁ = none := hG₁.dst_none
  subst hd
  cases h₂
  have hk' : slotAt c₁.slots k = .ok (.func f.sig) := slotAt_of_get hk
  have hit : funcItem c₁ f.mangled k = .ok (.func f.strip) := by
    simp only [funcItem, hk', bind, Except.bind]; rw [demangle_mangled hf]; rfl
  let c₂ : CSt := if imp then { c₁ with imports := c₁.imports ++ [.func f.strip] }
    else { c₁ with exports := c₁.exports ++ [.func f.strip] }
  have hstep : compStep c₁ (if imp then .import ↑f.mangled (.func k) else .inst (.export ↑f.mangled (.func k))) =
      .ok c₂ := by
    cases imp <;> simp only [c₂, ↓reduceIte, Bool.false_eq_true, compStep, hit] <;> rfl
  have hi := hI₁.inner_none
  refine ⟨c₂, ⟨compSteps_snoc hI₁.outer hstep, by cases imp <;> exact hI₁.olen, by cases imp <;> exact hI₁.ook,
    by cases imp <;> exact hI₁.otypes, by cases imp <;> exact hI₁.ilen, by cases imp <;> exact hI₁.inst,
    by simp [InnerOK, hi]⟩, hG₁.importTypes, ?_, ?_⟩
  · cases imp <;> simp [c₂, CSt.outs, DItem.toWorldItem, WorldItem.normalize, hG₁.imports, hG₁.exports]
  · cases imp <;> simp [c₂, CSt.others, hG₁.imports, hG₁.exports]

/-- An interface item of a world. -/
theorem ifaceItem_sim {e e' : Enc} {cst : CSt} (hI : Inv e cst none) {body : Interface} (hb : body.Valid)
    {key : IfaceName ⊕ String} {n : String} (hkey : nameKey n = .ok key) (imp : Bool)
    (h : (do let k ← encodeInstance key.getLeft? body; emit (instDecl imp n k)).run e = .ok ((), e')) :
    ∃ cst', Inv e' cst' none ∧ e'.importTypes = e.importTypes ∧
      (cst'.outs imp).map DItem.toWorldItem = (cst.outs imp).map DItem.toWorldItem ++
        [DItem.toWorldItem (.iface key body.normalize)] ∧ cst'.others imp = cst.others imp := by
  obtain ⟨c₁, hS, hI', hT⟩ := encodeInstance_item hI hb hkey imp h
  obtain ⟨ho, hot⟩ := addInst_outs c₁ body.normalize key imp
  refine ⟨_, hI', hT, ?_, ?_⟩
  · rw [ho]; cases imp <;> simp [CSt.outs, hS.imports, hS.exports]
  · rw [hot]; cases imp <;> simp [CSt.others, hS.imports, hS.exports]

theorem Interface.normalize_valid_strip (n : String) (b : Interface) :
    DItem.toWorldItem (.iface (.inr n) b.normalize) = (WorldItem.ifaceInline n b).normalize := rfl

/-- An interface referenced by a world. -/
theorem refItem_sim {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) {e e' : Enc} {cst : CSt}
    (hI : Inv e cst none) (hT : e.importTypes = false) {j : IfaceName} {d : Option String} {st : Stability}
    (hv : j.Valid) (imp : Bool) (h : (worldItem env imp (.ifaceRef j d st)).run e = .ok ((), e')) :
    ∃ cst', Inv e' cst' none ∧ e'.importTypes = false ∧ ItemOK imp cst cst' (.ifaceRef j d st) := by
  simp only [worldItem] at h
  cases hb : env.find? j with
  | none => rw [hb] at h; exact absurd h run_fail
  | some b =>
    rw [hb] at h
    obtain ⟨-, hbv⟩ := Interface.Valid.of_find henv hb
    obtain ⟨c', hI', hT', ho, hot⟩ := ifaceItem_sim (key := .inl j) hI hbv (nameKey_id hv) imp h
    exact ⟨c', hI', hT'.trans hT, by rw [ho]; rfl, hot⟩

/-- A type imported by a world. -/
theorem typeItem_sim {env : Env} {e e' : Enc} {cst : CSt} (hI : Inv e cst none) {td : TypeDef}
    (h : (worldItem env true (.type td)).run e = .ok ((), e')) :
    ∃ cst', Inv e' cst' none ∧ e'.importTypes = false ∧ ItemOK true cst cst' (.type td) := by
  simp only [worldItem, ↓reduceIte] at h
  obtain ⟨u, e₁, h₁, h₂⟩ := run_bind_ok h
  rw [modify_run] at h₁; cases h₁
  obtain ⟨u₃, e₃, h₅, h₆⟩ := run_bind_ok h₂
  rw [modify_run] at h₆; cases h₆
  obtain ⟨c', hI', hins, himp, hexp, hT', -, -⟩ := typeDef_sim_world (hI.setImportTypes true) rfl td h₅
  refine ⟨c', hI'.setImportTypes false, rfl, ?_, ?_⟩
  · simp [CSt.outs, himp, DItem.toWorldItem, WorldItem.normalize]
  · simp [CSt.others, hexp]

/-- **One world item** is read back in normal form. -/
theorem worldItem_sim {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) {e e' : Enc} {cst : CSt}
    (hI : Inv e cst none) (hT : e.importTypes = false) {it : WorldItem} (hv : it.Valid) (imp : Bool)
    (h : (worldItem env imp it).run e = .ok ((), e')) :
    ∃ cst', Inv e' cst' none ∧ e'.importTypes = false ∧ ItemOK imp cst cst' it := by
  match it, hv, imp, h with
  | .ifaceRef j d st, hv, imp, h => exact refItem_sim henv hI hT hv imp h
  | .ifaceInline n b, hv, imp, h =>
    obtain ⟨c', hI', hT', ho, hot⟩ := ifaceItem_sim (key := .inr n) hI hv.2 (nameKey_plain hv.1) imp h
    exact ⟨c', hI', hT'.trans hT, by rw [ho]; rfl, hot⟩
  | .func f, hv, imp, h =>
    obtain ⟨c', hI', hT', hok⟩ := funcItem_sim hI hv imp h
    exact ⟨c', hI', hT'.trans hT, hok⟩
  | .type td, _, false, h => exact absurd h run_fail
  | .type td, _, true, h => exact typeItem_sim hI h

theorem worldItems_sim {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) (imp : Bool) :
    ∀ (its : List WorldItem) {e e' : Enc} {cst : CSt}, (∀ it ∈ its, it.Valid) → Inv e cst none →
      e.importTypes = false → (worldItems env imp its).run e = .ok ((), e') →
      ∃ cst', Inv e' cst' none ∧ e'.importTypes = false ∧
        (cst'.outs imp).map DItem.toWorldItem = (cst.outs imp).map DItem.toWorldItem ++ its.map WorldItem.normalize ∧
        cst'.others imp = cst.others imp
  | [], _, _, cst, _, hI, hT, h => by
    obtain ⟨-, rfl⟩ := run_pure_ok h
    exact ⟨cst, hI, hT, by simp, rfl⟩
  | it :: its, _, _, _, hv, hI, hT, h => by
    obtain ⟨u, e₁, h₁, h₂⟩ := run_bind_ok h
    obtain ⟨c₁, hI₁, hT₁, ho₁, hot₁⟩ := worldItem_sim henv hI hT (hv it (by simp)) imp h₁
    obtain ⟨c₂, hI₂, hT₂, ho₂, hot₂⟩ := worldItems_sim henv imp its (fun x hx => hv x (by simp [hx])) hI₁ hT₁ h₂
    exact ⟨c₂, hI₂, hT₂, by rw [ho₂, ho₁]; simp, hot₂.trans hot₁⟩

/-- The empty encoder state and the empty decoder state agree. -/
theorem Inv.init : Inv {} {} none :=
  ⟨rfl, rfl, SlotsOK.empty _, fun _ _ h => by simp [lookup] at h, rfl, fun _ _ h => by simp [lookup] at h,
    trivial⟩

/-- **Worlds round-trip**: the component type of a world decodes to the
world's normal form. -/
theorem decWorld_encodeWorld {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid) {w : World}
    (hw : w.Valid) {ds : List ComponentDecl} (h : encodeWorld env w = .ok ds) : decWorld ds = .ok w.normalize := by
  unfold encodeWorld at h
  cases hr : (do worldItems env true w.imports; worldItems env false w.exports : EncM Unit).run {} with
  | error err => rw [hr] at h; cases h
  | ok r =>
    obtain ⟨u, e⟩ := r
    rw [hr] at h; cases h
    obtain ⟨u₁, e₁, h₁, h₂⟩ := run_bind_ok hr
    obtain ⟨c₁, hI₁, hT₁, ho₁, hot₁⟩ := worldItems_sim henv true w.imports hw.1 Inv.init rfl h₁
    obtain ⟨c₂, hI₂, -, ho₂, hot₂⟩ := worldItems_sim henv false w.exports hw.2 hI₁ hT₁ h₂
    have hi : c₂.imports.map DItem.toWorldItem = w.imports.map WorldItem.normalize := by
      have h1 : c₂.imports = c₁.imports := hot₂
      simpa [CSt.outs, h1] using ho₁
    have he : c₂.exports.map DItem.toWorldItem = w.exports.map WorldItem.normalize := by
      have h2 : c₁.exports = ([] : List DItem) := by simpa [CSt.others] using hot₁
      simpa [CSt.outs, h2] using ho₂
    simp only [decWorld, hI₂.outer, bind, Except.bind, pure, Except.pure, World.normalize, hi, he]

end Silmaril.Wasm.Wit.Binary
