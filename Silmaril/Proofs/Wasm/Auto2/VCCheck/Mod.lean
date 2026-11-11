module

public import Silmaril.Wasm.Auto2.VCCheck.Defs
public import Silmaril.Wasm.Auto2.VCNorm.Thms
public import Silmaril.Wasm.Auto2.VCBridge.Thms

/-!
# The VC stage with memory, callees and normalised conditions: soundness

* `vcCheckM_inv`: what a successful check says (the conditions of the export's code are valid,
  `allValid_of_coveredN`);
* `callees_of`, `calleesValid`: the callees the check finds are in the store and meet their
  total specifications (`genFunc_tsound` on each callee);
* **`modTSpecM_of_vcCheckM`**: `vcCheckM e m j = true` gives `ModTSpecM P e m j` at every profile;
* **`checkMeetsVCN_proved`**: a `proved` verdict of `checkMeetsVCN` is the front end's `ModMeets`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCCheck

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Auto2.VCBridge
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Game (FnType)
open Silmaril.Wasm.Auto.Front (addrOf ModMeets specOfFn)
open Silmaril.Wasm.Auto.Bridge (scalarInt? export_expand mapM_length OrDiv
  meets_orDiv_of_fspecValid)

variable {P : Profile}

theorem fnInst?_inv {m : Module} {j : Nat} {ft : FnType} {fi : FuncInst Nat} {code : Func}
    (h : fnInst? m j = some (ft, fi, code)) :
    ∃ mt I, instance? m = some (mt, I) ∧ I.exports[j]? = some ft ∧
      I.store.funcs[I.addrs.getD j 0]? = some fi ∧ fi.code = .wasm code := by
  unfold fnInst? at h
  split at h
  · rename_i mt I hI
    split at h
    · rename_i ft' fi' hft hfi
      split at h
      · rename_i code' hc
        cases h
        exact ⟨mt, I, hI, hft, hfi, hc⟩
      · cases h
    · cases h
  · cases h

theorem mem_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b
  | [], l', h, b, hb => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    cases hb
  | a :: l, l', h, b, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b₀, hb₀, l₀, hl₀, rfl⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hb₀⟩
    · obtain ⟨a', ha', hf⟩ := mem_of_mapM hl₀ b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hf⟩

theorem calleeCode?_inv {s : Store Nat} {fi : FuncInst Nat} {x p r : Nat} {code : Func}
    (h : calleeCode? s fi x p r = some code) :
    ∃ a' fi' ps rs, fi.module.funcs[x]? = some a' ∧ s.funcs[a']? = some fi' ∧
      fi'.code = .wasm code ∧ fi'.module = fi.module ∧ Expand fi'.type (.func ps rs) ∧
      p = ps.length ∧ r = rs.length := by
  unfold calleeCode? at h
  split at h
  · rename_i a' ha
    split at h
    · rename_i fi' hf
      split at h
      · rename_i code' ps rs hc hx
        split at h
        · rename_i hcond
          cases h
          exact ⟨a', fi', ps, rs, ha, hf, hc, hcond.1, Expand.iff.mpr hx, hcond.2.1, hcond.2.2⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem calleeOK?_inv {e : VcEntryM} {s : Store Nat} {fi : FuncInst Nat}
    {c : Nat × FnSpec × List Fm} {c' : Nat × FnSpec × Func} (hc : c ∈ e.calls)
    (h : calleeOK? e s fi c = some c') :
    c'.1 = c.1 ∧ c'.2.1 = c.2.1 ∧ c.2.1.total = true ∧ c.2.1.calls = [] ∧
      AllValid e.F (genFunc c.2.1 c'.2.2 e.fuel) ∧
      ∃ a' fi' ps rs, fi.module.funcs[c.1]? = some a' ∧ s.funcs[a']? = some fi' ∧
        fi'.code = .wasm c'.2.2 ∧ fi'.module = fi.module ∧ Expand fi'.type (.func ps rs) ∧
        c.2.1.params.length = ps.length ∧ c.2.1.results.length = rs.length := by
  obtain ⟨hT, hcl, hv⟩ := e.callsOK c hc
  unfold calleeOK? at h
  split at h
  · rename_i code hcode
    split at h
    · rename_i hcov
      cases h
      exact ⟨rfl, rfl, hT, hcl, allValid_of_coveredN hcov hv, calleeCode?_inv hcode⟩
    · cases h
  · cases h

/-- The callees the check found are in the store. -/
theorem callees_of {e : VcEntryM} {s : Store Nat} {fi : FuncInst Nat}
    {cs : List (Nat × FnSpec × Func)} (h : calleesOf? e s fi = some cs) :
    Callees (specOf e cs) fi s := by
  intro c' hc'
  obtain ⟨c, hc, hok⟩ := mem_of_mapM h c' hc'
  obtain ⟨h₁, h₂, -, -, -, a', fi', ps, rs, ha, hf, hcode, hmod, hE, hp, hr⟩ := calleeOK?_inv hc hok
  rw [h₁, h₂]
  exact ⟨a', fi', ps, rs, ha, hf, hcode, hmod, hE, hp, hr⟩

/-- The callees the check found meet their total specifications. -/
theorem calleesValid {H : Type} {host : HostSemantics H} {e : VcEntryM} {s : Store Nat}
    {fi : FuncInst Nat} {cs : List (Nat × FnSpec × Func)} (h : calleesOf? e s fi = some cs) :
    CalleesValid .total P host e.F (specOf e cs) := by
  intro c' hc' a'' fi'' ps' rs' hcode hE hp hr
  obtain ⟨c, hc, hok⟩ := mem_of_mapM h c' hc'
  obtain ⟨-, h₂, hT, hcl, hv, -⟩ := calleeOK?_inv hc hok
  rw [h₂] at hp hr ⊢
  refine genFunc_tsound hT hcode hE hp hr hv ?_
  intro c'' hc''
  rw [hcl] at hc''
  cases hc''

/-- What a successful check says about the export. -/
theorem vcCheckM_inv {e : VcEntryM} {m : Module} {j : Nat} (h : vcCheckM e m j = true) :
    ∃ mt I ft fi code cs, instance? m = some (mt, I) ∧ I.exports[j]? = some ft ∧
      I.store.funcs[I.addrs.getD j 0]? = some fi ∧ fi.code = .wasm code ∧
      calleesOf? e (instOf m).store fi = some cs ∧
      ft.params.mapM scalarInt? = some e.S.params ∧ ft.results.mapM scalarInt? = some e.S.results ∧
      AllValid e.F (genFunc (specOf e cs) code e.fuel) := by
  unfold vcCheckM at h
  split at h
  · rename_i ft fi code hfc
    obtain ⟨mt, I, hI, hft, hfi, hc⟩ := fnInst?_inv hfc
    split at h
    · rename_i cs hcs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨mt, I, ft, fi, code, cs, hI, hft, hfi, hc, hcs, h.1.1, h.1.2,
        allValid_of_coveredN h.2 e.valid⟩
    · cases h
  · cases h

/-- **The check gives the total specification of the export** (with memory and callees), at
every profile. -/
theorem modTSpecM_of_vcCheckM {e : VcEntryM} {m : Module} {j : Nat}
    (h : vcCheckM e m j = true) : ModTSpecM P e m j := by
  obtain ⟨mt, I, ft, fi, code, cs, hI, hft, hfi, hc, hcs, hps, hrs, hvc⟩ := vcCheckM_inv h
  intro fi' cs' hfi' hcs'
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, instOf_eq hI]
  rw [instOf_eq hI, haddr, hfi] at hfi'
  cases hfi'
  rw [hcs] at hcs'
  cases hcs'
  have he : Expand fi.type ft.toComp := export_expand hI hft hfi
  refine ⟨genFunc_tsound e.total hc he ?_ ?_ hvc (calleesValid hcs), callees_of hcs⟩
  · show e.S.params.length = _
    rw [Ty.length_ofList, List.length_map, mapM_length hps]
  · show e.S.results.length = _
    rw [Ty.length_ofList, List.length_map, mapM_length hrs]

theorem calleesOf?_toM (e : VcEntry) (s : Store Nat) (fi : FuncInst Nat) :
    calleesOf? e.toM s fi = some [] := rfl

theorem specOf_toM (e : VcEntry) : specOf e.toM [] = e.S := by
  obtain ⟨name, F, S, fuel, conds, valid, total, calls, mem⟩ := e
  cases S
  simp only at calls mem total
  subst calls
  rfl

/-- A check of a pass-1 contract at the computed instance: the total specification of the
export and the precondition at every accepted call. -/
theorem tspec_of_vcCheckM {e : VcEntry} {m : Module} {j : Nat} (h : vcCheckM e.toM m j = true)
    (hpre : ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ) :
    ∃ fi, TFSpecAt P SingleThreaded.Det.noHost (addrOf m j) (fspec e.F e.S (addrOf m j) fi) ∧
      ∀ vs, InvokeOk (instOf m).store (addrOf m j) vs → Silmaril.Wasm.Auto.Equiv.TypedVals e.S.params vs ∧
        (fspec e.F e.S (addrOf m j) fi).pre (instOf m).store vs := by
  obtain ⟨mt, I, ft, fi, code, cs, hI, hft, hfi, hc, hcs, hps, hrs, hvc⟩ := vcCheckM_inv h
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, instOf_eq hI]
  have hfi' : (instOf m).store.funcs[addrOf m j]? = some fi := by rw [instOf_eq hI, haddr, hfi]
  have hts := (modTSpecM_of_vcCheckM (P := P) (e := e.toM) h fi [] hfi' (calleesOf?_toM e _ _)).1
  rw [specOf_toM] at hts
  refine ⟨fi, hts, fun vs hvs => ?_⟩
  rw [instOf_eq hI, haddr] at hvs ⊢
  exact pre_of_invokeOk hI hft hfi hps hpre hvs

/-- **A pass-1 contract accepted by the normalising check meets a reference function** that
agrees with every result its postcondition allows, at every profile, for every reflexive
relation. -/
theorem modMeets_of_vcCheckM {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {e : VcEntry} {m : Module} {j : Nat} {f : List Val → Option Result}
    (h : vcCheckM e.toM m j = true)
    (hpre : ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ) (hf : RefOK e f) :
    ModMeets R P m j f := by
  obtain ⟨fi, hts, hok⟩ := tspec_of_vcCheckM (P := P) h hpre
  have hmeets : Equiv.Meets (entryPoints P SingleThreaded.Det.noHost) (OrDiv R)
      (instOf m).store (addrOf m j) (specOfFn f) :=
    meets_orDiv_of_fspecValid hR hts.valid (fun vs hvs => (hok vs hvs).2)
      (fun vs _ _ hvs hpost => returns_mem_specOfFn hf (hok vs hvs).1 hpost)
      (specOfFn_nonempty f)
  intro vs hvs b hb
  obtain ⟨b', hb', hr⟩ := hmeets vs hvs b hb
  refine ⟨b', hb', hr.resolve_left fun hd => ?_⟩
  have hdiv : Diverges P SingleThreaded.Det.noHost (invoke (instOf m).store (addrOf m j) vs) :=
    diverges_mem_behavioursOf_iff.mp (hd ▸ hb)
  exact hts.invoke_terminates (hok vs hvs).2 hdiv

/-- **A `proved` verdict of the front end with the normalising VC stage** is `ModMeets` at every
profile. -/
theorem checkMeetsVCN_proved {R : Silmaril.Wasm.Auto.Front.Rel} {r : RefEntry} {m : Module}
    {j n : Nat} (h : (checkMeetsVCN R r m j n).verdict = .proved) :
    ModMeets R.toProp P m j r.f := by
  unfold checkMeetsVCN at h
  by_cases hv : vcCheckM r.e.toM m j = true
  · exact modMeets_of_vcCheckM (Silmaril.Wasm.Auto.Bridge.rel_refl R) hv r.pre r.ref
  · exfalso
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · rename_i hb
      rw [hb] at h
      cases h
    · cases h

end Silmaril.Wasm.Auto2.VCCheck
