module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Basic
public import Silmaril.Wasm.Binaryen.Profile
public import Silmaril.Wasm.Validation.Subtyping.DefInv
public import Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck
public import Silmaril.Wasm.Execution.Core.Instantiation
public import Silmaril.Wasm.SingleThreaded.Determinism.FamDet

@[expose] public section

/-! # Integer parameters

If every function type of a module's type section has numeric parameters, so
does every defined function type the module allocates (`numParams_allocTypes`),
and so does every store function whose type matches such an import
(`numParams_externAddr`): function subtyping is contravariant in the
parameters, and a numeric type has no proper supertype.
-/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-- The function type of a sub type, if any, has numeric parameters. -/
def SubNumP (st : CSubType) : Prop :=
  ∀ ps rs, st.body = .func ps rs → ∀ p ∈ ps.toList, ∃ t, p = .num t

/-- Every function type of a recursive group has numeric parameters. -/
def GroupNumP (g : CRecType) : Prop := ∀ st ∈ g.subs.toList, SubNumP st

theorem subst_toList (σ : Subst) {k : TKind} : ∀ (l : Ty (.list k)),
    (l.subst σ).toList = l.toList.map (Ty.subst σ)
  | .nil => rfl
  | .cons a l => by simp [Ty.subst, subst_toList σ l]

theorem SubNumP.subst {st : CSubType} (h : SubNumP st) (σ : Subst) : SubNumP (st.subst σ) := by
  cases st with
  | sub fin sups ct =>
    intro ps rs hb p hp
    simp only [Ty.subst, Ty.body] at hb
    cases ct with
    | func ps₀ rs₀ =>
      simp only [Ty.subst] at hb
      injection hb with h1 h2
      subst h1
      rw [subst_toList] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      obtain ⟨t, rfl⟩ := h ps₀ rs₀ rfl q hq
      exact ⟨t, rfl⟩
    | struct fs => simp [Ty.subst] at hb
    | array f => simp [Ty.subst] at hb

theorem GroupNumP.subst {g : CRecType} (h : GroupNumP g) (σ : Subst) : GroupNumP (g.subst σ) := by
  cases g with
  | group subs =>
    intro st hst
    simp only [Ty.subst, Ty.subs] at hst
    rw [subst_toList] at hst
    obtain ⟨st₀, h₀, rfl⟩ := List.mem_map.1 hst
    exact SubNumP.subst (h st₀ h₀) _

theorem GroupNumP.rollrt {g : CRecType} (h : GroupNumP g) (x : Nat) : GroupNumP (rollrt x g) := by
  cases g with
  | group subs =>
    intro st hst
    simp only [Silmaril.Wasm.Validation.rollrt, Ty.subs] at hst
    rw [subst_toList] at hst
    obtain ⟨st₀, h₀, rfl⟩ := List.mem_map.1 hst
    exact SubNumP.subst (h st₀ h₀) _

theorem GroupNumP.unrollrt {g : CRecType} (h : GroupNumP g) : GroupNumP (unrollrt g) := by
  cases g with
  | group subs =>
    intro st hst
    simp only [Silmaril.Wasm.Validation.unrollrt, Ty.subs] at hst
    rw [subst_toList] at hst
    obtain ⟨st₀, h₀, rfl⟩ := List.mem_map.1 hst
    exact SubNumP.subst (h st₀ h₀) _

theorem numParams_defn {g : CRecType} (h : GroupNumP g) (i : Nat) : NumParams (Ty.defn g i) := by
  intro ps rs he p hp
  rcases he with ⟨hu⟩
  simp only [unrolldt] at hu
  exact GroupNumP.unrollrt h _ (List.mem_of_getElem? hu) ps rs rfl p hp

/-- The groups of a type section whose function types have profile parameters. -/
theorem groupNumP_liftRec {rt : RecType}
    (h : ∀ st ∈ rt.types, ∀ ft : FuncType, st.body = .func ft →
      ∀ t ∈ ft.params ++ ft.results, Binaryen.profileValType t = true) :
    GroupNumP (liftRec rt) := by
  intro st hst
  simp only [liftRec, Ty.subs, Ty.toList_ofList] at hst
  obtain ⟨st₀, h₀, rfl⟩ := List.mem_map.1 hst
  intro ps rs hb p hp
  simp only [liftSub, Ty.body] at hb
  cases hc : st₀.body with
  | func ft =>
    rw [hc] at hb
    simp only [liftComp, liftResult] at hb
    injection hb with h1 h2
    subst h1
    rw [Ty.toList_ofList] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hpv := h st₀ h₀ ft hc q (List.mem_append_left _ hq)
    rcases q with (t | t | t)
    · exact ⟨t, rfl⟩
    · simp [Binaryen.profileValType] at hpv
    · simp [Binaryen.profileValType] at hpv
  | struct fs => rw [hc] at hb; simp [liftComp] at hb
  | array f => rw [hc] at hb; simp [liftComp] at hb

/-- **Allocated types** of a type section with profile function types have integer
parameters. -/
theorem numParams_allocTypes {rts : List RecType} (h : ∀ rt ∈ rts, GroupNumP (liftRec rt)) :
    ∀ d ∈ allocTypes rts, NumParams d := by
  suffices key : ∀ (acc : List DefType), (∀ d ∈ acc, ∃ g i, d = Ty.defn g i ∧ GroupNumP g) →
      ∀ d ∈ rts.foldl (fun acc rt =>
        acc ++ (rolldt acc.length (liftRec rt)).map (·.substAll (acc.map .dt))) acc,
      ∃ g i, d = Ty.defn g i ∧ GroupNumP g by
    intro d hd
    obtain ⟨g, i, rfl, hg⟩ := key [] (by simp) d hd
    exact numParams_defn hg i
  induction rts with
  | nil => intro acc hacc d hd; exact hacc d hd
  | cons rt rts ih =>
    intro acc hacc d hd
    simp only [List.foldl_cons] at hd
    refine ih (fun rt' hrt' => h rt' (by simp [hrt'])) _ ?_ d hd
    intro d' hd'
    rcases List.mem_append.1 hd' with hd' | hd'
    · exact hacc d' hd'
    · simp only [List.mem_map] at hd'
      obtain ⟨d₀, hd₀, rfl⟩ := hd'
      simp only [rolldt, List.mem_map] at hd₀
      obtain ⟨i, -, rfl⟩ := hd₀
      exact ⟨_, i, rfl, GroupNumP.subst (GroupNumP.rollrt (h rt (by simp)) _) _⟩

theorem sub_num_inv {t : NumType} {p : CValType} (h : Sub {} (.num t) p) : p = .num t := by
  cases h
  rfl

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => by simp at hb
  | a :: _, _ :: _, .cons h t, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, by simp, h⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_mem_right t b hb
      exact ⟨a', by simp [ha'], h'⟩

/-- **A store function matching an import with numeric parameters takes integer
parameters.** -/
theorem numParams_externAddr {s : Store H} (hs : StoreOk s) {a : Nat} {d : DefType}
    (h : ExternAddrOk s (.func a) (.func d)) (hd : NumParams d) : NumParamsAt s.funcs a := by
  intro fi hfi
  obtain ⟨xt', e, hsub, hok⟩ := ExternAddrOk.principal hs h
  simp only [externAddrType?, hfi, Option.map_some, Option.some.injEq] at e
  subst e
  cases hsub with
  | func hsd =>
    cases hok with
    | func hdok hexp =>
      have hfok : TyOk {} fi.type := by
        cases hs.funcs fi (List.mem_of_getElem? hfi) <;> assumption
      obtain ⟨ps', rs', he', hps⟩ := Sub.defHeap_func_list (.defDef hsd) hfok hdok hexp
      intro qs ss hq p hp
      have := Silmaril.Wasm.SingleThreaded.Det.Expand.det hq he'
      injection this with h1 h2
      subst h1
      obtain ⟨q, hq', hsq⟩ := forall₂_mem_right hps p hp
      obtain ⟨t, rfl⟩ := hd _ _ hexp q hq'
      exact ⟨t, sub_num_inv hsq⟩

end Silmaril.Wasm.Binaryen.RUMESim
