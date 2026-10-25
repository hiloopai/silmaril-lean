module

public import Silmaril.Wasm.Execution.Core.Instantiation
public import Silmaril.Wasm.Validation.Modules

@[expose] public section

/-! # Counting imports by kind

The extern addresses given to an instantiation have the kinds of the module's imports
(`ExternAddrOk` and `ImportOk` keep the kind), so the imported functions of a module number
`(ExternAddr.funcs xas).length` (`externAddr_funcs_length_eq`), and a module without table
imports receives no table addresses (`externAddr_tables_nil`). This generalises the global
count of `Pass/SimplifyGlobalsSim.lean` to every kind.
-/

namespace Silmaril.Wasm.Binaryen

namespace DirectizeCount

open Execution.Core Validation

variable {H : Type}

/-- The kind of an extern address. -/
def kXA : ExternAddr → Nat
  | .tag _ => 0 | .global _ => 1 | .mem _ => 2 | .table _ => 3 | .func _ => 4

/-- The kind of an extern type. -/
def kXT : CExternType → Nat
  | .tag _ => 0 | .global _ => 1 | .mem _ => 2 | .table _ => 3 | .func _ => 4

/-- The kind of an import. -/
def kIm (i : Import) : Nat :=
  match i.type with
  | .tag _ => 0 | .global _ => 1 | .memory _ => 2 | .table _ => 3 | .func _ => 4

theorem externAddrOk_k {s : Store H} {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) : kXA xa = kXT xt := by
  induction h with
  | sub _ _ hs ih => rw [ih]; cases hs <;> rfl
  | _ => rfl

theorem importOk_k {C : Context} {i : Import} {xt : CExternType} (h : ImportOk C i xt) :
    kIm i = kXT xt := by
  obtain ⟨h, -⟩ := h
  unfold kIm
  cases hty : i.type with
  | tag x =>
    rw [hty] at h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | global g => rw [hty] at h; cases h; rfl
  | memory mt => rw [hty] at h; cases h; rfl
  | table tt => rw [hty] at h; cases h; rfl
  | func x =>
    rw [hty] at h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl

theorem filter_length_forall₂ {α β : Type _} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hR : ∀ a b, R a b → p a = q b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → (l.filter p).length = (l'.filter q).length
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    rw [List.filter_cons, List.filter_cons, hR _ _ h]
    split <;> simp [filter_length_forall₂ hR t]

theorem externAddr_funcs_length : ∀ xas : List ExternAddr,
    (ExternAddr.funcs xas).length = (xas.filter (kXA · == 4)).length
  | [] => rfl
  | xa :: xas => by
    cases xa <;> simp [ExternAddr.funcs, kXA, externAddr_funcs_length xas]

theorem externAddr_tables_length : ∀ xas : List ExternAddr,
    (ExternAddr.tables xas).length = (xas.filter (kXA · == 3)).length
  | [] => rfl
  | xa :: xas => by
    cases xa <;> simp [ExternAddr.tables, kXA, externAddr_tables_length xas]

theorem importedFunctions_length : ∀ is : List Import,
    (is.filterMap fun i => match i.type with | .func t => some t | _ => none).length =
      (is.filter (kIm · == 4)).length
  | [] => rfl
  | i :: is => by
    rw [List.filterMap_cons, List.filter_cons]
    have ih := importedFunctions_length is
    cases h : i.type with
    | func t => have hk : kIm i = 4 := by simp [kIm, h]
                simp [hk, ih]
    | tag t => have hk : kIm i = 0 := by simp [kIm, h]
               simp [hk, ih]
    | global t => have hk : kIm i = 1 := by simp [kIm, h]
                  simp [hk, ih]
    | memory t => have hk : kIm i = 2 := by simp [kIm, h]
                  simp [hk, ih]
    | table t => have hk : kIm i = 3 := by simp [kIm, h]
                 simp [hk, ih]

/-- **The imported functions of a module number the function addresses imported.** -/
theorem externAddr_funcs_length_eq {s : Store H} {C : Context} {is : List Import}
    {xtI : List CExternType} {xas : List ExternAddr} (hI : List.Forall₂ (ImportOk C) is xtI)
    (hx : List.Forall₂ (ExternAddrOk s) xas xtI) :
    (ExternAddr.funcs xas).length =
      (is.filterMap fun i => match i.type with | .func t => some t | _ => none).length := by
  rw [externAddr_funcs_length, importedFunctions_length,
    filter_length_forall₂ (q := (kXT · == 4)) (fun _ _ h => by rw [externAddrOk_k h]) hx,
    filter_length_forall₂ (q := (kXT · == 4)) (fun _ _ h => by rw [importOk_k h]) hI]

/-- **A module without table imports receives no table addresses.** -/
theorem externAddr_tables_nil {s : Store H} {C : Context} {is : List Import}
    {xtI : List CExternType} {xas : List ExternAddr} (hI : List.Forall₂ (ImportOk C) is xtI)
    (hx : List.Forall₂ (ExternAddrOk s) xas xtI)
    (hno : is.all (fun i => match i.type with | .table _ => false | _ => true) = true) :
    ExternAddr.tables xas = [] := by
  have hz : (is.filter (kIm · == 3)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro i hi
    have := List.all_eq_true.mp hno i hi
    unfold kIm
    cases h : i.type <;> rw [h] at this <;> simp_all
  have := externAddr_tables_length xas
  rw [filter_length_forall₂ (q := (kXT · == 3)) (fun _ _ h => by rw [externAddrOk_k h]) hx,
    ← filter_length_forall₂ (p := (kIm · == 3)) (fun _ _ h => by rw [importOk_k h]) hI, hz] at this
  exact List.eq_nil_of_length_eq_zero this

end DirectizeCount

end Silmaril.Wasm.Binaryen
