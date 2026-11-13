module

public import Silmaril.Wasm.Execution.Runtime

@[expose] public section

/-! # Store extension and host contracts

Store extension preserves allocated addresses and immutable contents; it is
separate from store validity. `HostContract` states the required nonempty
outcome set, result typing, and preservation of an explicit store invariant.
It does not supply a complete store-typing judgment or a type-safety theorem.

See the [Wasm 1.0 runtime properties](https://github.com/WebAssembly/spec/blob/977f97014c962f7bd1291fcc6d28b41a924882bf/document/core/appendix/properties.rst).
-/

namespace Silmaril.Wasm.Execution.Runtime

/-- Existing addresses persist, with their contents related pointwise. -/
structure ExtendsList {α : Type*} (R : α → α → Prop) (before after : List α) : Prop where
  length : before.length ≤ after.length
  entry : ∀ (i : Nat) (x : α), before[i]? = some x → ∃ y, after[i]? = some y ∧ R x y

theorem ExtendsList.refl {α : Type*} {R : α → α → Prop}
    (hr : ∀ a, R a a) (xs : List α) : ExtendsList R xs xs :=
  ⟨Nat.le_refl _, fun _ x h => ⟨x, h, hr x⟩⟩

theorem ExtendsList.trans {α : Type*} {R : α → α → Prop}
    (ht : ∀ a b c, R a b → R b c → R a c) {a b c : List α}
    (h : ExtendsList R a b) (h' : ExtendsList R b c) : ExtendsList R a c where
  length := h.length.trans h'.length
  entry i x hx := by
    obtain ⟨y, hy, hxy⟩ := h.entry i x hx
    obtain ⟨z, hz, hyz⟩ := h'.entry i y hy
    exact ⟨z, hz, ht x y z hxy hyz⟩

def TableExtends (a b : TableInst) : Prop := a.max = b.max ∧ a.refs.length ≤ b.refs.length

def MemoryExtends (a b : MemInst) : Prop := a.max = b.max ∧ a.data.size ≤ b.data.size

def GlobalExtends (a b : GlobalInst) : Prop :=
  a.mutability = b.mutability ∧ a.value.type = b.value.type ∧
    (a.mutability = .const → a.value = b.value)

theorem GlobalExtends.refl (a : GlobalInst) : GlobalExtends a a := ⟨rfl, rfl, fun _ => rfl⟩

theorem GlobalExtends.trans {a b c : GlobalInst} (h : GlobalExtends a b)
    (h' : GlobalExtends b c) : GlobalExtends a c := by
  refine ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, fun hc => ?_⟩
  exact (h.2.2 hc).trans (h'.2.2 (h.1.symm.trans hc))

structure StoreExtends {Code H : Type*} (a b : Store Code H) : Prop where
  funcs : ExtendsList Eq a.funcs b.funcs
  tables : ExtendsList TableExtends a.tables b.tables
  memories : ExtendsList MemoryExtends a.memories b.memories
  globals : ExtendsList GlobalExtends a.globals b.globals

theorem StoreExtends.refl {Code H : Type*} (s : Store Code H) : StoreExtends s s where
  funcs := ExtendsList.refl (fun _ => rfl) _
  tables := ExtendsList.refl (fun _ => ⟨rfl, Nat.le_refl _⟩) _
  memories := ExtendsList.refl (fun _ => ⟨rfl, Nat.le_refl _⟩) _
  globals := ExtendsList.refl GlobalExtends.refl _

theorem StoreExtends.trans {Code H : Type*} {a b c : Store Code H}
    (h : StoreExtends a b) (h' : StoreExtends b c) : StoreExtends a c where
  funcs := ExtendsList.trans (R := Eq) (fun _ _ _ hab hbc => hab.trans hbc) h.funcs h'.funcs
  tables := h.tables.trans (fun _ _ _ ⟨hm, hl⟩ ⟨hm', hl'⟩ => ⟨hm.trans hm', hl.trans hl'⟩) h'.tables
  memories := h.memories.trans
    (fun _ _ _ ⟨hm, hl⟩ ⟨hm', hl'⟩ => ⟨hm.trans hm', hl.trans hl'⟩) h'.memories
  globals := ExtendsList.trans (R := GlobalExtends)
    (fun _ _ _ hab hbc => GlobalExtends.trans hab hbc) h.globals h'.globals

def ResultHasTypes : Result → List NumType → Prop
  | .values vs, ts => vs.map Value.type = ts
  | .trap, _ => True

/-- A host implementation must provide an outcome on valid, correctly typed calls.
Returned stores must remain valid and extend the original, even when trapping. -/
def HostContract {Code H : Type*} (ValidStore : Store Code H → Prop)
    (host : HostSemantics Code H) : Prop :=
  ∀ s, ValidStore s → ∀ (address : Nat) (ft : V1.FuncType) (code : H) (args : List Value),
    s.funcs[address]? = some (.host ft code) → args.map Value.type = ft.params →
      (∃ outcome, host code s args outcome) ∧
      ∀ outcome, host code s args outcome →
        match outcome with
        | .diverged => True
        | .returned s' result => ValidStore s' ∧ StoreExtends s s' ∧ ResultHasTypes result ft.results

theorem HostContract.returned {Code H : Type*} {ValidStore : Store Code H → Prop}
    {host : HostSemantics Code H} (contract : HostContract ValidStore host)
    {s s' : Store Code H} (valid : ValidStore s) {a : Nat} {ft : V1.FuncType}
    {code : H} {args : List Value} {result : Result}
    (registered : s.funcs[a]? = some (.host ft code)) (typed : args.map Value.type = ft.params)
    (behavior : host code s args (.returned s' result)) :
    ValidStore s' ∧ StoreExtends s s' ∧ ResultHasTypes result ft.results :=
  (contract s valid a ft code args registered typed).2 _ behavior

end Silmaril.Wasm.Execution.Runtime
