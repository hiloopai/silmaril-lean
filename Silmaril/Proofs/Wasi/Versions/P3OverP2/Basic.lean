module

public import Silmaril.Wasi.Versions.P3OverP2.Impl.Defs
public import Silmaril.Wasi.Versions.Stateful.Thms

/-!
# Proofs: WASI 0.3 over 0.2, basic lemmas

Weakest preconditions of programs whose result does not depend on the theory (`wp_const`,
`wp_fin`), of embedded non-read programs under a theory that ignores them (`wp_emb`), the
classification of names (`cls_name`), and the decoding of handles and copy codes.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult blocked)
open Silmaril.Wasi.Versions.P3

variable {ST : Type} {I : Set FnName}

/-- A postcondition that holds of every result holds after every program. -/
theorem wp_const {A : Type} (T : Protocol ST WEv) {P : A → Prop} (hP : ∀ a, P a) :
    ∀ (p : Prog (nsig I) A) (qT : ST), Wp T p (fun a _ => P a) qT := fun p _ =>
  Wp.stable (R := fun _ => True) (fun _ _ _ _ _ => trivial) (fun a _ _ => hP a) p trivial

/-- A program followed by a pure finish: enough that the finish is good for every result. -/
theorem wp_fin {A B : Type} (T : Protocol ST WEv) {P : B → Prop} (p : Prog (nsig I) A)
    (g : A → B) (hP : ∀ a, P (g a)) (qT : ST) :
    Wp T (p.bind fun a => .pure (g a)) (fun b _ => P b) qT :=
  (Wp.bind _ p qT).2 (wp_const T hP p qT)

/-- A program followed by a pure finish, for a postcondition that may mention the state. -/
theorem wp_fin' {A B : Type} (T : Protocol ST WEv) {Q : B → ST → Prop} (p : Prog (nsig I) A)
    (g : A → B) (hQ : ∀ a q, Q (g a) q) (qT : ST) :
    Wp T (p.bind fun a => .pure (g a)) Q qT :=
  (Wp.bind _ p qT).2
    (Wp.stable (R := fun _ => True) (fun _ _ _ _ _ => trivial) (fun a q _ => hQ a q) p trivial)

/-- **Embedded non-read programs**: under a theory that accepts every non-read answer without
changing its state, the postcondition must hold of every result in the initial state. -/
theorem wp_emb {A : Type} (T : Protocol ST WEv)
    (hT : ∀ q f a n, f ∈ nrFns → T.step q (.imp f a n) = some q) {Q : A → ST → Prop} {qT : ST}
    (hQ : ∀ a, Q a qT) : ∀ p : NProg A, Wp T (emb p) Q qT
  | .pure a => hQ a
  | .call m k => fun n qT' hn => by
    have h := hT qT m.1.1 m.2 n m.1.2
    have hq : qT' = qT := Option.some.inj (hn.symm.trans h)
    subst hq
    exact wp_emb T hT hQ (k n)

/-- The name of a class. -/
def Fn3.name : Fn3 → FnName
  | .streamNew => cStreamNew | .streamWrite => cStreamWrite | .streamRead => cStreamRead
  | .dropR => cStreamDropR | .dropW => cStreamDropW | .futRead => cFutureRead
  | .futDropR => cFutureDropR | .wsNew => cWsNew | .join => cJoin | .wait => cWait
  | .wvs => stdoutWrite3 | .stdin => stdinRead3 | .now => now3 | .waitFor => waitFor3
  | .getDirs => getDirs3 | .openAt => openAt3 | .readVia => readVia3 | .other => ⟨"", ""⟩

/-- A classified name is in the table with its class. -/
theorem cls_mem {f : FnName} (h : cls f ≠ .other) : (cls f, f) ∈ fnTable := by
  unfold cls at h ⊢
  cases hf : fnTable.find? (·.2 = f) with
  | none => simp [hf] at h
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have h2 : e.2 = f := by simpa using List.find?_some hf
    simp only [Option.map_some, Option.getD_some]
    exact h2 ▸ he

/-- A function of the 0.3 slice is classified. -/
theorem cls_ne_other {f : FnName} (hf : f ∈ p3World.imports) : cls f ≠ .other := by
  simp only [p3World, wasiFns3_eq, canonFns, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hf
  rcases hf with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

/-- Handles below `2^32` decode. -/
theorem natOf_natV {x : Nat} (hx : x < 2 ^ 32) : natOf (natV x) = some x := by
  simp only [natOf, natV, BitVec.toNat_ofNat, Option.some.injEq]
  exact Nat.mod_eq_of_lt hx

/-- A completed copy of at most `cap` items decodes. -/
theorem copyOf_completed {k : Nat} (hk : k ≤ cap) :
    copyOf (packCopy .completed k) = some (some (.completed, k)) := by
  have hb : packCopy .completed k ≠ blocked := by
    simp only [packCopy, CopyResult.toNat, blocked, cap] at hk ⊢; omega
  have h1 : packCopy .completed k % 16 = 0 := by simp only [packCopy, CopyResult.toNat]; omega
  have h2 : packCopy .completed k / 16 = k := by simp only [packCopy, CopyResult.toNat]; omega
  simp only [copyOf, hb, h1, h2, ↓reduceIte]

/-- `DROPPED 0` decodes. -/
theorem copyOf_dropped : copyOf (packCopy .dropped 0) = some (some (.dropped, 0)) := by decide

/-- `BLOCKED` decodes. -/
theorem copyOf_blocked : copyOf blocked = some none := by decide

/-- A completed copy of at most `cap` items is below `2^32`. -/
theorem pack_lt {k : Nat} (hk : k ≤ cap) : packCopy .completed k < 2 ^ 32 := by
  simp only [packCopy, CopyResult.toNat, cap] at hk ⊢; omega

/-- The code of a `stream.write` decodes to an admissible copy result. -/
theorem wcode_ok (len n : Nat) :
    ∃ c, natOf (natV (wcode len n)) >>= copyOf = some c ∧ copyOk len c = true := by
  unfold wcode
  split
  · rename_i h
    simp only [codeOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlt, hc⟩ := h
    revert hc
    cases hco : copyOf n with
    | none => simp
    | some c => exact fun hc => ⟨c, by simp [natOf_natV hlt, hco], hc⟩
  · exact ⟨none, by simp [natOf_natV (by decide : blocked < 2 ^ 32), copyOf_blocked], rfl⟩

end Silmaril.Wasi.Versions.P3OverP2
