module

public import Silmaril.Machine.Abi.Defs
/-! # Calling-convention comorphisms: satisfaction, agreement and thunks

`Convention.coHom_sat` is the institution-comorphism satisfaction condition of
an ABI, read in the Goguen–Roşu form. `Convention.Thunk.sound` transfers a
callee proof across a correct adapter, and `Convention.Agree.sat_iff` says that
two agreeing conventions impose the same machine obligation.
-/

@[expose] public section
namespace Silmaril.Machine.Abi

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Bridges

namespace Convention

variable {V : Vocab} {St D : Type}

/-- The institution-level satisfaction condition of the ABI comorphism: a machine
interface model satisfies the translated C sentence iff its reduct satisfies it. -/
theorem coHom_sat (A : Convention V St D) (iface : Iface V.Proto)
    (model : (machineLogic St D).Model (iface.map A.desc))
    (sentence : V.logic.Sentence iface) :
    Logic.Sat model ((A.translation.corridor iface).sen sentence) ↔
      Logic.Sat ((A.translation.corridor iface).mod.obj (Discrete.mk model)).as sentence :=
  Inst.CoHom.satisfaction A.coHom iface (Discrete.mk model) sentence

/-- Per symbol, the comorphism's satisfaction condition is the ABI correctness
statement `sat_translate`. -/
theorem coHom_sat_iff (A : Convention V St D) (iface : Iface V.Proto)
    (model : (machineLogic St D).Model (iface.map A.desc))
    (sentence : V.logic.Sentence iface) :
    Logic.Sat model ((A.translation.corridor iface).sen sentence) ↔
      Contracts.Sat (A.reduce sentence.desc
        (model sentence.sym (A.desc sentence.desc) (Iface.map_decl sentence.declared)))
        sentence.contract :=
  A.sat_translate _ _ _

/-- A thunk proof: a callee meeting `B`'s machine contract, reached through a
correct `A`-to-`B` thunk, meets `A`'s machine contract for the same C contract. -/
theorem Thunk.sound {A B : Convention V St D} {p : V.Proto} {t : Thunk A B p}
    (correct : t.Correct) {model : Contracts.Model St St}
    {c : Contracts.Contract (V.Args p) (Option (V.Ret p))}
    (callee : Contracts.Sat model (B.translate p c)) :
    Contracts.Sat (t.wrap model) (A.translate p c) := by
  rintro s ⟨a, entry, pre⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨s₁, entered⟩ := correct.enter_progress a s entry
    obtain ⟨s₂, ran⟩ := (callee s₁ ⟨a, correct.enter_entry a s entry s₁ entered, pre⟩).1
    obtain ⟨s₃, left⟩ := correct.leave_progress a s entry s₂
    exact ⟨s₃, s₁, entered, s₂, ran, left⟩
  · rintro s₃ ⟨s₁, entered, s₂, ran, left⟩ a' entry' pre' o observed
    have entry₁ := correct.enter_entry a' s entry' s₁ entered
    exact (callee s₁ ⟨a', entry₁, pre'⟩).2 s₂ ran a' entry₁ pre' o
      (correct.observe a' s entry' s₁ entered s₂ s₃ left o observed)

/-- The same transfer, read through both satisfaction conditions at C level. -/
theorem Thunk.sound_reduce {A B : Convention V St D} {p : V.Proto} {t : Thunk A B p}
    (correct : t.Correct) {model : Contracts.Model St St}
    {c : Contracts.Contract (V.Args p) (Option (V.Ret p))}
    (callee : Contracts.Sat (B.reduce p model) c) :
    Contracts.Sat (A.reduce p (t.wrap model)) c :=
  (A.sat_translate p _ c).1 (Thunk.sound correct ((B.sat_translate p model c).2 callee))

/-- Agreeing conventions translate every C contract to the same machine contract. -/
theorem Agree.translate_eq {A B : Convention V St D} {p : V.Proto} (agree : A.Agree B p)
    (c : Contracts.Contract (V.Args p) (Option (V.Ret p))) :
    A.translate p c = B.translate p c := by
  obtain ⟨entry, observe⟩ := agree
  apply Contracts.Contract.ext
  · funext s
    simp only [translate, entry]
  · funext s s'
    simp only [translate, entry, observe]

/-- Agreeing conventions read machine relations back identically. -/
theorem Agree.reduce_eq {A B : Convention V St D} {p : V.Proto} (agree : A.Agree B p)
    (model : Contracts.Model St St) : A.reduce p model = B.reduce p model := by
  obtain ⟨entry, observe⟩ := agree
  funext a
  ext o
  simp only [reduce, Set.mem_ofPred_eq, entry, observe]

/-- Cross-ABI linking without a thunk: under agreement, a callee verified for one
convention satisfies the other convention's contract. -/
theorem Agree.sat_iff {A B : Convention V St D} {p : V.Proto} (agree : A.Agree B p)
    (model : Contracts.Model St St) (c : Contracts.Contract (V.Args p) (Option (V.Ret p))) :
    Contracts.Sat model (A.translate p c) ↔ Contracts.Sat model (B.translate p c) := by
  rw [agree.translate_eq c]

theorem Agree.symm {A B : Convention V St D} {p : V.Proto} (agree : A.Agree B p) :
    B.Agree A p :=
  ⟨fun a s => (agree.1 a s).symm, fun s s' o => (agree.2 s s' o).symm⟩

theorem Agree.trans {A B C : Convention V St D} {p : V.Proto} (first : A.Agree B p)
    (second : B.Agree C p) : A.Agree C p :=
  ⟨fun a s => (first.1 a s).trans (second.1 a s),
    fun s s' o => (first.2 s s' o).trans (second.2 s s' o)⟩

/-- The empty thunk: jump straight to the callee. -/
def Thunk.direct (A B : Convention V St D) (p : V.Proto) : Thunk A B p where
  enter s := {s}
  leave _ s₂ := {s₂}

theorem Thunk.direct_wrap (A B : Convention V St D) (p : V.Proto)
    (model : Contracts.Model St St) : (Thunk.direct A B p).wrap model = model := by
  funext s
  ext s₃
  simp [Thunk.wrap, Thunk.direct]

/-- The empty thunk is correct when the conventions agree. (Only this direction is
proved; correctness of the empty thunk is weaker than `Agree`, since it is one-way
and only constrains `A`-entry states.) -/
theorem Agree.direct_correct {A B : Convention V St D} {p : V.Proto} (agree : A.Agree B p) :
    (Thunk.direct A B p).Correct where
  enter_entry a s entry s₁ entered := by
    simp only [Thunk.direct, Set.mem_singleton_iff] at entered
    exact entered ▸ (agree.1 a s).1 entry
  enter_progress _ s _ := ⟨s, rfl⟩
  leave_progress _ _ _ s₂ := ⟨s₂, rfl⟩
  observe a s entry s₁ entered s₂ s₃ left o observed := by
    simp only [Thunk.direct, Set.mem_singleton_iff] at entered left
    subst entered left
    exact (agree.2 _ _ o).1 observed

end Convention

end Silmaril.Machine.Abi
