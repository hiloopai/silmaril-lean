module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Basic
public import Silmaril.Wasi.Versions.P3.Wit.Thms

/-!
# Proofs: WASI 0.3 over 0.2 answers well typed

`wp_typed`: every answer of `body` has its WIT type (`ok3`), whatever the 0.2 host answers;
`typed_sat`: the component satisfies `agP T (retG typed3)` for every theory `T` of the 0.2 host.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3

variable {ST : Type}

/-- The class of an export call, with its name. -/
theorem cls_cases {f : FnName} (hf : f ∈ p3World.imports) :
    ∃ c, cls f = c ∧ c ≠ .other ∧ f = c.name := by
  have h := cls_mem (cls_ne_other hf)
  refine ⟨cls f, rfl, cls_ne_other hf, ?_⟩
  revert h
  generalize cls f = c
  intro h
  simp only [fnTable, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- `get-directories` answers are well typed. -/
theorem encDirs_ok (a : List Val) (r : Option (List Val)) :
    ok3 (.imp getDirs3 a (encDirs r)) = true := by
  rw [ok3_eq_hand]
  unfold encDirs
  split
  · split
    · rename_i h; exact h
    · rfl
  · rfl

/-- `open-at` answers are well typed. -/
theorem encOpen_ok (a : List Val) (r : Option (List Val)) :
    ok3 (.imp openAt3 a (encOpen r)) = true := by
  rw [ok3_eq_hand]
  unfold encOpen
  split <;> rfl

/-- `future.read` answers are well typed. -/
theorem fans_ok (a : List Val) (x : FAns) : ok3 (.imp cFutureRead a x.enc) = true := by
  rw [ok3_eq_hand]
  cases x <;> rfl

/-- **Every answer of the component is well typed**, under any theory of the 0.2 host. -/
theorem wp_typed (T : Protocol ST WEv) (s : St) (q : (nsig p3World.imports).Op) (qT : ST) :
    Wp T (body s q) (fun a _ => ok3 (.imp q.1.1 q.2 a.2) = true) qT := by
  obtain ⟨⟨f, hf⟩, a⟩ := q
  obtain ⟨c, hc, hne, rfl⟩ := cls_cases hf
  cases c <;> simp only [body, hc, thenFin] <;>
    first
    | exact absurd rfl hne
    | rfl
    | (refine wp_fin' T _ _ (fun d _ => ?_) qT
       first | rfl | exact fans_ok _ _ | exact encDirs_ok _ _ | exact encOpen_ok _ _)

/-- **The component's answers satisfy `typed3`**, for every theory of the 0.2 host. -/
theorem typed_sat (T : Protocol ST WEv) :
    (agP T (retG typed3)).holds p3OverP2 :=
  ag_of_wpInv (J := fun _ _ _ => True)
    ⟨trivial, fun s qT _ q _ => Wp.mono (fun a _ h => ⟨(), by simp [typed3, pointwise, h], trivial⟩)
      (wp_typed T s q qT)⟩

end Silmaril.Wasi.Versions.P3OverP2
