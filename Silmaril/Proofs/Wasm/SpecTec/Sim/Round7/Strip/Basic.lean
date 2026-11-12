module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs

/-!
# Round 7: configurations up to export lists, basic facts

* `stripAdmins_eq_map`, `stripAdmins_append`, `stripAdmins_vals`: stripping acts element-wise and
  leaves values alone.
* `Atomic`: an administrative instruction that is not a label, handler or frame; stripping leaves
  it alone (`stripAdmin_atomic`) and is injective at it (`stripAdmin_eq_atomic`).
* Inversion: a sequence whose strip is that of `l ++ r` with `l` atomic is `l ++ r'`
  (`stripAdmins_eq_atomic_append`); the strip of a label, handler or frame comes from one
  (`stripAdmin_eq_label`, …).
* `exRel_nf`: a configuration related to `⟨s, f, is⟩` has the store `s` with other function
  instances (equal up to exports), the frame `f` with other exports, and code equal to `is` up to
  exports.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## Stripping, element-wise -/

theorem stripAdmins_eq_map : ∀ l : List Admin, stripAdmins l = l.map stripAdmin
  | [] => rfl
  | a :: l => by simp [stripAdmins, stripAdmins_eq_map l]

@[simp] theorem stripAdmins_nil : stripAdmins [] = [] := rfl

@[simp] theorem stripAdmins_cons (a : Admin) (l : List Admin) :
    stripAdmins (a :: l) = stripAdmin a :: stripAdmins l := rfl

@[simp] theorem stripAdmins_append (l r : List Admin) :
    stripAdmins (l ++ r) = stripAdmins l ++ stripAdmins r := by
  simp [stripAdmins_eq_map]

/-- Not a label, handler or frame. -/
def Atomic : Admin → Prop
  | .label .. | .handler .. | .frame .. => False
  | _ => True

/-- Every element is `Atomic`. -/
def AllAtomic (l : List Admin) : Prop := ∀ a ∈ l, Atomic a

theorem stripAdmin_atomic {a : Admin} (h : Atomic a) : stripAdmin a = a := by
  cases a <;> simp_all [Atomic, stripAdmin]

theorem stripAdmin_eq_atomic {a b : Admin} (h : Atomic a) (hb : stripAdmin b = stripAdmin a) :
    b = a := by
  rw [stripAdmin_atomic h] at hb
  cases b <;> cases a <;> simp_all [Atomic, stripAdmin]

theorem atomic_toAdmin (v : Val) : Atomic v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Atomic]

theorem allAtomic_vals (vs : List Val) : AllAtomic (vals vs) := by
  intro a ha
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp ha
  exact atomic_toAdmin v

theorem allAtomic_nil : AllAtomic [] := fun _ h => absurd h (List.not_mem_nil)

theorem allAtomic_cons {a : Admin} {l : List Admin} (ha : Atomic a) (hl : AllAtomic l) :
    AllAtomic (a :: l) := fun b hb => by
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact hl b hb

theorem allAtomic_append {l r : List Admin} (hl : AllAtomic l) (hr : AllAtomic r) :
    AllAtomic (l ++ r) := fun b hb => by
  rcases List.mem_append.mp hb with hb | hb
  · exact hl b hb
  · exact hr b hb

theorem stripAdmins_atomic {l : List Admin} (h : AllAtomic l) : stripAdmins l = l := by
  rw [stripAdmins_eq_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun a ha => stripAdmin_atomic (h a ha)

@[simp] theorem stripAdmins_vals (vs : List Val) : stripAdmins (vals vs) = vals vs :=
  stripAdmins_atomic (allAtomic_vals vs)

/-! ## Inversion -/

theorem stripAdmins_eq_atomic_append :
    ∀ {l : List Admin} (r : List Admin) {js : List Admin}, AllAtomic l →
      stripAdmins js = stripAdmins (l ++ r) → ∃ r', js = l ++ r' ∧ stripAdmins r' = stripAdmins r
  | [], r, js, _, h => ⟨js, rfl, by simpa using h⟩
  | a :: l, r, [], _, h => by simp at h
  | a :: l, r, b :: js, hl, h => by
      have ha : Atomic a := hl a (List.mem_cons_self ..)
      have hl' : AllAtomic l := fun x hx => hl x (List.mem_cons_of_mem _ hx)
      simp only [List.cons_append, stripAdmins_cons, List.cons.injEq] at h
      obtain ⟨r', hr', hs⟩ := stripAdmins_eq_atomic_append r hl' h.2
      exact ⟨r', by rw [stripAdmin_eq_atomic ha h.1, hr']; rfl, hs⟩

theorem stripAdmins_eq_atomic {l js : List Admin} (hl : AllAtomic l)
    (h : stripAdmins js = stripAdmins l) : js = l := by
  obtain ⟨r', h₁, h₂⟩ := stripAdmins_eq_atomic_append [] hl (by simpa using h)
  cases r' with
  | nil => simpa using h₁
  | cons a r' => simp at h₂

theorem stripAdmin_eq_label {b : Admin} {n : Nat} {cont : List Instr} {body : List Admin}
    (h : stripAdmin b = stripAdmin (.label n cont body)) :
    ∃ body', b = .label n cont body' ∧ stripAdmins body' = stripAdmins body := by
  cases b <;> simp_all [stripAdmin]

theorem stripAdmin_eq_handler {b : Admin} {n : Nat} {cs : List Catch} {body : List Admin}
    (h : stripAdmin b = stripAdmin (.handler n cs body)) :
    ∃ body', b = .handler n cs body' ∧ stripAdmins body' = stripAdmins body := by
  cases b <;> simp_all [stripAdmin]

theorem stripAdmin_eq_frame {b : Admin} {n : Nat} {f : Frame} {body : List Admin}
    (h : stripAdmin b = stripAdmin (.frame n f body)) :
    ∃ f' body', b = .frame n f' body' ∧ stripFrame f' = stripFrame f ∧
      stripAdmins body' = stripAdmins body := by
  cases b <;> simp_all [stripAdmin]

theorem stripAdmins_eq_singleton {js : List Admin} {a : Admin}
    (h : stripAdmins js = stripAdmins [a]) : ∃ b, js = [b] ∧ stripAdmin b = stripAdmin a := by
  rcases js with _ | ⟨b, _ | ⟨c, js⟩⟩ <;> simp_all

/-! ## Stores and frames up to exports -/

theorem stripStore_eq (s : Store H) : stripStore s = { s with funcs := s.funcs.map stripFI } := rfl

theorem stripFrame_withEx (f : Frame) (E : List ExportInst) :
    stripFrame { f with module := { f.module with exports := E } } = stripFrame f := rfl

theorem stripStore_withFuncs (s : Store H) {F : List (FuncInst H)}
    (hF : F.map stripFI = s.funcs.map stripFI) :
    stripStore { s with funcs := F } = stripStore s := by
  simp only [stripStore_eq, hF]

/-- **The normal form of a store up to exports**: the same store with other function
instances. -/
theorem stripStore_nf {s s₂ : Store H} (h : stripStore s₂ = stripStore s) :
    s₂ = { s with funcs := s₂.funcs } ∧ s₂.funcs.map stripFI = s.funcs.map stripFI := by
  cases s; cases s₂
  simp only [stripStore_eq, Store.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  subst h1 h2 h3 h4 h6 h7 h8 h9 h10
  exact ⟨rfl, h5⟩

/-- The normal form of a frame up to exports. -/
theorem stripFrame_nf {f f₂ : Frame} (h : stripFrame f₂ = stripFrame f) :
    f₂ = { f with module := { f.module with exports := f₂.module.exports } } := by
  obtain ⟨l₂, ⟨t₂, g₂, gl₂, m₂, tb₂, fn₂, d₂, e₂, x₂⟩⟩ := f₂
  obtain ⟨l, ⟨t, g, gl, m, tb, fn, d, e, x⟩⟩ := f
  simp only [stripFrame, stripModule, Frame.mk.injEq, ModuleInst.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := h
  rfl

/-- **The normal form of a configuration up to exports.** -/
theorem exRel_nf {s : Store H} {f : Frame} {is : List Admin} {d : Config H}
    (h : ExRel ⟨s, f, is⟩ d) :
    ∃ F E js, d = ⟨{ s with funcs := F }, { f with module := { f.module with exports := E } }, js⟩ ∧
      F.map stripFI = s.funcs.map stripFI ∧ stripAdmins js = stripAdmins is := by
  obtain ⟨s₂, f₂, js⟩ := d
  simp only [ExRel, stripConfig, Config.mk.injEq] at h
  obtain ⟨hs, hf, hc⟩ := h
  obtain ⟨hs₁, hs₂⟩ := stripStore_nf hs.symm
  exact ⟨s₂.funcs, f₂.module.exports, js, by rw [← hs₁, ← stripFrame_nf hf.symm], hs₂, hc.symm⟩

/-- `ExRel` from its three components. -/
theorem exRel_mk {s s₂ : Store H} {f f₂ : Frame} {is js : List Admin}
    (hs : stripStore s = stripStore s₂) (hf : stripFrame f = stripFrame f₂)
    (hc : stripAdmins is = stripAdmins js) : ExRel ⟨s, f, is⟩ ⟨s₂, f₂, js⟩ := by
  simp only [ExRel, stripConfig, hs, hf, hc]

theorem exRel_symm {c d : Config H} (h : ExRel c d) : ExRel d c := Eq.symm h

theorem exRel_refl (c : Config H) : ExRel c c := rfl

end Silmaril.Wasm.SpecTec.Sim.Round7
