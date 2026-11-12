module

public import Silmaril.Wasm.Auto.ESeg.Defs
public import Silmaril.Proofs.Wasm.Auto.ESeg.Select
public import Silmaril.Proofs.Wasm.Auto.ESeg.Logic

/-! # From exec-level equivalence to the every-run logic, with `select` and traps

* `wp_iff_of_outEq`: two typed bodies whose `execS` results agree up to the locals, run in
  frames of the same module, have the same every-run weakest precondition for every
  postcondition blind to the locals. A trap is allowed: `xexec` shows that both sides then trap
  (typed code is never stuck), in the same store and module, and the weakest precondition is
  the trap postcondition at the trap (`wp_xexec_trap_iff`);
* **`outEquivSel_of_bodyEquivSel`**: `BodyEquivSel Γ a b` gives `Equiv.OutEquiv Γ [] a b` for typed
  bodies, trapping or not; `outEquiv_of_bodyEquiv_typed` does the same for the `select`-free
  `Silmaril.Wasm.Auto.ESeg.BodyEquiv`;
* **`equivSeg_of_segEquivSel`**: `SegEquivSel Γ a b` gives `Equiv.SegEquiv Γ [] a b` for typed
  segments without division;
* **`funcOutEquiv_of_funcEquiv`**: `FuncEquiv Γ da db a b` gives `FuncOutEquiv Γ da db a b` for
  typed bodies.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.ESeg

open Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Auto

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post exec localVal?)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.ESeg Silmaril.Wasm.Auto.XExec Silmaril.Wasm.Auto.ESeg

variable {H : Type} {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}

theorem localsOk_of_frameOk {Γ : List IntType} {f : Frame} (hl : Γ.length < 2 ^ 32)
    (hf : FrameOk Γ f) : LocalsOk Γ f := by
  refine ⟨len_le_of_frameOk hl hf, fun i t hi => ?_⟩
  have hi' : i < Γ.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨x, hx⟩ := hf i t hi
  have hx' : localVal? f (lidx i) = some (intVal t x) := hx
  simp only [localVal?, Frame.local?, lidx_toNat (by omega : i < 2 ^ 32)] at hx'
  split at hx'
  · rename_i v hv
    cases hx'
    exact ⟨x, hv⟩
  · cases hx'

theorem typedBody_spec {Γ : List IntType} {a : List Instr} (h : typedBody Γ a = true) :
    Γ.length < 2 ^ 32 ∧ ∃ st, tsteps Γ [] a = some st := by
  simp only [typedBody, Bool.and_eq_true, localsOk, decide_eq_true_eq,
    Option.isSome_iff_exists] at h
  exact h

/-- The every-run weakest precondition of a typed body: its end or its trap. -/
theorem wp_typed {Γ : List IntType} {a : List Instr} {s : Store H} {f : Frame} {us : List Val}
    {st : List IntType} (ht : tsteps Γ [] a = some st) (hf : LocalsOk Γ f) :
    (∃ f' rs', execS s f us.reverse a = some (s, f', rs') ∧ f'.module = f.module ∧
        (Wp m P host s f (vals us ++ expression a ++ []) Q ↔ Q s f' (.normal rs'.reverse))) ∨
      (∃ f', execS s f us.reverse a = none ∧ f'.module = f.module ∧
        (Wp m P host s f (vals us ++ expression a ++ []) Q ↔ Q s f' .trap)) := by
  rcases xexec_typed (s := s) (rs := us.reverse) ht hf trivial with ⟨f', rs', he, hm⟩ |
    ⟨f', he, hm⟩
  · refine .inl ⟨f', rs', xexec_ok_iff.mp he, hm, ?_⟩
    rw [wp_xexec_ok_iff he, List.append_nil, wp_vals_iff]
  · refine .inr ⟨f', execS_none_iff.mpr (fun s' f'' rs' h => by rw [he] at h; cases h), hm, ?_⟩
    exact wp_xexec_trap_iff he

/-- **Typed bodies with the same `execS` results up to the locals** have the same every-run
weakest precondition for every postcondition blind to the locals. -/
theorem wp_iff_of_outEq {Γa Γb : List IntType} {a b : List Instr} {s : Store H} {fa fb : Frame}
    {us : List Val} {sta stb : List IntType} (hta : tsteps Γa [] a = some sta)
    (htb : tsteps Γb [] b = some stb) (hfa : LocalsOk Γa fa) (hfb : LocalsOk Γb fb)
    (hmod : fa.module = fb.module) (h : OutEq (execS s fa us.reverse a) (execS s fb us.reverse b))
    (hQ : Silmaril.Wasm.Auto.Equiv.LocalsBlind Q) :
    Wp m P host s fa (vals us ++ expression a ++ []) Q ↔
      Wp m P host s fb (vals us ++ expression b ++ []) Q := by
  rcases wp_typed (m := m) (P := P) (host := host) (Q := Q) (us := us) hta hfa with
    ⟨fa', ra, hea, hma, hwa⟩ | ⟨fa', hea, hma, hwa⟩ <;>
  rcases wp_typed (m := m) (P := P) (host := host) (Q := Q) (us := us) htb hfb with
    ⟨fb', rb, heb, hmb, hwb⟩ | ⟨fb', heb, hmb, hwb⟩ <;>
  rw [hea, heb] at h
  · obtain ⟨-, -, rfl⟩ := h
    rw [hwa, hwb]
    exact hQ s fa' fb' _ (by rw [hma, hmb, hmod])
  · exact h.elim
  · exact h.elim
  · rw [hwa, hwb]
    exact hQ s fa' fb' _ (by rw [hma, hmb, hmod])

/-! ## The bridges -/

/-- **Bodies with `select`, traps included, in the every-run logic.** -/
theorem outEquivSel_of_bodyEquivSel {Γ : List IntType} {a b : List Instr} (h : BodyEquivSel Γ a b)
    (ha : typedBody Γ a = true) (hb : typedBody Γ b = true) :
    Silmaril.Wasm.Auto.Equiv.OutEquiv Γ [] a b := by
  intro m P H host s f ρ us Q hQ
  obtain ⟨hl, sta, hta⟩ := typedBody_spec ha
  obtain ⟨-, stb, htb⟩ := typedBody_spec hb
  have hf := frameOk_frameAt hl f ρ
  have hlo := localsOk_of_frameOk hl hf
  rw [codeAt_init, codeAt_init]
  exact wp_iff_of_outEq hta htb hlo hlo rfl (h s _ us.reverse hf) hQ

/-- Without `select`, `BodyEquiv` is `BodyEquivSel`. -/
theorem bodyEquivSel_of_bodyEquiv {Γ : List IntType} {a b : List Instr} (h : BodyEquiv Γ a b)
    (ha : noSelect a = true) (hb : noSelect b = true) : BodyEquivSel Γ a b := by
  intro H s f rs hf
  rw [execS_eq_exec s f rs ha, execS_eq_exec s f rs hb]
  exact h s f rs hf

/-- **`select`-free bodies, traps included, in the every-run logic.** -/
theorem outEquiv_of_bodyEquiv_typed {Γ : List IntType} {a b : List Instr} (h : BodyEquiv Γ a b)
    (ha : noSelect a && typedBody Γ a = true) (hb : noSelect b && typedBody Γ b = true) :
    Silmaril.Wasm.Auto.Equiv.OutEquiv Γ [] a b := by
  simp only [Bool.and_eq_true] at ha hb
  exact outEquivSel_of_bodyEquivSel (bodyEquivSel_of_bodyEquiv h ha.1 hb.1) ha.2 hb.2

theorem noDiv_spec : ∀ {a : List Instr}, noDiv a = true →
    (∀ t d, .intBinOp t (.div d) ∉ a) ∧ (∀ t d, .intBinOp t (.rem d) ∉ a)
  | [], _ => ⟨by simp, by simp⟩
  | i :: is, h => by
    have k : noDiv is = true ∧ (∀ t d, i ≠ .intBinOp t (.div d)) ∧
        (∀ t d, i ≠ .intBinOp t (.rem d)) := by
      cases i
      case intBinOp t op => cases op <;> simp_all [noDiv]
      all_goals simp_all [noDiv]
    obtain ⟨hk, hd, hr⟩ := k
    obtain ⟨ihd, ihr⟩ := noDiv_spec hk
    exact ⟨fun t d hm => (List.mem_cons.mp hm).elim (fun he => hd t d he.symm) (ihd t d),
      fun t d hm => (List.mem_cons.mp hm).elim (fun he => hr t d he.symm) (ihr t d)⟩

/-- **Segments with `select`, without division, in the every-run logic.** -/
theorem equivSeg_of_segEquivSel {Γ : List IntType} {a b : List Instr} (h : SegEquivSel Γ a b)
    (ha : typedBody Γ a && noDiv a = true) : Silmaril.Wasm.Auto.Equiv.SegEquiv Γ [] a b := by
  intro m P H host s f ρ us rest Q
  simp only [Bool.and_eq_true] at ha
  obtain ⟨hl, sta, hta⟩ := typedBody_spec ha.1
  obtain ⟨hd, hr⟩ := noDiv_spec ha.2
  have hf := frameOk_frameAt hl f ρ
  obtain ⟨f', rs', hea, -⟩ := xexec_typed_noTrap (s := s) (rs := us.reverse) hta
    (localsOk_of_frameOk hl hf) trivial hd hr
  have heb : xexec s (Silmaril.Wasm.Auto.Equiv.frameAt f ρ (Silmaril.Wasm.Auto.Equiv.initState Γ []))
      us.reverse b = .ok s f' rs' :=
    xexec_ok_iff.mpr (by rw [← h s _ us.reverse hf]; exact xexec_ok_iff.mp hea)
  rw [codeAt_init, codeAt_init, wp_xexec_ok_iff hea, wp_xexec_ok_iff heb]

/-- **Function bodies with different declared locals in the every-run logic**, traps
included. -/
theorem funcOutEquiv_of_funcEquiv {Γ da db : List IntType} {a b : List Instr}
    (h : FuncEquiv Γ da db a b) (ha : typedBody (Γ ++ da) a = true)
    (hb : typedBody (Γ ++ db) b = true) : FuncOutEquiv Γ da db a b := by
  intro m P H host s fa fb Q hfa hfb hp hmod hQ
  obtain ⟨hla, sta, hta⟩ := typedBody_spec ha
  obtain ⟨hlb, stb, htb⟩ := typedBody_spec hb
  have k := wp_iff_of_outEq (m := m) (P := P) (host := host) (us := []) hta htb
    (localsOk_of_frameOk hla hfa.1) (localsOk_of_frameOk hlb hfb.1) hmod
    (h s fa fb [] hfa hfb hp hmod) hQ
  simpa using k

end Silmaril.Proofs.Wasm.Auto.ESeg
