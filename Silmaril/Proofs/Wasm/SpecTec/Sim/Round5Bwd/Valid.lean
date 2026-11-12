module

public import Silmaril.Wasm.SpecTec.Sim.Round5Bwd.Defs

/-!
# Round 5: `ConfigOk` gives reference liveness

`readValidR_of_configOk`: Core validity gives `ReadValidR`. Liveness comes from `RefOk` (a typed
`REF.ARRAY_ADDR a` has `s.arrays[a]?`), at every depth of the code, by recursion on Core's
`AdminsOk`/`AdminOk` derivation; the rest is `Round4Int.readValid_of_configOk`.
`readValidR_ctxClosed`: `ReadValidR` survives the context decompositions of the backward
recursion.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Bwd

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round4Read (ReadValid CtxClosed)

variable {H : Type} {s : Store H}

/-- **A typed reference is live.** -/
theorem refLive_of_refOk {r : Ref} {rt : CRefType} (h : RefOk s r rt) : refLive s r := by
  induction h with
  | struct h => simp [refLive, h]
  | array h => simp [refLive, h]
  | func h => simp [refLive, h]
  | exn h => simp [refLive, h]
  | extern _ _ ih => exact ih
  | sub _ _ _ ih => exact ih
  | _ => trivial

/-- `codeLive` along an append. -/
theorem codeLive_append : ∀ {l₁ l₂ : List Admin},
    codeLive s (l₁ ++ l₂) ↔ codeLive s l₁ ∧ codeLive s l₂
  | [], _ => by simp [codeLive]
  | _ :: _, _ => by simp [codeLive, codeLive_append, and_assoc]

mutual
/-- **Every reference of a valid administrative instruction is live**, at every depth. -/
theorem adminLive_of_ok : ∀ {C : Context} {a : Admin} {it : InstrType},
    AdminOk s C a it → adminLive s a
  | _, _, _, .plain _ => by simp [adminLive]
  | _, _, _, .callRefType _ _ => by simp [adminLive]
  | _, _, _, .returnCallRefType _ _ _ _ _ => by simp [adminLive]
  | _, _, _, .ref h => refLive_of_refOk h
  | _, _, _, .label _ _ hb => codeLive_of_ok hb
  | _, _, _, .frame _ _ hb _ => codeLive_of_ok hb
  | _, _, _, .handler _ hb => codeLive_of_ok hb
  | _, _, _, .trap _ => by simp [adminLive]
  | _, _, _, .throwRefInits _ => by simp [adminLive]

/-- **Every reference of valid code is live**, at every depth. -/
theorem codeLive_of_ok : ∀ {C : Context} {l : List Admin} {it : InstrType},
    AdminsOk s C l it → codeLive s l
  | _, _, _, .nil => trivial
  | _, _, _, .single h => ⟨adminLive_of_ok h, trivial⟩
  | _, _, _, .seq h₁ _ h₂ => codeLive_append.2 ⟨codeLive_of_ok h₁, codeLive_of_ok h₂⟩
  | _, _, _, .cons ha _ hs => ⟨adminLive_of_ok ha, codeLive_of_ok hs⟩
  | _, _, _, .sub h _ _ => codeLive_of_ok h
  | _, _, _, .frame h _ => codeLive_of_ok h
end

/-- **Core validity and the store bounds give `ReadValidR`.** -/
theorem readValidR_of_configOk {c : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hs : Integrate.StoreOk c.store) : ReadValidR c := by
  have hr := Round4Int.readValid_of_configOk hc hs
  obtain ⟨C, -, hcode⟩ := hc
  exact ⟨hr, codeLive_of_ok hcode⟩

/-- **A valid, bounded configuration satisfies `ReadValidR`.** -/
theorem readValidR_of_bounded {c : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hb : Round4.Bounded c) : ReadValidR c :=
  readValidR_of_configOk hc hb.store

/-- **`ReadValidR` survives the context decompositions** of the backward recursion. -/
theorem readValidR_ctxClosed : CtxClosed (ReadValidR (H := H)) where
  mid s f a b c h := ⟨Round4Read.readValid_ctxClosed.mid s f a b c h.read,
    (codeLive_append.1 (codeLive_append.1 h.live).1).2⟩
  label s f n cont body h := ⟨Round4Read.readValid_ctxClosed.label s f n cont body h.read, h.live.1⟩
  handler s f n cs body h := ⟨Round4Read.readValid_ctxClosed.handler s f n cs body h.read, h.live.1⟩
  frame s f fi n body h := ⟨Round4Read.readValid_ctxClosed.frame s f fi n body h.read, h.live.1⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Bwd
