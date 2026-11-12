module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Table
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.MemoryFwd

/-!
# Track bwd-read: `Step_read/memory.fill-oob` (53), backward

`mem_inv` and `memLen_inv` read `$mem(z, x)` and `|$mem(z, x).BYTES|` back into Core's
`Store.mem?`; `bwd_memoryFillOob` is the `Backward.read 53` field.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_memoryFill {a : Admin} (h : Typing.adminHead a = "MEMORY.FILL") :
    ∃ x, a = .plain (.memoryFill x) := by
  revert h
  admin_head_inv

theorem decode_memoryFill {a : Admin} {X : Value} (h : adminToV a = .case "MEMORY.FILL" X) :
    ∃ x : MemIdx, a = .plain (.memoryFill x) ∧ X = idxV x.toNat := by
  obtain ⟨x, rfl⟩ := head_memoryFill (Typing.adminToV_case h).symm
  refine ⟨x, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

variable (B : Builtins) (NA : NoAcc B) {ρ : VarEnv} {s : Store H} {f : Frame}
include NA

/-- **`$mem(z, x)` on an encoded state, read back.** -/
theorem mem_inv {zx : IL.Id} {x : MemIdx} {Mv : Value} (hρ : ρ.findDef? "mem" = none)
    (fz : ρ.findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fx : ρ.findVal? zx = some (idxV x.toNat))
    (h : EvalExp (simEnv B) ρ (.callE "mem" [.expA (.varE "z"), .expA (.varE zx)]) Mv) :
    ∃ ma mi, s.mem? f x = some (ma, mi) ∧ Mv = memInstToValue mi := by
  obtain ⟨Ls, M, As, ma, hLs, hM, hAs, hma, hm⟩ := evalExp_storeAcc_inv (State.stateDefs_simEnv B)
    (State.stateDefs_simEnv B).mem hρ (NA.mem _) (evalExp_var fz) (evalExp_var fx) h
  have hLs' : Ls = .list (s.mems.map memInstToValue) := by simpa using hLs.symm
  have hM' : M = moduleInstToValue CT f.module := by simpa using hM.symm
  have hAs' : As = .list (f.module.mems.map fun a => .num (.natN a)) := by
    simpa [hM'] using hAs.symm
  obtain ⟨mi, h₁, h₂, rfl⟩ := idx_idx_map_inv (hAs' ▸ hma) (hLs' ▸ hm)
  exact ⟨ma, mi, by simp [Store.mem?, h₁, h₂], rfl⟩

/-- **`|$mem(z, x).BYTES|`, read back.** -/
theorem memLen_inv {zx : IL.Id} {x : MemIdx} {v : Value} (hρ : ρ.findDef? "mem" = none)
    (fz : ρ.findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fx : ρ.findVal? zx = some (idxV x.toNat))
    (h : EvalExp (simEnv B) ρ
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE zx)]) "BYTES")) v) :
    ∃ ma mi, s.mem? f x = some (ma, mi) ∧ v = .num (.natN mi.bytes.size) := by
  obtain ⟨bs, hbs, rfl⟩ := evalExp_lenE_iff.1 h
  obtain ⟨Mv, hMv, hB⟩ := evalExp_dotE_iff.1 hbs
  obtain ⟨ma, mi, hm, rfl⟩ := mem_inv B NA hρ fz fx hMv
  have e : bs = Memory.bytesL mi.bytes := by simpa using hB.symm
  exact ⟨ma, mi, hm, by simp [e]⟩

/-- **`Backward.read 53`** (`memory.fill-oob`). -/
theorem bwd_memoryFillOob : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 53 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).memoryFillOob hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, -⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨V, fv, hV⟩ := hq "val" State.valT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "CONST" (.tuple [AT, I]),
      V, .case "CONST" (.tuple [AT, .case "%" (.tuple [N])]), .case "MEMORY.FILL" X]]) ∧
      w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x, ha₄, hX⟩ := decode_memoryFill h₄
  obtain ⟨v, ha₂⟩ := (Typing.stateDecode_simEnv B).val a₂ _ (valsOnly_bindVals σ) (h₂ ▸ hV)
  have hpr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0) (.varE "n"))
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")))
      (.bool true) := ifPrem (hp _ (by simp))
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 hpr
  obtain ⟨t, b, t', b', ha₁, hAT, ha₃, hAT', hv₁⟩ := oob_sum_inv fi fn h₁ h₃ e₁
  have et : t' = t := encode_addrType_inj (hAT'.symm.trans hAT)
  obtain ⟨ma, mi, hm, hv₂⟩ := memLen_inv B NA rfl (hZ ▸ fz) (hX ▸ fx) e₂
  have hlt : mi.bytes.size < b.toNat + b'.toNat := gt_nat_inv (hv₁ ▸ hv₂ ▸ hcmp)
  have hstep : Step P host ⟨s, f, is⟩ ⟨s, f, [.trap]⟩ := by
    subst et
    rw [his, ha₁, ha₂, ha₃, ha₄]
    exact .memory (.fillOob hm hlt)
  exact ⟨[.trap], trap_out hc.2, hstep⟩

end Silmaril.Wasm.SpecTec.Sim.BwdRead
