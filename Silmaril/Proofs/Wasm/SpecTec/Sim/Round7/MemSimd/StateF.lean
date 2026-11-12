module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Defs
public import Silmaril.Wasm.SpecTec.Sim.BwdRead.Thms
public import Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Thms

/-!
# Round 7, memory SIMD: reading `$mem(z, x)` at a state with any function list

The memory SIMD load rules consult the state only through `$mem(z, x)`, which reads the store's
`MEMS` field and the frame's module. `stateVF F s f` is `stateV hn s f` with the store's `FUNCS`
field replaced by an arbitrary value `F`; `stateV` and `stateVD` are its instances
(`stateV_eq_stateVF`, `stateVD_eq_stateVF`).

* `mem_invF`, `memPrem_invF`: round 5's `BwdPureStep.mem_inv` and `memPrem_inv` at `stateVF`;
* `memIdx_invF`: `BwdRead.mem_inv` at `stateVF`.

The proofs are those of the originals, which read only `MEMS` and `MODULE`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (idxV)

variable {H : Type}

/-- `stateV` is `stateVF` at the `funcInstV` images of the store's functions. -/
theorem stateV_eq_stateVF (hn : H → String) (s : Store H) (f : Frame) :
    stateV hn s f = stateVF (.list (s.funcs.map (funcInstV hn))) s f := rfl

/-- `stateVD` is `stateVF` at the `funcInstVD` images of the store's functions. -/
theorem stateVD_eq_stateVF (hn : H → String) (s : Store H) (f : Frame) :
    stateVD hn s f = stateVF (.list (s.funcs.map (funcInstVD hn))) s f := rfl

@[simp] theorem storeVF_MEMS (F : Value) (s : Store H) :
    (storeVF F s).field? "MEMS" = some (.list (s.mems.map memInstToValue)) := rfl

/-- A module address list entry at `stateVF` (`BwdPureStep.moduleIdx_inv` at any function
list). -/
theorem moduleIdx_invF {env : Env} {ρ₀ : VarEnv} (D : State.StateDefs env) {F : Value}
    {s : Store H} {f : Frame} {k : Nat} {iv : Value} {Fl : AtomS} {As : List Nat}
    (fz : ρ₀.findVal? "z" = some (stateVF F s f))
    (fx : ρ₀.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (hd : ρ₀.findDef? "fof" = none)
    (hM : (moduleInstToValue CT f.module).field? Fl = some (.list (As.map fun a => .num (.natN a))))
    (h : EvalExp env ρ₀ (.idxE (.dotE (.dotE (.callE "fof" [.expA (.varE "z")]) "MODULE")
      Fl) State.idxPayload) iv) :
    ∃ a, As[k]? = some a ∧ iv = .num (.natN a) := by
  obtain ⟨Bs, j, hBs, hj, hBj⟩ := evalExp_idxE_iff.1 h
  have eBs : Bs = .list (As.map fun a => .num (.natN a)) :=
    EvalExp.unique hBs (evalExp_dotE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨_,
      State.evalExp_fof D hd (evalExp_var fz), State.frameV_MODULE f⟩, hM⟩)
  have ej : Value.num (.natN j) = .num (.natN k) := EvalExp.unique hj (State.evalExp_idxPayload fx)
  have ej' : j = k := by simpa using ej
  have hAk : (As.map fun a => Value.num (.natN a))[k]? = some iv := by
    rw [eBs, ej'] at hBj
    exact hBj
  rw [List.getElem?_map] at hAk
  obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.1 hAk
  exact ⟨a, ha, he.symm⟩

variable (B : Builtins)

/-- **`$mem(z, x)` at `stateVF`, inverted**: the module lists `x` and the store holds the memory
(`BwdPureStep.mem_inv` at any function list). -/
theorem mem_invF (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none) {ρ : VarEnv}
    (hρ : ValsOnly ρ) {F : Value} {s : Store H} {f : Frame} {k : Nat} {M : Value}
    (fz : ρ.findVal? "z" = some (stateVF F s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (h : EvalExp (simEnv B) ρ (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) M) :
    ∃ ma mi, f.module.mems[k]? = some ma ∧ s.mems[ma]? = some mi ∧ M = memInstToValue mi := by
  have D := State.stateDefs_simEnv B
  have hbody := BwdPureStep.evalExp_call1_inv D.mem (Prims.findDef_none_of_valsOnly hρ _) (hb _ _)
    (evalArgs_cons (evalExp_var fz) (evalArgs_cons (evalExp_var fx) evalArgs_nil))
    State.matchArgs_zxPat h
  obtain ⟨L, j, hL, hj, hLj⟩ := evalExp_idxE_iff.1 hbody
  have eL : L = .list (s.mems.map memInstToValue) :=
    EvalExp.unique hL (evalExp_dotE_iff.2 ⟨_, State.evalExp_sof D rfl (evalExp_var rfl),
      storeVF_MEMS F s⟩)
  obtain ⟨ma, hma, hj'⟩ := moduleIdx_invF D rfl rfl rfl (State.moduleV_MEMS _) hj
  have hj'' : j = ma := by simpa using hj'
  have hLt : (s.mems.map memInstToValue)[ma]? = some M := by
    rw [eL, hj''] at hLj
    exact hLj
  rw [List.getElem?_map] at hLt
  obtain ⟨mi, hmi, he⟩ := Option.map_eq_some_iff.1 hLt
  exact ⟨ma, mi, hma, hmi, he.symm⟩

/-- **The premise `N > |$mem(z, x).BYTES|` at `stateVF`, read back**, given the access end `N`
(`BwdPureStep.memPrem_inv` at any function list). -/
theorem memPrem_invF (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none) {ρ : VarEnv}
    (hρ : ValsOnly ρ) {F : Value} {s : Store H} {f : Frame} {k N : Nat} {eN : Exp}
    (fz : ρ.findVal? "z" = some (stateVF F s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (hN : EvalExp (simEnv B) ρ eN (.num (.natN N)))
    (h : EvalExp (simEnv B) ρ (.cmpE .gtOp (.numT .natT) eN
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")))
      (.bool true)) :
    ∃ ma mi, f.module.mems[k]? = some ma ∧ s.mems[ma]? = some mi ∧ mi.bytes.size < N := by
  obtain ⟨v₁, v₂, e₁, e₂, hc⟩ := evalExp_cmpE_iff.1 h
  have ev₁ : v₁ = .num (.natN N) := EvalExp.unique e₁ hN
  obtain ⟨vs, hvs, rfl⟩ := evalExp_lenE_iff.1 e₂
  obtain ⟨M, hM, hMf⟩ := evalExp_dotE_iff.1 hvs
  obtain ⟨ma, mi, hma, hmi, rfl⟩ := mem_invF B hb hρ fz fx hM
  have evs : vs = Memory.bytesL mi.bytes := by
    simpa [Memory.memInstV_BYTES] using hMf.symm
  have hlt : mi.bytes.size < N := by
    simpa [ev₁, evs, cmpValues, Num.cmp, Res.ofOption] using hc
  exact ⟨ma, mi, hma, hmi, hlt⟩

/-- **`$mem(z, x)` at `stateVF`, read back into `Store.mem?`** (`BwdRead.mem_inv` at any function
list), for a `B` that does not interpret the state accessors. -/
theorem memIdx_invF (NA : BwdRead.NoAcc B) {ρ : VarEnv} {zx : IL.Id} {F : Value} {s : Store H}
    {f : Frame} {x : MemIdx} {Mv : Value} (hρ : ρ.findDef? "mem" = none)
    (fz : ρ.findVal? "z" = some (stateVF F s f))
    (fx : ρ.findVal? zx = some (idxV x.toNat))
    (h : EvalExp (simEnv B) ρ (.callE "mem" [.expA (.varE "z"), .expA (.varE zx)]) Mv) :
    ∃ ma mi, s.mem? f x = some (ma, mi) ∧ Mv = memInstToValue mi := by
  obtain ⟨Ls, M, As, ma, hLs, hM, hAs, hma, hm⟩ :=
    BwdRead.evalExp_storeAcc_inv (State.stateDefs_simEnv B) (State.stateDefs_simEnv B).mem hρ
      (NA.mem _) (evalExp_var fz) (evalExp_var fx) h
  have hLs' : Ls = .list (s.mems.map memInstToValue) := by simpa using hLs.symm
  have hM' : M = moduleInstToValue CT f.module := by simpa using hM.symm
  have hAs' : As = .list (f.module.mems.map fun a => .num (.natN a)) := by
    simpa [hM'] using hAs.symm
  obtain ⟨mi, h₁, h₂, rfl⟩ := BwdRead.idx_idx_map_inv (hAs' ▸ hma) (hLs' ▸ hm)
  exact ⟨ma, mi, by simp [Store.mem?, h₁, h₂], rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
