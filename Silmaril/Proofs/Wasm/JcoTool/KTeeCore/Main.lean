module

public import Silmaril.Wasm.JcoTool.KTeeCore.Defs
public import Silmaril.Wasm.JcoTool.KCoreRun.Thms
public import Silmaril.Wasm.JcoTool.KCoreHost.Thms

/-!
# The generated tee on Core 3.0, from instantiation on: proofs

* `impsOKT_host`: the tee's host store supplies its eight imports, `task.return` with two values;
* `liftT_calls`: the six drop-store calls of the tee's lift succeed on every store in which the
  input is a readable end below the next free handle, with the next five handles;
* `genT_inst_host`, `genT_lift_host`: instantiation of `KTeeEmit.toModuleT N name` on the host
  store, then its lift on a fresh input, end at the machine `KTee.initMST` with the callback in
  place;
* `imports_xtT`, `addrs_okT`, `instT_exists`: a valid tee module has a Core 3.0 instantiation on its
  host store.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KTeeCore

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCore (BI M32 INSR OUTSW WS)
open Silmaril.Wasm.JcoTool.KCoreRun (ImpsOKN InstR RetAt EntryAt CbAt LSteps w)
open Silmaril.Wasm.JcoTool.KTeeCore
open Silmaril.Wasm.JcoTool.KTee (genT initMST W1g)
open Silmaril.Wasm.Component.Streams.Drop (DStore dstep)

variable {H : Type}

/-- **The tee's host store supplies its eight imports.** -/
theorem impsOKT_host (hb : BI → H) : ImpsOKN 2 hb (hostStoreT hb) Silmaril.Wasm.JcoTool.KCoreHost.hostAddrs := by
  refine ⟨rfl, fun b => ?_⟩
  cases b
  all_goals exact ⟨_, _, _, _, rfl, rfl, rfl, Expand.iff.mpr rfl, rfl⟩

open Silmaril.Wasm.Component.Async (upd) in
/-- **The tee's six drop-store calls succeed** on every store in which `r` is a readable end below
the next free handle `n`: the outputs are `(n, n + 1)` and `(n + 2, n + 3)`, the set `n + 4`. -/
theorem liftT_calls {st : DStore} {r s : Nat} (ht : st.tbl r = some (.streamR s)) (hr : r < st.next) :
    ∃ st₁ st₂ st₃ st₄ st₅ st₆ u₁ u₂ u₃,
      dstep st .streamNew = some (st₁, .ends st.next (st.next + 1)) ∧
      dstep st₁ .streamNew = some (st₂, .ends (st.next + 2) (st.next + 3)) ∧
      dstep st₂ .wsNew = some (st₃, .nat (st.next + 4)) ∧
      dstep st₃ (.join r (st.next + 4)) = some (st₄, u₁) ∧
      dstep st₄ (.join (st.next + 1) (st.next + 4)) = some (st₅, u₂) ∧
      dstep st₅ (.join (st.next + 3) (st.next + 4)) = some (st₆, u₃) := by
  have n0 : r ≠ st.next := by omega
  have n1 : r ≠ st.next + 1 := by omega
  have n2 : r ≠ st.next + 2 := by omega
  have n3 : r ≠ st.next + 3 := by omega
  have n4 : r ≠ st.next + 4 := by omega
  let st₁ : DStore := ⟨st.next + 2,
    upd (upd st.tbl st.next (some (.streamR st.next))) (st.next + 1) (some (.streamW st.next)),
    upd st.chans st.next {}, st.joined⟩
  let st₂ : DStore := ⟨st.next + 4,
    upd (upd st₁.tbl (st.next + 2) (some (.streamR (st.next + 2)))) (st.next + 3)
      (some (.streamW (st.next + 2))), upd st₁.chans (st.next + 2) {}, st.joined⟩
  let st₃ : DStore := ⟨st.next + 5, upd st₂.tbl (st.next + 4) (some .wset), st₂.chans, st.joined⟩
  let st₄ : DStore := ⟨st₃.next, st₃.tbl, st₃.chans, upd st₃.joined r (some (st.next + 4))⟩
  let st₅ : DStore := ⟨st₄.next, st₄.tbl, st₄.chans, upd st₄.joined (st.next + 1) (some (st.next + 4))⟩
  let st₆ : DStore := ⟨st₅.next, st₅.tbl, st₅.chans, upd st₅.joined (st.next + 3) (some (st.next + 4))⟩
  refine ⟨st₁, st₂, st₃, st₄, st₅, st₆, .unit, .unit, .unit, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [dstep, st₂, st₁, show st.next + 2 + 2 = st.next + 4 by omega]
  · simp only [dstep, st₃, st₂, st₁, show st.next + 4 + 1 = st.next + 5 by omega]
  · simp [st₄, st₃, st₂, st₁, dstep, upd, n0, n1, n2, n3, n4, ht]
  · simp [st₅, st₄, st₃, st₂, st₁, dstep, upd]
  · simp [st₆, st₅, st₄, st₃, st₂, st₁, dstep, upd]

/-- **Instantiation of the tee on its host store.** -/
theorem genT_inst_host {Pf : Profile} {host : HostSemantics H} {hb : BI → H} {N : Nat} {name : String}
    {c : Config H}
    (hI : Instantiate Pf host (hostStoreT hb) (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name)
      (Silmaril.Wasm.JcoTool.KCoreHost.hostAddrs.map .func) c) :
    c.code = [] ∧ ∃ ma a₉ a₁₀, InstR hb ma c.store c.frame.module (fun _ => 0) (fun _ => 0) ∧
      RetAt hb c.store c.frame.module 2 ∧
      c.frame.module.funcs[9]? = some a₉ ∧ EntryAt c.store c.frame.module (genT N) a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧ CbAt c.store c.frame.module (genT N) a₁₀ := by
  have h := Silmaril.Wasm.JcoTool.KCoreRun.toModuleI_inst hI (impsOKT_host hb)
  have hg : (fun i => (genT N).g0 i % M32) = fun _ => 0 := funext fun _ => Nat.zero_mod _
  rw [hg] at h
  exact h

/-- **Instantiation and the lift of the tee on Core 3.0**, on any drop store whose input `r` is a
readable end below the next free handle `n` (with room for five more handles): the lift runs to
`YIELD`, returns `n` and `n + 2` with one `task.return` of two values, and leaves the instance at
the machine `initMST r (n + 1) (n + 3) (n + 4)` with the callback in place. -/
theorem genT_lift_host (Pf : Profile) {host : HostSemantics H} {hb : BI → H} {N : Nat} {name : String}
    {c : Config H}
    (hI : Instantiate Pf host (hostStoreT hb) (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name)
      (Silmaril.Wasm.JcoTool.KCoreHost.hostAddrs.map .func) c)
    {st : DStore} {rp : Option (Nat × Nat)} {t : List Nat} {r sr : Nat}
    (ht : st.tbl r = some (.streamR sr)) (hr : r < st.next) (hn : st.next + 5 ≤ M32) :
    c.code = [] ∧ ∃ st₆ ma a₉ a₁₀ cs', c.frame.module.funcs[9]? = some a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧
      LSteps Pf hb ma (((st, rp), t), invoke c.store a₉ [Val.i32 (w r)])
        (((st₆, rp), t ++ [st.next, st.next + 2]), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) ∧
      InstR hb ma cs' c.frame.module (initMST r (st.next + 1) (st.next + 3) (st.next + 4)).g
        (initMST r (st.next + 1) (st.next + 3) (st.next + 4)).m ∧
      CbAt cs' c.frame.module (genT N) a₁₀ := by
  obtain ⟨hc, ma, a₉, a₁₀, hI₀, hret, h₉, hen, h₁₀, hcb⟩ := genT_inst_host hI
  obtain ⟨st₁, st₂, st₃, st₄, st₅, st₆, u₁, u₂, u₃, hn₀, hn₁, hws, hj₁, hj₂, hj₃⟩ := liftT_calls ht hr
  obtain ⟨cs', hI', hfs, hrun⟩ := Silmaril.Wasm.JcoTool.KCoreRun.entryT_run Pf (t := t) (rp := rp) rfl hI₀ hret
    hen (by omega) hn₀ (by omega) (by omega) hn₁ (by omega) (by omega) hws (by omega) hj₁ hj₂ hj₃
  exact ⟨hc, st₆, ma, a₉, a₁₀, cs', h₉, h₁₀, hrun, hI', Silmaril.Wasm.JcoTool.KCoreRun.cbAt_of_funcs hcb hfs⟩

/-- The extern types of the tee's imports are those of its host store's functions. -/
theorem imports_xtT {name : String} {xtI : List CExternType}
    (h : List.Forall₂ (ImportOk { types := allocTypes Silmaril.Wasm.JcoTool.KCoreEmit.types })
      (Silmaril.Wasm.JcoTool.KTeeEmit.importsT name) xtI) :
    xtI = Silmaril.Wasm.JcoTool.KCoreHost.bis.map fun b => .func (hostDTT b) := by
  rcases h with _ | ⟨h0, h⟩; rcases h with _ | ⟨h1, h⟩; rcases h with _ | ⟨h2, h⟩
  rcases h with _ | ⟨h3, h⟩; rcases h with _ | ⟨h4, h⟩; rcases h with _ | ⟨h5, h⟩
  rcases h with _ | ⟨h6, h⟩; rcases h with _ | ⟨h7, h⟩; rcases h with _ | ⟨_, _⟩
  have e : ∀ {x y : Option CExternType} {z : CExternType}, x = some z → x = y → y = some z :=
    fun h1 h2 => h2 ▸ h1
  simp only [Silmaril.Wasm.JcoTool.KCoreHost.bis, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact ⟨(Option.some.inj (e h0.1 rfl)).symm, (Option.some.inj (e h1.1 rfl)).symm,
    (Option.some.inj (e h2.1 rfl)).symm, (Option.some.inj (e h3.1 rfl)).symm,
    (Option.some.inj (e h4.1 rfl)).symm, (Option.some.inj (e h5.1 rfl)).symm,
    (Option.some.inj (e h6.1 rfl)).symm, (Option.some.inj (e h7.1 rfl)).symm⟩

theorem addr_okT (hb : BI → H) (i : Nat) (b : BI)
    (h : (hostStoreT hb).funcs[i]? = some ⟨hostDTT b, {}, .host (hb b)⟩) :
    ExternAddrOk (hostStoreT hb) (.func i) (.func (hostDTT b)) := .func h

/-- The tee's host store's addresses have its host functions' types. -/
theorem addrs_okT (hb : BI → H) :
    List.Forall₂ (ExternAddrOk (hostStoreT hb)) (Silmaril.Wasm.JcoTool.KCoreHost.hostAddrs.map .func)
      (Silmaril.Wasm.JcoTool.KCoreHost.bis.map fun b => .func (hostDTT b)) :=
  .cons (addr_okT hb 0 .taskReturn rfl) <| .cons (addr_okT hb 1 .streamNew rfl) <|
    .cons (addr_okT hb 2 .streamRead rfl) <| .cons (addr_okT hb 3 .streamWrite rfl) <|
    .cons (addr_okT hb 4 .dropR rfl) <| .cons (addr_okT hb 5 .dropW rfl) <|
    .cons (addr_okT hb 6 .wsNew rfl) <| .cons (addr_okT hb 7 .join rfl) .nil

/-- **A valid tee module has a Core 3.0 instantiation on its host store.** -/
theorem instT_exists {Pf : Profile} {host : HostSemantics H} (hb : BI → H) (N : Nat) (name : String)
    (hv : ModuleValid (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name)) :
    ∃ c, Instantiate Pf host (hostStoreT hb) (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name)
      (Silmaril.Wasm.JcoTool.KCoreHost.hostAddrs.map .func) c := by
  obtain ⟨⟨xtI, xtE⟩, hok⟩ := hv
  have hvalid : ∃ xtE xtI, ModuleOk (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name) ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk (hostStoreT hb)) (Silmaril.Wasm.JcoTool.KCoreHost.hostAddrs.map .func) xtI := by
    refine ⟨xtE, xtI, hok, ?_⟩
    obtain ⟨htypes, himports, -⟩ := hok
    rw [← allocTypes_eq htypes] at himports
    rw [imports_xtT himports]
    exact addrs_okT hb
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1
    (Silmaril.Wasm.JcoTool.KCoreHost.instantiate?_some (genT N) name
      (Silmaril.Wasm.JcoTool.KTeeEmit.importsT name) (hostStoreT hb))
  exact ⟨c, (instantiate?_iff hvalid).1 hc⟩

end Silmaril.Proofs.Wasm.JcoTool.KTeeCore
