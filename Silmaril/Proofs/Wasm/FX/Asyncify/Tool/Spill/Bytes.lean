module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Spill.Tool

/-!
# The tool on the wider fragment, on bytes
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- What both branches of `asyncifyW` give: the module's machine program `E`, a well-formed
statement-form program `P` with `E`'s signatures (`E`'s own program, or its spilled form), the
output module, and equal behaviours of every call in `E` and in the asyncified `P.elide`. -/
def WSpec (m m' : Module) (pages : Nat) (E : Env) (P : Prog) : Prop :=
  envOf m = some E ∧ P.WF ∧ m' = asyncifyModule m P.elide pages ∧ E.imps = P.imps ∧
    List.Forall₂ (fun d fn => d.nparams = fn.nparams ∧ d.nres = fn.nres) E.fns P.fns ∧
    ∀ {σ : Type} (H : Host σ) {e : Nat} {fn : FnSrc} (args : List W) (s : σ),
      P.fnAt e = some fn → args.length = fn.nparams → DepthBound P H (srcCfg e fn args, s) →
      ∃ c, srcInit E e args = some c ∧
        beh (srcStep E H) (c, s) =
          beh (tgtStep (asyncifyProg P.elide) H) (tgtSt P.elide e fn.elide args s)

theorem wspec_of_E {m m' : Module} {pages : Nat} (h : asyncifyE m pages = .ok m') :
    ∃ E P, WSpec m m' pages E P := by
  obtain ⟨P, hr, hm'⟩ := asyncifyE_eq h
  obtain ⟨hwf, henv⟩ := recognize_sound hr
  refine ⟨P.env, P, henv, hwf, hm', rfl, forall₂_sig_self P,
    fun {_} H {_} {_} args s hfn hargs hb => ⟨_, srcInit_eq hfn args, ?_⟩⟩
  exact asyncify_elide_beh P hwf H hfn args hargs s hb

theorem wspec_of_S {m m' : Module} {pages : Nat} (h : asyncifyS m pages = .ok m') :
    ∃ E P, WSpec m m' pages E P := by
  obtain ⟨E, gs, hE, hgs, hP, hwf, hm'⟩ := asyncifyS_eq h
  have hEq : E = segEnv E.imps gs := (segmentEnv_sound hgs).1
  have himps : E.imps = (progOf (spEnv E.imps gs)).imps := by
    have := congrArg Env.imps hP; simpa [Prog.env, spEnv] using this.symm
  have hfns : List.Forall₂ (fun d fn => d.nparams = fn.nparams ∧ d.nres = fn.nres) E.fns
      (progOf (spEnv E.imps gs)).fns := by
    rw [hEq]; exact forall₂_sig_spill hP
  exact ⟨E, _, hE, hwf, hm', himps, hfns, fun {_} H {_} {_} args s hfn hargs hb =>
    asyncifyS_beh hgs hP hwf H args s hfn hargs hb⟩

theorem wspec_of_W {m m' : Module} {pages : Nat} (h : asyncifyW m pages = .ok m') :
    ∃ E P, WSpec m m' pages E P := by
  unfold asyncifyW at h
  split at h
  · rename_i m'' he
    have hm : m'' = m' := Except.ok.inj h
    exact hm ▸ wspec_of_E he
  · exact wspec_of_S h

theorem asyncifyBytesW_inv {b b' : ByteArray} {pages : Nat} (h : asyncifyBytesW b pages = .ok b') :
    ∃ m m' bs, Binary.Core.decode? b = some m ∧ asyncifyW m pages = .ok m' ∧
      Binaryen.Exe.encodeModule? m' = .ok bs ∧ b' = ⟨bs.toArray⟩ := by
  unfold asyncifyBytesW at h
  split at h
  · cases h
  · rename_i m hd
    split at h
    · cases h
    · rename_i m' ha
      split at h
      · rename_i bs he
        exact ⟨m, m', bs, hd, ha, he, (Except.ok.inj h).symm⟩
      · cases h

/-- **The tool on the wider fragment, end to end** (`wasm-asyncify asyncify`, the default).
When `asyncifyBytesW` turns `b` into `b'`: `b` decodes to a module `m` with machine program `E`;
`P` is a well-formed statement-form program (`E`'s own, or its spill when operands are live
across calls); `b'` encodes a module read back as the asyncified `P.elide`, with the protocol's
globals and the same exports; and every call of a defined function has the same behaviours in
`E` under the suspending semantics and in `b'` under the asyncify host protocol, for every
deterministic host, when the shadow stack of `P`'s runs stays below `2 ^ 32`. -/
theorem asyncifyBytesW_correct {b b' : ByteArray} {pages : Nat}
    (h : asyncifyBytesW b pages = .ok b') :
    ∃ m E P m', Binary.Core.decode? b = some m ∧ Binary.Core.Encodes b'.data.toList m' ∧
      envOf m = some E ∧ P.WF ∧ envOfLax m' = some (asyncifyProg P.elide) ∧
      globalsOfLax m' = some P.elide.tGlobals ∧ (∀ name, exportFunc m' name = exportFunc m name) ∧
      ∀ {σ : Type} (H : Host σ) {e : Nat} {fn : FnSrc} (args : List W) (s : σ),
        P.fnAt e = some fn → args.length = fn.nparams → DepthBound P H (srcCfg e fn args, s) →
        ∃ c, srcInit E e args = some c ∧
          beh (srcStep E H) (c, s) =
            beh (tgtStep (asyncifyProg P.elide) H) (tgtSt P.elide e fn.elide args s) := by
  obtain ⟨m, m', bs, hd, hw, he, hb'⟩ := asyncifyBytesW_inv h
  obtain ⟨E, P, hE, hwf, hm', himps, hfns, hbeh⟩ := wspec_of_W hw
  have hfns' : List.Forall₂ (fun d fn => d.nparams = fn.nparams ∧ d.nres = fn.nres) E.fns
      P.elide.fns := by
    simp only [Prog.elide]
    exact List.forall₂_map_right_iff.2 (hfns.imp fun _ _ hx => hx)
  have henc : Binary.Core.Encodes b'.data.toList m' := by
    rw [hb']; simpa using Binaryen.Exe.encodeModule?_sound he
  refine ⟨m, E, P, m', hd, henc, hE, hwf, ?_, ?_, ?_, hbeh⟩
  · rw [hm']; exact envOfLax_asyncifyModule_of (P := P.elide) hE himps hfns' pages
  · rw [hm']; exact globalsOfLax_asyncifyModule m P.elide pages
  · rw [hm']; exact exportFunc_asyncifyModule m P.elide pages

end Silmaril.Wasm.FX.Asyncify.Tool
