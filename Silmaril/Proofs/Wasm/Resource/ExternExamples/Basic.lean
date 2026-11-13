module

public import Silmaril.Wasm.Resource.ExternExamples.Defs
public import Silmaril.Wasm.Resource.Extern.Thms
public import Silmaril.Wasm.Game.Untyped.Thms
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.Verify.Check.Thms

/-!
# Real `externref` clients: refutation and proof

* Kernel-checked facts (`decide +kernel`): both modules validate and instantiate; the shape of
  the instantiated stores.
* `badPlay_mem`: the host-free Core run of `run hnd` in `exUse` reaches the callout
  `use hnd` (hand-built Core steps, every profile, `out_iff_core`), so `badPlay` is a play of
  `exUseU.strategy P`; `badPlay` is rejected by `uClientSpec 0 1 2` and by
  `keptSpec exUseS (· ∈ useG) 0 1 2`.
* `keptInv`: for an untyped instance whose exports lie in a closed function set `G` avoiding the
  `use` and `free` host functions, an `LTSInv` of `U.lts P` for `keptSpec` (thread invariant:
  silmaril-lean's reachability invariant `CfgIn` of `Silmaril.Wasm.Verify.Reach`, carried across
  environment answers by the guard).

New proofs, following `Silmaril.Proofs.Wasm.Game.Untyped.Example` and
`Silmaril.Proofs.Wasm.Verify.Reach.Plays`.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.ExternExamples

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.UntypedExample Silmaril.Wasm.Verify
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-- The closed type `externref`. -/
abbrev externC : CValType := .refv (.ref true (.abs .extern))

/-- `[] → [externref]`. -/
abbrev allocTy : CCompType := .func (Ty.ofList []) (Ty.ofList [externC])

/-- `[externref] → []`. -/
abbrev useTy : CCompType := .func (Ty.ofList [externC]) (Ty.ofList [])

/-- The host code of a host function. -/
def hostCode? (fi : FuncInst Nat) : Option Nat := match fi.code with
  | .host h => some h
  | _ => none

/-- A Wasm function without locals whose body is `local.get 0; call 1`. -/
def isUseBody (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.localGet x, .call y]⟩ => x.toNat == 0 && y.toNat == 1
  | _ => false

/-- A Wasm function without locals whose body is `call 0`. -/
def isAllocBody (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.call y]⟩ => y.toNat == 0
  | _ => false

/-! ### Kernel-checked facts -/

theorem exUse_valid : (validate? exUse).isSome = true := by decide +kernel
theorem exUse_prep : (prepare? evalConst? (impStoreOf exUse) exUse
    (importAddrs (mtOf exUse))).isSome = true := by decide +kernel
theorem exAlloc_valid : (validate? exAlloc).isSome = true := by decide +kernel
theorem exAlloc_prep : (prepare? evalConst? (impStoreOf exAlloc) exAlloc
    (importAddrs (mtOf exAlloc))).isSome = true := by decide +kernel

theorem use_len : exUseS.funcs.length = 4 := by decide +kernel
theorem use_host : exUseS.funcs.map hostCode? = [some 0, some 1, some 2, none] := by
  decide +kernel
theorem use_expand : exUseS.funcs.map (fun fi => fi.type.expand?) =
    [some allocTy, some useTy, some useTy, some useTy] := by decide +kernel
theorem use_mod : (exUseS.funcs.map fun fi => fi.module.funcs) = [[], [], [], [0, 1, 2, 3]] := by
  decide +kernel
theorem use_body : exUseS.funcs.map isUseBody = [false, false, false, true] := by decide +kernel
theorem use_addrs : exportFuncAddrs (prepOf exUse).1.frame.module = [3] := by decide +kernel
theorem use_storeFuncs : storeFuncs exUseS = [] := by decide +kernel

theorem alloc_host : exAllocS.funcs.map hostCode? = [some 0, some 1, some 2, none] := by
  decide +kernel
theorem alloc_expand : exAllocS.funcs.map (fun fi => fi.type.expand?) =
    [some allocTy, some useTy, some useTy, some allocTy] := by decide +kernel
theorem alloc_body : exAllocS.funcs.map isAllocBody = [false, false, false, true] := by
  decide +kernel
theorem alloc_addrs : exportFuncAddrs (prepOf exAlloc).1.frame.module = [3] := by decide +kernel
theorem alloc_storeFuncs : storeFuncs exAllocS = [] := by decide +kernel
theorem alloc_closed : closedB exAllocS [0, 1, 2, 3] allocG = true := by decide +kernel
theorem alloc_avoids_use : avoidsB exAllocS allocG 1 = true := by decide +kernel
theorem alloc_avoids_free : avoidsB exAllocS allocG 2 = true := by decide +kernel

/-! ### The shape of the store of `exUse` -/

theorem hostCode?_code {fi : FuncInst Nat} {h : Nat} (hh : hostCode? fi = some h) :
    fi.code = .host h := by
  unfold hostCode? at hh
  split at hh
  · cases hh; assumption
  · cases hh

theorem isUseBody_code {fi : FuncInst Nat} (h : isUseBody fi = true) :
    ∃ (t : TypeIdx) (x : LocalIdx) (y : FuncIdx),
      fi.code = .wasm ⟨t, [], [.localGet x, .call y]⟩ ∧ x.toNat = 0 ∧ y.toNat = 1 := by
  unfold isUseBody at h
  split at h
  · rename_i t x y hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨t, x, y, hc, h.1, h.2⟩
  · cases h

theorem list_four {α : Type} {l : List α} (h : l.length = 4) : ∃ a b c d, l = [a, b, c, d] :=
  match l, h with
  | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

/-- The shape of the instantiated store of `exUse`. -/
structure UseShape (fu fr : FuncInst Nat) (t : TypeIdx) (x : LocalIdx) (y : FuncIdx) : Prop where
  get₁ : exUseS.funcs[1]? = some fu
  get₃ : exUseS.funcs[3]? = some fr
  codeU : fu.code = .host 1
  tyU : Expand fu.type useTy
  codeR : fr.code = .wasm ⟨t, [], [.localGet x, .call y]⟩
  tyR : Expand fr.type useTy
  hx : x.toNat = 0
  hy : y.toNat = 1
  modR : fr.module.funcs = [0, 1, 2, 3]

theorem useShape : ∃ fu fr t x y, UseShape fu fr t x y := by
  obtain ⟨f₀, f₁, f₂, f₃, hf⟩ := list_four use_len
  have hhost := hf ▸ use_host
  have hexp := hf ▸ use_expand
  have hmod := hf ▸ use_mod
  have hbody := hf ▸ use_body
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hhost hexp hmod hbody
  obtain ⟨t, x, y, hc, hx, hy⟩ := isUseBody_code hbody.2.2.2.1
  exact ⟨f₁, f₃, t, x, y, by rw [hf]; rfl, by rw [hf]; rfl, hostCode?_code hhost.2.1,
    Expand.iff.mpr hexp.2.1, hc, Expand.iff.mpr hexp.2.2.2.1, hx, hy, hmod.2.2.2.1⟩

/-! ### The run of `run hnd` in `exUse` (every profile) -/

section Run

variable {P : Profile} {host : HostSemantics Nat} {fu fr : FuncInst Nat} {t : TypeIdx}
  {x : LocalIdx} {y : FuncIdx}

/-- The frame of `run hnd`. -/
abbrev runFrame (fr : FuncInst Nat) : Frame := Frame.forCall fr.module [hnd] []

theorem step_head' {s s' : Store Nat} {f f' : Frame} {is is' rest : List Admin}
    (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (hr : rest ≠ []) :
    Step P host ⟨s, f, is ++ rest⟩ ⟨s', f', is' ++ rest⟩ := by
  simpa [vals] using Step.ctxtInstrs (vs := []) (rest := rest) h (.inr hr)

/-- The code at the callout `use hnd`. -/
abbrev useCode (fu fr : FuncInst Nat) : List Admin :=
  [.frame 0 (runFrame fr) [.label 0 [] (vals [hnd] ++ [.ref (.func 1), .callRefType fu.type])]]

/-- **The host-free run of `run hnd` to the callout `use hnd`**, every profile. -/
theorem run_use (h : UseShape fu fr t x y) :
    Reach P (exUseS, .pending 3 [hnd]) (exUseS, .active {} (useCode fu fr)) := by
  have h₁ : Step P (fun _ _ _ _ => False) (invoke exUseS 3 [hnd])
      ⟨exUseS, {}, [.frame 0 (runFrame fr)
        [.label 0 [] [.plain (.localGet x), .plain (.call y)]]]⟩ :=
    Step.callRefFunc (s := exUseS) (f := {})
      (c := .callRefType ((exUseS.funcs[3]?.map FuncInst.type).getD default)) (vs := [hnd])
      trivial h.get₃ h.tyR rfl h.codeR
  have hl : (runFrame fr).local? x = some (some hnd) := by
    simp [Frame.local?, Frame.forCall, h.hx]
  have h₂ : Step P (fun _ _ _ _ => False)
      ⟨exUseS, runFrame fr, [.plain (.localGet x), .plain (.call y)]⟩
      ⟨exUseS, runFrame fr, [hnd.toAdmin, .plain (.call y)]⟩ :=
    step_head' (is := [.plain (.localGet x)]) (Step.«variable» (VariableStep.localGet hl))
      (by simp)
  have hx' : (runFrame fr).module.funcs[y.toNat]? = some 1 := by
    simp [Frame.forCall, h.modR, h.hy]
  have h₃ : Step P (fun _ _ _ _ => False) ⟨exUseS, runFrame fr, [hnd.toAdmin, .plain (.call y)]⟩
      ⟨exUseS, runFrame fr, vals [hnd] ++ [.ref (.func 1), .callRefType fu.type]⟩ := by
    simpa [vals] using Step.ctxtInstrs (vs := [hnd]) (rest := []) (Step.call hx' h.get₁)
      (.inl (by simp))
  have h₂' := Step.ctxtFrame (f := {}) (n := 0) (Step.ctxtLabel (n := 0) (cont := []) h₂)
  have h₃' := Step.ctxtFrame (f := {}) (n := 0) (Step.ctxtLabel (n := 0) (cont := []) h₃)
  have i₁ : InternalP P (exUseS, Thread.pending 3 [hnd]) (exUseS, .active {}
      [.frame 0 (runFrame fr) [.label 0 [] [.plain (.localGet x), .plain (.call y)]]]) :=
    ⟨_, _, rfl, h₁⟩
  have i₂ : InternalP P (exUseS, Thread.active {}
      [.frame 0 (runFrame fr) [.label 0 [] [.plain (.localGet x), .plain (.call y)]]])
      (exUseS, .active {} [.frame 0 (runFrame fr) [.label 0 [] [hnd.toAdmin, .plain (.call y)]]]) :=
    ⟨_, _, rfl, h₂'⟩
  have i₃ : InternalP P (exUseS, Thread.active {}
      [.frame 0 (runFrame fr) [.label 0 [] [hnd.toAdmin, .plain (.call y)]]])
      (exUseS, .active {} (useCode fu fr)) := ⟨_, _, rfl, h₃'⟩
  exact (Relation.ReflTransGen.single i₁).tail i₂ |>.tail i₃

/-- `decompose?` finds the callout `use hnd`. -/
theorem decompose_use (h : UseShape fu fr t x y) :
    CalloutAt exUseS (.active {} (useCode fu fr)) 1 [hnd] := by
  have hr : decompose? exUseS (vals [hnd] ++ [.ref (.func 1), .callRefType fu.type]) =
      some (.top [] [], 1, 1, [hnd]) :=
    decompose?_redex (c := .callRefType fu.type) trivial h.get₁ h.tyU rfl h.codeU
  have hsl : splitVals [Admin.label 0 [] (vals [hnd] ++ [.ref (.func 1), .callRefType fu.type])]
      = ([], [.label 0 [] (vals [hnd] ++ [.ref (.func 1), .callRefType fu.type])]) :=
    splitVals_vals_cons (vs := []) rfl []
  have hsf : splitVals [Admin.frame 0 (runFrame fr)
      [.label 0 [] (vals [hnd] ++ [.ref (.func 1), .callRefType fu.type])]] =
      ([], [.frame 0 (runFrame fr)
        [.label 0 [] (vals [hnd] ++ [.ref (.func 1), .callRefType fu.type])]]) :=
    splitVals_vals_cons (vs := []) rfl []
  refine ⟨.frame [] 0 (runFrame fr) (.label [] 0 [] (.top [] []) []) [], 1, ?_⟩
  show decompose? exUseS (useCode fu fr) = _
  rw [decompose?_of_split hsf]
  simp only [decompHead]
  rw [decompose?_of_split hsl]
  simp only [decompHead, hr, Option.map_some]

end Run

/-! ### The bad play -/

/-- A host-free run is a silent run of the untyped system. -/
theorem run_of_reach {U : UInstance} {P : Profile} (f : U.F.Op) {x y : Store Nat × Thread}
    (h : Reach P x y) : (U.lts P).Run (.running f x.1 x.2) [] (.running f y.1 y.2) := by
  induction h with
  | refl => exact .nil _
  | tail _ hst ih => exact ih.append (.tau (UInstance.Trans.tau hst) (.nil _))

/-- **`badPlay` is a play of `exUse`**, every profile: the export call `run hnd` reaches the
callout `use hnd` by host-free Core steps. -/
theorem badPlay_mem (P : Profile) : badPlay ∈ exUseU.strategy P := by
  obtain ⟨fu, fr, t, x, y, h⟩ := useShape
  refine UInstance.mem_strategy_iff.2 ⟨.waiting ⟨(), exUseS, [hnd]⟩ exUseS
    (.active {} (useCode fu fr)) ⟨1, exUseS, [hnd]⟩, ?_⟩
  exact .vis (UInstance.Trans.call _) ((run_of_reach (U := exUseU) _ (run_use h)).append
    (.vis (UInstance.Trans.ucall (decompose_use h)) (.nil _)))

/-- `badPlay` is rejected: `use hnd` with no live handle. -/
theorem badPlay_rejected : ¬ (uClientSpec (ι := Unit) 0 1 2).Accepts badPlay := by
  show ¬ ((uClientSpec (ι := Unit) 0 1 2).acceptsB badPlay = true)
  rw [show (uClientSpec (ι := Unit) 0 1 2).acceptsB badPlay = false by decide +kernel]
  decide

/-- **The bad client is refuted**, every profile. -/
theorem exUse_refuted (P : Profile) :
    ¬ ∀ p ∈ exUseU.strategy P, (uClientSpec (ι := Unit) 0 1 2).Accepts p :=
  fun h => badPlay_rejected (h _ (badPlay_mem P))

/-! ### The guard -/

section Guard

variable {S : Type} {E F : Sig.{0}} {ok : Move E F → Prop} {π : Protocol S (Move E F)}

theorem guardO_none (m : Move E F) : (π.guardO ok).step none m = some none := rfl

theorem guardO_bad {q : S} {m : Move E F} (hO : Move.IsO m) (hb : ¬ ok m) :
    (π.guardO ok).step (some q) m = some none := by
  simp only [Protocol.guardO]
  split
  · rfl
  · rename_i hn; exact absurd ⟨hO, hb⟩ hn

theorem guardO_ok {q : S} {m : Move E F} (h : Move.IsO m → ok m) :
    (π.guardO ok).step (some q) m = (π.step q m).map some := by
  simp only [Protocol.guardO]
  split
  · rename_i hc; exact absurd (h hc.1) hc.2
  · rfl

/-- The guard keeps environment moves total. -/
theorem guardO_oTotal (hT : OTotal π) : OTotal (π.guardO ok) := by
  intro q o hO
  rcases q with _ | q
  · rfl
  · by_cases hb : ok o
    · rw [guardO_ok (fun _ => hb)]
      simpa using hT q o hO
    · rw [guardO_bad hO hb]
      rfl

end Guard

/-- Environment moves never break the kept sentence. -/
theorem keptSpec_oTotal {ι : Type} (S₀ : Store Nat) (G : Nat → Prop) (ha hu hf : Nat) :
    OTotal (keptSpec (ι := ι) S₀ G ha hu hf) :=
  guardO_oTotal (uClientSpec_oTotal ha hu hf)

theorem refIn_hnd {G : Nat → Prop} : ∀ r, Val.ref r ∈ [hnd] → RefIn G r := by
  intro r hr
  simp only [hnd, List.mem_singleton, Val.ref.injEq] at hr
  subst hr
  intro a ha
  simp [refFuncs] at ha

/-- `exUse`'s own store keeps the instance. -/
theorem keeps_exUseS : Keeps exUseS (· ∈ useG) exUseS :=
  ⟨fun _ _ => rfl, mem_storeFuncs_of (by rw [use_storeFuncs]; simp)⟩

/-- **The bad client is refuted even for environments keeping the instance**, every profile:
the environment of `badPlay` hands over `exUse`'s own store and a host reference. -/
theorem exUse_refuted_kept (P : Profile) :
    ¬ ∀ p ∈ exUseU.strategy P, (keptSpec (ι := Unit) exUseS (· ∈ useG) 0 1 2).Accepts p := by
  intro h
  have hacc := h _ (badPlay_mem P)
  have h₁ : (keptSpec (ι := Unit) exUseS (· ∈ useG) 0 1 2).step (some (some []))
      (.inr (.ask ⟨(), exUseS, [hnd]⟩)) = some (some (some [])) := by
    rw [keptSpec, guardO_ok (fun _ => ⟨keeps_exUseS, refIn_hnd⟩)]
    rfl
  have h₂ : (keptSpec (ι := Unit) exUseS (· ∈ useG) 0 1 2).step (some (some []))
      (.inl (.ask ⟨1, exUseS, [hnd]⟩)) = none := by
    rw [keptSpec, guardO_ok (m := (.inl (.ask (⟨1, exUseS, [hnd]⟩ : UCall Nat)) : Move UImp (untypedSig Unit))) (fun hO => False.elim hO)]
    decide +kernel
  have hrun : (keptSpec (ι := Unit) exUseS (· ∈ useG) 0 1 2).run (some (some [])) badPlay =
      none := by
    simp only [badPlay, Protocol.run, h₁, Option.bind_some, h₂, Option.bind_none]
  have hs : ((keptSpec (ι := Unit) exUseS (· ∈ useG) 0 1 2).run (some (some [])) badPlay).isSome
      = true := hacc
  rw [hrun] at hs
  cases hs

/-! ### Clients that cannot reach `use` or `free`, in kept environments -/

/-- What the reachability checker establishes about an instantiated store `S₀` for the exports
of `U`: the function set `G` is closed for the module's function list `fs`, contains the
exports, and avoids the `use` and `free` host functions. -/
structure KeptHyp (U : UInstance) (S₀ : Store Nat) (G : Nat → Prop) (fs : List Nat)
    (hu hf : Nat) : Prop where
  closed : FuncsClosed G fs (InstrIn G fs) S₀.funcs
  avoidsU : Avoids G S₀.funcs hu
  avoidsF : Avoids G S₀.funcs hf
  exports : ∀ x, G (U.addr x)

section Kept

variable {U : UInstance} {S₀ : Store Nat} {G : Nat → Prop} {fs : List Nat} {hu hf : Nat}

theorem Keeps.closed {s : Store Nat} (hk : Keeps S₀ G s)
    (hc : FuncsClosed G fs (InstrIn G fs) S₀.funcs) : FuncsClosed G fs (InstrIn G fs) s.funcs :=
  fun a fi code ha hfi hcode => hc a fi code ha (by rw [← hk.1 a ha]; exact hfi) hcode

theorem Keeps.avoids {s : Store Nat} (hk : Keeps S₀ G s) {i : Nat} (hav : Avoids G S₀.funcs i) :
    Avoids G s.funcs i :=
  fun a fi ha hfi => hav a fi ha (by rw [← hk.1 a ha]; exact hfi)

/-- The invariant: running and waiting threads satisfy the reachability invariant `CfgIn` in a
store keeping the instance (after an environment fault, nothing). -/
def KJ (U : UInstance) (S₀ : Store Nat) (G : Nat → Prop) (fs : List Nat) :
    Option (Option (List Val)) → U.State → Prop
  | none, _ => True
  | some _, .idle => True
  | some _, .running _ s t => Keeps S₀ G s ∧ CfgIn G fs (InstrIn G fs) (t.config s)
  | some _, .waiting _ s t _ =>
    Keeps S₀ G s ∧ CfgIn G fs (InstrIn G fs) (t.config s) ∧ ∃ h args, CalloutAt s t h args

theorem kJ_tau (hK : KeptHyp U S₀ G fs hu hf) {P : Profile} {q : Option (Option (List Val))}
    {x y : U.State} (hst : U.Trans P x none y) (hJ : KJ U S₀ G fs q x) : KJ U S₀ G fs q y := by
  rcases q with _ | q
  · trivial
  cases hst with
  | tau hi =>
    obtain ⟨hk, hc⟩ := hJ
    obtain ⟨hc', hfe⟩ := internalP_cfgIn instrIn_plainOK hi (hk.closed hK.closed) hc
    refine ⟨⟨fun a ha => ?_, ?_⟩, hc'⟩
    · rw [← hk.1 a ha]
      exact congrArg (·[a]?) hfe
    · have h₁ := hc'.1
      rwa [Thread.config_store] at h₁

/-- The kept sentence on a Proponent move whose client event is `skip`. -/
theorem kept_skip {ha : Nat} {q : Option (List Val)} {m : Move UImp (untypedSig U.X)}
    (hP : ¬ Move.IsO m) (hs : uClientEv ha hu hf m = .skip) :
    (keptSpec (ι := U.X) S₀ G ha hu hf).step (some q) m = some (some q) := by
  rw [keptSpec, guardO_ok (fun hO => absurd hO hP)]
  show (handleStep .client q (uClientEv ha hu hf m)).map some = _
  rw [hs, handleStep_skip]
  rfl

theorem kJ_call (hK : KeptHyp U S₀ G fs hu hf) {ha : Nat} {q : Option (List Val)}
    (f : U.F.Op) : ∃ q', (keptSpec (ι := U.X) S₀ G ha hu hf).step (some q) (.inr (.ask f)) = some q' ∧
      KJ U S₀ G fs q' (.running f f.store (U.init f)) := by
  by_cases hok : EnvKeeps S₀ G (.inr (.ask f) : Move UImp (untypedSig U.X))
  · refine ⟨some q, ?_, hok.1, invoke_cfgIn hok.1.2 (hK.exports _) hok.2⟩
    rw [keptSpec, guardO_ok (fun _ => hok)]
    show (handleStep .client q .skip).map some = _
    rw [handleStep_skip]
    rfl
  · exact ⟨none, guardO_bad trivial hok, trivial⟩

theorem kJ_ucall (hK : KeptHyp U S₀ G fs hu hf) {ha : Nat} {q : Option (List Val)}
    {f : U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (callout : CalloutAt s t h args) (hJ : KJ U S₀ G fs (some q) (.running f s t)) :
    ∃ q', (keptSpec (ι := U.X) S₀ G ha hu hf).step (some q) (.inl (.ask ⟨h, s, args⟩)) = some q' ∧
      KJ U S₀ G fs q' (.waiting f s t ⟨h, s, args⟩) := by
  obtain ⟨hk, hc⟩ := hJ
  have hnu : h ≠ hu := callout_ne callout hc (hk.avoids hK.avoidsU)
  have hnf : h ≠ hf := callout_ne callout hc (hk.avoids hK.avoidsF)
  refine ⟨some q, kept_skip (m := .inl (.ask ⟨h, s, args⟩)) (fun hO => False.elim hO) ?_, hk, hc,
    h, args, callout⟩
  simp [uClientEv, hnu, hnf]

theorem kJ_uret {ha : Nat} {q : Option (List Val)} {f : U.F.Op} {s : Store Nat} {t : Thread}
    {e : U.E.Op} (a : UReply) (hJ : KJ U S₀ G fs (some q) (.waiting f s t e)) :
    ∃ q', (keptSpec (ι := U.X) S₀ G ha hu hf).step (some q) (.inl (.ans e a)) = some q' ∧
      KJ U S₀ G fs q' (.running f a.store (resumeResult s t a.result)) := by
  by_cases hok : EnvKeeps S₀ G (.inl (.ans e a) : Move UImp (untypedSig U.X))
  · obtain ⟨hk, hc, h, args, E, a', hd⟩ := hJ
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1
      (uClientSpec_oTotal (ι := U.X) ha hu hf q (.inl (.ans e a)) trivial)
    refine ⟨some q', ?_, hok.1, ?_⟩
    · rw [keptSpec, guardO_ok (fun _ => hok), hq']
      rfl
    · have h₁ := resume_cfgIn hc hok.2
      rw [resumeResult_config hd] at h₁ ⊢
      exact ⟨hok.1.2, h₁.2.1, h₁.2.2⟩
  · exact ⟨none, guardO_bad trivial hok, trivial⟩

/-- **The protocol invariant** of the untyped system for the kept sentence (every profile). -/
def keptInv (hK : KeptHyp U S₀ G fs hu hf) (ha : Nat) (P : Profile) :
    LTSInv (U.lts P) (keptSpec (ι := U.X) S₀ G ha hu hf) where
  J := KJ U S₀ G fs
  init := trivial
  tau hst hJ := kJ_tau hK hst hJ
  vis := by
    intro q x o y hst hJ
    rcases q with _ | q
    · exact ⟨none, rfl, trivial⟩
    change U.Trans P x (some o) y at hst
    cases hst with
    | call f => exact kJ_call hK f
    | ucall callout => exact kJ_ucall hK callout hJ
    | uret a => exact kJ_uret a hJ
    | @oret f s t r final =>
      exact ⟨some q, kept_skip (m := .inr (.ans f ⟨s, r⟩)) (fun hO => False.elim hO) rfl, trivial⟩

/-- **Clients that cannot reach `use` or `free` satisfy the kept sentence**, every profile. -/
theorem kept_accepts (hK : KeptHyp U S₀ G fs hu hf) (ha : Nat) (P : Profile) :
    ∀ p ∈ U.strategy P, (keptSpec (ι := U.X) S₀ G ha hu hf).Accepts p :=
  untyped_accepts (keptInv hK ha P) (keptSpec_oTotal S₀ G ha hu hf)

end Kept

/-- The checker's facts for `exAlloc`, by kernel evaluation. -/
theorem exAlloc_keptHyp : KeptHyp exAllocU exAllocS (· ∈ allocG) [0, 1, 2, 3] 1 2 :=
  ⟨closedB_sound alloc_closed, avoidsB_sound alloc_avoids_use, avoidsB_sound alloc_avoids_free,
    fun _ => by simp [allocG, exAllocU]⟩

/-- **The allocating client satisfies the kept sentence**, every profile. -/
theorem exAlloc_client (P : Profile) :
    ∀ p ∈ exAllocU.strategy P, (keptSpec (ι := Unit) exAllocS (· ∈ allocG) 0 1 2).Accepts p :=
  kept_accepts exAlloc_keptHyp 0 P

/-- **Without the guard the allocating client is refuted too**, every profile: its untyped
instance is that of `exUse`, and Opponent may hand it `exUse`'s store. -/
theorem exAlloc_refuted_unkept (P : Profile) :
    ¬ ∀ p ∈ exAllocU.strategy P, (uClientSpec (ι := Unit) 0 1 2).Accepts p :=
  exUse_refuted P

/-! ### `exAlloc` does call `alloc` (every profile) -/

theorem alloc_len : exAllocS.funcs.length = 4 := by decide +kernel
theorem alloc_mod : (exAllocS.funcs.map fun fi => fi.module.funcs) = [[], [], [], [0, 1, 2, 3]] := by
  decide +kernel

theorem isAllocBody_code {fi : FuncInst Nat} (h : isAllocBody fi = true) :
    ∃ (t : TypeIdx) (y : FuncIdx), fi.code = .wasm ⟨t, [], [.call y]⟩ ∧ y.toNat = 0 := by
  unfold isAllocBody at h
  split at h
  · rename_i t y hc
    exact ⟨t, y, hc, by simpa using h⟩
  · cases h

/-- The shape of the instantiated store of `exAlloc`. -/
structure AllocShape (fa fr : FuncInst Nat) (t : TypeIdx) (y : FuncIdx) : Prop where
  get₀ : exAllocS.funcs[0]? = some fa
  get₃ : exAllocS.funcs[3]? = some fr
  codeA : fa.code = .host 0
  tyA : Expand fa.type allocTy
  codeR : fr.code = .wasm ⟨t, [], [.call y]⟩
  tyR : Expand fr.type allocTy
  hy : y.toNat = 0
  modR : fr.module.funcs = [0, 1, 2, 3]

theorem allocShape : ∃ fa fr t y, AllocShape fa fr t y := by
  obtain ⟨f₀, f₁, f₂, f₃, hf⟩ := list_four alloc_len
  have hhost := hf ▸ alloc_host
  have hexp := hf ▸ alloc_expand
  have hmod := hf ▸ alloc_mod
  have hbody := hf ▸ alloc_body
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hhost hexp hmod hbody
  obtain ⟨t, y, hc, hy⟩ := isAllocBody_code hbody.2.2.2.1
  exact ⟨f₀, f₃, t, y, by rw [hf]; rfl, by rw [hf]; rfl, hostCode?_code hhost.1,
    Expand.iff.mpr hexp.1, hc, Expand.iff.mpr hexp.2.2.2.1, hy, hmod.2.2.2.1⟩

/-- The code at the callout `alloc`. -/
abbrev allocCode (fa fr : FuncInst Nat) : List Admin :=
  [.frame 1 (Frame.forCall fr.module [] [])
    [.label 1 [] (vals [] ++ [.ref (.func 0), .callRefType fa.type])]]

/-- **`allocPlay` is a play of `exAlloc`**, every profile. -/
theorem allocPlay_mem (P : Profile) : allocPlay ∈ exAllocU.strategy P := by
  obtain ⟨fa, fr, t, y, h⟩ := allocShape
  have h₁ : Step P (fun _ _ _ _ => False) (invoke exAllocS 3 [])
      ⟨exAllocS, {}, [.frame 1 (Frame.forCall fr.module [] [])
        [.label 1 [] [.plain (.call y)]]]⟩ :=
    Step.callRefFunc (s := exAllocS) (f := {})
      (c := .callRefType ((exAllocS.funcs[3]?.map FuncInst.type).getD default)) (vs := [])
      trivial h.get₃ h.tyR rfl h.codeR
  have hx : (Frame.forCall fr.module [] []).module.funcs[y.toNat]? = some 0 := by
    simp [Frame.forCall, h.modR, h.hy]
  have h₂ : Step P (fun _ _ _ _ => False) ⟨exAllocS, Frame.forCall fr.module [] [],
      [.plain (.call y)]⟩ ⟨exAllocS, Frame.forCall fr.module [] [],
      vals [] ++ [.ref (.func 0), .callRefType fa.type]⟩ := Step.call hx h.get₀
  have h₂' := Step.ctxtFrame (f := {}) (n := 1) (Step.ctxtLabel (n := 1) (cont := []) h₂)
  have i₂ : InternalP P (exAllocS, Thread.active {} [.frame 1 (Frame.forCall fr.module [] [])
      [.label 1 [] [.plain (.call y)]]]) (exAllocS, .active {} (allocCode fa fr)) :=
    ⟨_, _, rfl, h₂'⟩
  have hreach : Reach P (exAllocS, .pending 3 []) (exAllocS, .active {} (allocCode fa fr)) :=
    (Relation.ReflTransGen.single (⟨_, _, rfl, h₁⟩ : InternalP P (exAllocS, Thread.pending 3 [])
      (exAllocS, .active {} [.frame 1 (Frame.forCall fr.module [] [])
        [.label 1 [] [.plain (.call y)]]]))).tail i₂
  have hr : decompose? exAllocS (vals [] ++ [.ref (.func 0), .callRefType fa.type]) =
      some (.top [] [], 0, 0, []) :=
    decompose?_redex (c := .callRefType fa.type) trivial h.get₀ h.tyA rfl h.codeA
  have hsl : splitVals [Admin.label 1 [] (vals [] ++ [.ref (.func 0), .callRefType fa.type])]
      = ([], [.label 1 [] (vals [] ++ [.ref (.func 0), .callRefType fa.type])]) :=
    splitVals_vals_cons (vs := []) rfl []
  have hsf : splitVals (allocCode fa fr) = ([], allocCode fa fr) :=
    splitVals_vals_cons (vs := []) rfl []
  have hco : CalloutAt exAllocS (.active {} (allocCode fa fr)) 0 [] := by
    refine ⟨.frame [] 1 (Frame.forCall fr.module [] []) (.label [] 1 [] (.top [] []) []) [], 0, ?_⟩
    show decompose? exAllocS (allocCode fa fr) = _
    rw [decompose?_of_split hsf]
    simp only [decompHead]
    rw [decompose?_of_split hsl]
    simp only [decompHead, hr, Option.map_some]
  refine UInstance.mem_strategy_iff.2 ⟨.waiting ⟨(), exAllocS, []⟩ exAllocS
    (.active {} (allocCode fa fr)) ⟨0, exAllocS, []⟩, ?_⟩
  exact .vis (UInstance.Trans.call _) ((run_of_reach (U := exAllocU) _ hreach).append
    (.vis (UInstance.Trans.ucall hco) (.nil _)))

end Silmaril.Wasm.Resource.ExternExamples
