module

public import Silmaril.Proofs.Wasm.Auto2.VCGen.Func

/-!
# The VC generator: recursive functions (total correctness)

A function that calls itself is verified with a **recursive callee contract**
and induction on a bound: the specification functions form a family `Fs N`; the caller's
specification `S` is checked against the callee contract `S'` for its own code (an entry
`(x, S', code)` of `S.calls`, where function `x` of the module is the function itself), with

* `S'` asking, under `Fs (N + 1)`, what `S` asks under `Fs N` (`hpre`: for merge sort, the length
  is below `N + 1`), and nothing satisfiable under `Fs 0` (`hbase`);
* `S'` promising, under `Fs (N + 1)`, what `S` promises under `Fs N` (`hpost`).

Then `genFunc_tsound_rec`: if the conditions of `S` are valid under every `Fs N`, the function
meets `fspec (Fs N) S` for total correctness, for every `N`. The other callees are assumed for
every `N`. The proof is an induction on `N`: the call to itself at `N + 1` uses the specification
at `N`, restricted to calls from a store with the same functions (`fspecIn`, which is what
`CallsOK` asks).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCGen

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation (Expand Ty)
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Logic.Hoare (TFSpecAt TSafe FSpec callPost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- `genFunc_tsound` with the callees given for each entry store (instead of `CalleesValid`). -/
theorem genFunc_tsound_calls {F : Fns} {S : FnSpec} {fuel a : Nat} {fi : FuncInst H} {code : Func}
    {ps rs : Ty (.list .val)} (hT : S.total = true) (hcode : fi.code = .wasm code)
    (he : Expand fi.type (.func ps rs)) (hps : S.params.length = ps.length)
    (hrs : S.results.length = rs.length) (hvc : AllValid F (genFunc S code fuel))
    (hC : ∀ s args, (fspec F S a fi).pre s args → CallsOK .total P host F S s fi.module) :
    TFSpecAt P host a (fspec F S a fi) := by
  unfold genFunc at hvc
  split at hvc
  next lts hl =>
    split at hvc
    next hS =>
      refine Silmaril.Wasm.Logic.Hoare.TFSpecAt.of_body (fun s args hpre => hpre.1) hcode he
        (fun s args hpre => ?_) fun s args hpre f vs₀ => ?_
      · obtain ⟨-, -, ρ₀, rfl, -⟩ := hpre
        simp [argsOf, hps]
      · have hcs := hC s args hpre
        obtain ⟨-, -, ρ₀, rfl, hm, hg, hp⟩ := hpre
        exact TSafe.post_mono (body_wp (c := .total) hl hS (fun _ => hT) hvc hcs
          hm hg hp) fun _ _ _ h => bodyPostT_of_postOf hS hrs rfl hm hg (drop_lt_init lts) h
    next => exact (not_allValid_ff hvc).elim
  next => exact (not_allValid_ff hvc).elim

/-- `Callees` only reads the functions of the store. -/
theorem Callees.funcs {S : FnSpec} {fi : FuncInst H} {s s' : Store H} (h : Callees S fi s)
    (hf : s'.funcs = s.funcs) : Callees S fi s' := by
  intro c hc
  obtain ⟨a', fi', ps, rs, hx, hs, hrest⟩ := h c hc
  exact ⟨a', fi', ps, rs, hx, by rw [hf]; exact hs, hrest⟩

/-- Two specifications with the same signature, memory and globals. -/
structure SameShape (S S' : FnSpec) : Prop where
  params : S'.params = S.params
  results : S'.results = S.results
  mem : S'.mem = S.mem
  globals : S'.globals = S.globals

theorem SameShape.argsOf {S S' : FnSpec} (h : SameShape S S') (ρ : Env) :
    argsOf S' ρ = argsOf S ρ := by
  simp only [VCGen.argsOf, h.params]

theorem SameShape.memOk {S S' : FnSpec} (h : SameShape S S') {s : Store H} {mi : ModuleInst}
    {B : ByteArray} : MemOk S' s mi B ↔ MemOk S s mi B := by
  simp only [MemOk, h.mem]

theorem SameShape.globOk {S S' : FnSpec} (h : SameShape S S') {s : Store H} {mi : ModuleInst}
    {ρ : Env} : GlobOk S' s mi ρ ↔ GlobOk S s mi ρ := by
  simp only [GlobOk, h.globals, h.params]

theorem SameShape.upd {S S' : FnSpec} (h : SameShape S S') (s : Store H) (mi : ModuleInst)
    (B : ByteArray) : VCGen.upd S' s mi B = VCGen.upd S s mi B := by
  simp only [VCGen.upd, h.mem]

/-- The callee contract at `N + 1` from the specification at `N`. -/
theorem self_conseq {Fs : Nat → Fns} {S S' : FnSpec} {a : Nat} {fi : FuncInst H} {s₀ : Store H}
    (hsh : SameShape S S') (hcalls : Callees S fi s₀) {N : Nat}
    (hpre : ∀ ρ, S'.preF.den (Fs (N + 1)) ρ ρ → S.preF.den (Fs N) ρ ρ)
    (hpost : ∀ ρ ξ, S.post.den (Fs N) ρ ξ → S'.post.den (Fs (N + 1)) ρ ξ)
    (h : TFSpecAt P host a (fspec (Fs N) S a fi)) :
    TFSpecAt P host a (fspecIn (Fs (N + 1)) S' a fi s₀) := by
  intro s args hp f vs₀ c hc
  obtain ⟨⟨hfi, -, ρ, rfl, hm, hg, hpr⟩, hfs⟩ := hp
  have hp' : (fspec (Fs N) S a fi).pre s (argsOf S' ρ) :=
    ⟨hfi, hcalls.funcs hfs, ρ, hsh.argsOf ρ, hsh.memOk.mp hm, hsh.globOk.mp hg, hpre ρ hpr⟩
  refine Silmaril.Wasm.Logic.Hoare.TSafe.post_mono (h s _ hp' f vs₀ c hc) ?_
  rintro s' f' o ⟨rfl, hq⟩
  refine ⟨rfl, hq.imp ?_ (Or.imp ?_ ?_)⟩
  · rintro ⟨res, rfl, B', G, hs', hG, res', hres, hlen, hty, hρ⟩
    refine ⟨res, rfl, B', G, by rw [hsh.upd]; exact hs', by rw [hsh.globals]; exact hG, res', hres,
      by rw [hsh.results]; exact hlen, by rw [hsh.results]; exact hty, fun ρ' ha hm' hg' => ?_⟩
    exact hpost _ _ (hρ ρ' (ha.trans (hsh.argsOf ρ')) (hsh.memOk.mp hm') (hsh.globOk.mp hg'))
  · rintro ⟨rfl, B', G, -, -, res', h', -⟩
    exact absurd h' (by simp)
  · rintro ⟨a', rfl, B', G, -, -, res', h', -⟩
    exact absurd h' (by simp)

/-- A specification whose precondition is unsatisfiable holds. -/
theorem tfspec_of_not_pre {F : Fns} {S : FnSpec} {a : Nat} {fi : FuncInst H} {s₀ : Store H}
    (h : ∀ ρ, ¬ S.preF.den F ρ ρ) : TFSpecAt P host a (fspecIn F S a fi s₀) := by
  intro s args hp
  obtain ⟨⟨-, -, ρ, -, -, -, hpr⟩, -⟩ := hp
  exact (h ρ hpr).elim

/-- The callees of a recursive function at bound `N`, from its specification at the bound below
(`ih`, unused at `0`, where the recursive contract cannot be called). -/
theorem callsOK_rec {Fs : Nat → Fns} {S S' : FnSpec} {a x : Nat} {fi : FuncInst H} {N : Nat}
    {s : Store H} {args : List Val} (hp : (fspec (Fs N) S a fi).pre s args)
    (hx : fi.module.funcs[x]? = some a) (hself : ∀ e ∈ S.calls, e.1 = x → e.2.1 = S')
    (hrec : ∀ (s₀ : Store H), Callees S fi s₀ →
      TFSpecAt P host a (fspecIn (Fs N) S' a fi s₀))
    (hothers : ∀ e ∈ S.calls, e.1 ≠ x → ∀ a' (fi' : FuncInst H) (ps' rs' : Ty (.list .val)),
      fi'.code = .wasm e.2.2 → Expand fi'.type (.func ps' rs') →
      e.2.1.params.length = ps'.length → e.2.1.results.length = rs'.length →
      TFSpecAt P host a' (fspec (Fs N) e.2.1 a' fi')) :
    CallsOK .total P host (Fs N) S s fi.module := by
  intro e he'
  obtain ⟨a', fi', ps', rs', hx', hf', hcode', hmod', hE', hp', hr'⟩ := hp.2.1 e he'
  refine ⟨a', fi', hx', hf', hmod', ?_⟩
  by_cases hex : e.1 = x
  · rw [hself e he' hex]
    have ha : a' = a := by rw [hex, hx] at hx'; exact (Option.some.inj hx').symm
    subst ha
    have hfi : fi' = fi := Option.some.inj (hf'.symm.trans hp.1)
    subst hfi
    exact hrec s hp.2.1
  · exact SpecOK.fspecIn (c := .total) (hothers e he' hex a' fi' ps' rs' hcode' hE' hp' hr') s

/-- **Soundness for a recursive function** (total correctness; see the module docstring). -/
theorem genFunc_tsound_rec {Fs : Nat → Fns} {S S' : FnSpec} {fuel a x : Nat} {fi : FuncInst H}
    {code : Func} {ps rs : Ty (.list .val)} (hT : S.total = true) (hcode : fi.code = .wasm code)
    (he : Expand fi.type (.func ps rs)) (hps : S.params.length = ps.length)
    (hrs : S.results.length = rs.length) (hx : fi.module.funcs[x]? = some a)
    (hvc : ∀ N, AllValid (Fs N) (genFunc S code fuel))
    (hself : ∀ e ∈ S.calls, e.1 = x → e.2.1 = S') (hsh : SameShape S S')
    (hpre : ∀ N ρ, S'.preF.den (Fs (N + 1)) ρ ρ → S.preF.den (Fs N) ρ ρ)
    (hbase : ∀ ρ, ¬ S'.preF.den (Fs 0) ρ ρ)
    (hpost : ∀ N ρ ξ, S.post.den (Fs N) ρ ξ → S'.post.den (Fs (N + 1)) ρ ξ)
    (hothers : ∀ N, ∀ e ∈ S.calls, e.1 ≠ x → ∀ a' (fi' : FuncInst H) (ps' rs' : Ty (.list .val)),
      fi'.code = .wasm e.2.2 → Expand fi'.type (.func ps' rs') →
      e.2.1.params.length = ps'.length → e.2.1.results.length = rs'.length →
      TFSpecAt P host a' (fspec (Fs N) e.2.1 a' fi')) :
    ∀ N, TFSpecAt P host a (fspec (Fs N) S a fi) := by
  intro N
  induction N with
  | zero =>
    exact genFunc_tsound_calls hT hcode he hps hrs (hvc 0) fun s args hp =>
      callsOK_rec hp hx hself (fun _ _ => tfspec_of_not_pre hbase) (hothers 0)
  | succ N ih =>
    exact genFunc_tsound_calls hT hcode he hps hrs (hvc (N + 1)) fun s args hp =>
      callsOK_rec hp hx hself (fun _ hc => self_conseq hsh hc (hpre N) (hpost N) ih)
        (hothers (N + 1))

end Silmaril.Wasm.Auto2.VCGen
