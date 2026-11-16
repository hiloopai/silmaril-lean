module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.TrapClose

/-!
# Determinism of logged runs, and the end of a resolved canonical run (proofs)

The backward direction (Core to `wasmEvFunXP`) is read off the forward one (`evalLXPh_fwd`,
`evalLXPh_trap`) by determinism, in the deterministic profile `SingleThreaded.profile o`:

* `evRunN_event_det`, `evRun_det_end`: two labelled runs from the same configuration with the
  **same log** end alike, when one end has no step at all and the other has no host-free step;
* `ends_stuck`, `ends_decompose`: a final form (`Outcome.Ends`) has no step, under any host, and
  is not at a host call;
* `ResX`: the calls of a logged canonical run all resolved against the closure, or a resolved
  prefix and then a call whose callee traps (`TrapRes`), the run ending in a trap;
* `EndOK`: a Core configuration is the final form of a logged canonical result (`MatchP`), or a
  trap for a trapping result;
* `match_end`: a resolved logged run of checked code whose Core run, with the same log, ends with
  no host-free step, ends as `EndOK` says.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Determinism of logged runs -/

/-- **At a host call, a labelled run whose log starts with the event `e` goes through the answer
of `e`**, strictly fewer steps after it. -/
theorem evRunN_event_det {n : Nat} {K K₁ c : Config H} {e : Call (wasmHostSig H)}
    {q : List (Call (wasmHostSig H))} (he : HEvStep P host K (some e) K₁)
    (h : EvRunN P host n K (e :: q) c) : ∃ m < n, EvRunN P host m K₁ q c := by
  obtain ⟨E, a, hd, hs, -, hK₁⟩ := he
  suffices key : ∀ n y cs, EvRunN P host n y cs c → y = K → cs = e :: q →
      ∃ m < n, EvRunN P host m K₁ q c from key _ _ _ h rfl rfl
  clear h
  intro n y cs hy
  induction hy with
  | refl => intro _ h; cases h
  | @silent m y z c₃ cs hs' hrest ih =>
    intro hy hcs
    subst hy
    rcases hs' with h' | ⟨rfl, -⟩
    · exact (noFree_of_decompose hd h').elim
    · obtain ⟨m', hm', h'⟩ := ih rfl hcs
      exact ⟨m', by omega, h'⟩
  | @event m y z c₃ e' cs hs' hrest _ =>
    intro hy hcs
    subst hy
    obtain ⟨rfl, rfl⟩ := List.cons.inj hcs
    obtain ⟨E', a', hd', -, -, hz⟩ := hs'
    rw [hd] at hd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl, -⟩ := hd'
    have hzK : z = K₁ := by rw [hz, hK₁]
    subst hzK
    exact ⟨m, by omega, hrest⟩

/-- **Two labelled runs, the second's log extending the first's, end alike** (deterministic
profile): a run to a configuration with no step at all, and a counted run to a configuration with
no host-free step whose log extends the first log, end at the same configuration, and the second
log adds nothing. -/
theorem evRun_det_end_pre {o : GrowOracle} {K X : Config H} {q : List (Call (wasmHostSig H))}
    (hf : EvRun (profile o) host K q X) (hX : ∀ c', ¬ Step (profile o) host X c') :
    ∀ {n : Nat} {c : Config H} {q' : List (Call (wasmHostSig H))},
      EvRunN (profile o) host n K (q ++ q') c →
      (∀ c', ¬ Step (profile o) Det.noHost c c') → c = X ∧ q' = [] := by
  induction hf with
  | refl K =>
    intro n c q' h hend
    obtain ⟨h₁, h₂⟩ := evRunN_of_stuck hX h
    exact ⟨h₁, by simpa using h₂⟩
  | @silent K K₁ X q hs hrest ih =>
    intro n c q' h hend
    rcases hs with hs | ⟨rfl, -⟩
    · obtain ⟨m, -, h'⟩ := evRunN_through h hend (d := K₁) hs
      exact ih hX h' hend
    · exact ih hX h hend
  | @event K K₁ X e q hs hrest ih =>
    intro n c q' h hend
    obtain ⟨m, -, h'⟩ := evRunN_event_det hs (by simpa using h)
    exact ih hX h' hend

/-- **Two labelled runs with the same log end alike** (deterministic profile). -/
theorem evRun_det_end {o : GrowOracle} {K X : Config H} {q : List (Call (wasmHostSig H))}
    (hf : EvRun (profile o) host K q X) (hX : ∀ c', ¬ Step (profile o) host X c') {n : Nat}
    {c : Config H} (h : EvRunN (profile o) host n K q c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') : c = X :=
  (evRun_det_end_pre hf hX (q' := []) (by simpa using h) hend).1

/-! ## Final forms -/

theorem ends_labelExit {o : Outcome} {c : List Admin} (he : o.Ends c) :
    ∃ out, LabelExit 0 [] c out := by
  rcases o with ws | ⟨l, ws⟩ | ws | _ | a | ⟨ws, a, r⟩ | ⟨ws, r⟩
  · rw [he]; exact ⟨_, .vals ws⟩
  · obtain ⟨x, rest, rfl, rfl⟩ := he
    have e : vals ws ++ .plain (.br x) :: rest = vals ws ++ [.plain (.br x)] ++ rest := by simp
    rw [e]
    by_cases hx : x.toNat = 0
    · have := LabelExit.brZero (n := 0) (cont := []) (vs' := ws) (vs := []) (rest := rest) hx rfl
      rw [show vals ws ++ vals [] = vals ws by simp [vals]] at this
      exact ⟨_, this⟩
    · exact ⟨_, .brSucc (vs := ws) (rest := rest) (Nat.pos_of_ne_zero hx)⟩
  · obtain ⟨rest, rfl⟩ := he
    have e : vals ws ++ .plain .return_ :: rest = vals ws ++ [.plain .return_] ++ rest := by simp
    rw [e]
    exact ⟨_, .ret⟩
  · rw [he]; exact ⟨_, .trap⟩
  · rw [he]; exact ⟨_, .throw a⟩
  · obtain ⟨hr, rest, rfl⟩ := he
    have := LabelExit.returnCall (n := 0) (cont := []) (vs := ws ++ [.ref (.func a)]) (rest := rest)
      hr
    rw [show vals (ws ++ [.ref (.func a)]) ++ [r] ++ rest = vals ws ++ .ref (.func a) :: r :: rest
      by simp [vals, Val.toAdmin]] at this
    exact ⟨_, this⟩
  · obtain ⟨hr, rest, rfl⟩ := he
    have := LabelExit.returnCall (n := 0) (cont := []) (vs := ws ++ [.ref .null]) (rest := rest) hr
    rw [show vals (ws ++ [.ref .null]) ++ [r] ++ rest = vals ws ++ .ref .null :: r :: rest
      by simp [vals, Val.toAdmin]] at this
    exact ⟨_, this⟩

/-- **A final form has no step**, under any host. -/
theorem ends_stuck {o : Outcome} {c : List Admin} (he : o.Ends c) (s : Store H) (f : Frame) :
    ∀ c', ¬ Step P host ⟨s, f, c⟩ c' := by
  obtain ⟨out, hx⟩ := ends_labelExit he
  exact fun c' => labelExit_stuck hx c'

/-- A final form is not at a host call. -/
theorem ends_decompose {o : Outcome} {c : List Admin} (he : o.Ends c) (s : Store H) :
    decompose? s c = none := by
  obtain ⟨out, hx⟩ := ends_labelExit he
  exact decompose?_labelExit hx

/-- No host-free step and not at a host call: no step at all. -/
theorem noStep_of {c : Config H} (hend : ∀ c', ¬ Step P Det.noHost c c')
    (hd : decompose? c.store c.code = none) : ∀ c', ¬ Step P host c c' := by
  intro c' h
  rcases Step.split_host h with h | ⟨E, a, hh, args, hdc, -⟩
  · exact hend c' h
  · rw [hd] at hdc; cases hdc

/-! ## Resolved logged runs and their ends -/

/-- The closure. -/
abbrev Cl : (wasmHShape H).ClosedMod := Shape.close wasmHOpenXP

/-- **A trapping resolution of a log**: a prefix resolved to `q₁`, then a call whose callee traps
in the closure with the host events `c₁`; anything after it is not resolved. -/
def TrapRes (l : List (OCall H)) (cs : List (Call (wasmHostSig H))) : Prop :=
  ∃ (l₁ l₂ : List (OCall H)) (g : Nat) (args : List Val) (s₁ : Store H) (b : List Val ⊕ Nat)
    (s₂ : Store H) (q₁ c₁ : List (Call (wasmHostSig H))),
    l = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂ ∧ Shape.SubstPre Cl (l₁.map OCall.lift) q₁ ∧
      (c₁, .trap) ∈ Cl g s₁ args ∧ cs = q₁ ++ c₁

/-- **The resolution of a logged run's calls**: all of them by returning callees, or a trapping
resolution of a trapping run. -/
def ResX (l : List (OCall H)) (r : Store H × Frame × POut) (cs : List (Call (wasmHostSig H))) :
    Prop :=
  Shape.SubstPre Cl (l.map OCall.lift) cs ∨ (r.2.2 = .flow .trap ∧ TrapRes l cs)

/-- **A Core configuration ends as a logged result**: its final form matches the result
(`MatchP`), or the result traps and so does the configuration. -/
def EndOK (r : Store H × Frame × POut) (c : Config H) : Prop :=
  (∃ o : Outcome, o.Ends c.code ∧ MatchP r c.store c.frame o) ∨
    (r.2.2 = .flow .trap ∧ c.code = [.trap])

theorem trapRes_prepend {l₀ l : List (OCall H)} {q₀ cs : List (Call (wasmHostSig H))}
    (h₀ : Shape.SubstPre Cl (l₀.map OCall.lift) q₀) (h : TrapRes l cs) :
    TrapRes (l₀ ++ l) (q₀ ++ cs) := by
  obtain ⟨l₁, l₂, g, args, s₁, b, s₂, q₁, c₁, rfl, h₁, hc, rfl⟩ := h
  refine ⟨l₀ ++ l₁, l₂, g, args, s₁, b, s₂, q₀ ++ q₁, c₁, by simp, ?_, hc, by simp⟩
  rw [List.map_append]
  exact substPre_append.2 ⟨q₀, q₁, rfl, h₀, h₁⟩

theorem trapRes_append {l l' : List (OCall H)} {cs : List (Call (wasmHostSig H))}
    (h : TrapRes l cs) : TrapRes (l ++ l') cs := by
  obtain ⟨l₁, l₂, g, args, s₁, b, s₂, q₁, c₁, rfl, h₁, hc, rfl⟩ := h
  exact ⟨l₁, l₂ ++ l', g, args, s₁, b, s₂, q₁, c₁, by simp, h₁, hc, rfl⟩

theorem resPre_append {l₁ l₂ : List (OCall H)} {q₁ q₂ : List (Call (wasmHostSig H))}
    (h₁ : Shape.SubstPre Cl (l₁.map OCall.lift) q₁) (h₂ : Shape.SubstPre Cl (l₂.map OCall.lift) q₂) :
    Shape.SubstPre Cl ((l₁ ++ l₂).map OCall.lift) (q₁ ++ q₂) := by
  rw [List.map_append]
  exact substPre_append.2 ⟨q₁, q₂, rfl, h₁, h₂⟩

/-- A resolved prefix in front of a resolution. -/
theorem resX_prepend {l₀ l : List (OCall H)} {r : Store H × Frame × POut}
    {q₀ cs : List (Call (wasmHostSig H))} (h₀ : Shape.SubstPre Cl (l₀.map OCall.lift) q₀)
    (h : ResX l r cs) : ResX (l₀ ++ l) r (q₀ ++ cs) := by
  rcases h with h | ⟨ht, h⟩
  · exact .inl (resPre_append h₀ h)
  · exact .inr ⟨ht, trapRes_prepend h₀ h⟩

/-- A resolution of an escaping sub-run, for the same log. -/
theorem resX_of_esc {l : List (OCall H)} {r r' : Store H × Frame × POut}
    {cs : List (Call (wasmHostSig H))} (h : ResX l r cs) (he : r'.2.2 = r.2.2) : ResX l r' cs := by
  rcases h with h | ⟨ht, h⟩
  · exact .inl h
  · exact .inr ⟨he.trans ht, h⟩

/-- A resolution of a trap is a trapping resolution of any trapping result. -/
theorem resX_trap {l : List (OCall H)} {r r' : Store H × Frame × POut}
    {cs : List (Call (wasmHostSig H))} (h : ResX l r cs) (hr : r.2.2 = .flow .trap)
    (hr' : r'.2.2 = .flow .trap) : ResX l r' cs :=
  resX_of_esc h (hr'.trans hr.symm)

section End

variable {tags : List TagInst} {o : GrowOracle}

/-- **The end of a resolved logged run** (deterministic profile): the Core run of checked code
with the same log as a resolved logged run of it, to an end with no host-free step, ends as the
run does. -/
theorem match_end (hH : NativeHostSlice host) (hE : HostSliceE tags host) {s : Store H}
    {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {cs : List (Call (wasmHostSig H))} {c : Config H} {n : Nat}
    {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hd : EvalLXPh s f stk es l r) (hres : ResX l r cs) (hcons : Cons host cs)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hc : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some out)
    (ha : EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') : EndOK r c := by
  rcases hres with hq | ⟨ht, l₁, l₂, g, args, s₁, b, s₂, q₁, c₁, rfl, hq₁, htr, rfl⟩
  · obtain ⟨-, -, -, cl⟩ := full_run (P := profile o) hH hE hd
      (substPre_mono (close_le_goodCX hH hE) hq) hcons hts
    obtain ⟨s', f', c', oc, hrun, he, hm⟩ := cl hS hc
    obtain rfl := evRun_det_end hrun (ends_stuck he s' f') ha hend
    exact .inl ⟨oc, he, hm⟩
  · rw [cons_append] at hcons
    have hz := trapAt_of_trapC (P := profile o) (ans := (b, s₂))
      (close_le_trapC (tags := tags) (P := profile o) hH hE g s₁ args htr) hcons.2
    have cl : CoreLT tags (profile o) host s f stk es (q₁ ++ c₁) :=
      evalLXPh_trap (P := profile o) hH hE hd l₁ _ l₂ rfl q₁ c₁
        (substPre_mono (close_le_goodCX hH hE) hq₁) hz (cons_append.2 hcons) hts
    obtain ⟨s', f', c', oc, hrun, he, rfl⟩ := cl hS hc
    obtain rfl := evRun_det_end hrun (ends_stuck he s' f') ha hend
    exact .inr ⟨ht, he⟩

/-- **The end of a resolved logged run, the Core log extending its log**: no further event. -/
theorem match_end_pre (hH : NativeHostSlice host) (hE : HostSliceE tags host) {s : Store H}
    {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {cs cs' : List (Call (wasmHostSig H))} {c : Config H} {n : Nat}
    {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hd : EvalLXPh s f stk es l r) (hres : ResX l r cs) (hcons : Cons host cs)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hc : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some out)
    (ha : EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ (cs ++ cs') c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') : cs' = [] ∧ EndOK r c := by
  rcases hres with hq | ⟨ht, l₁, l₂, g, args, s₁, b, s₂, q₁, c₁, rfl, hq₁, htr, rfl⟩
  · obtain ⟨-, -, -, cl⟩ := full_run (P := profile o) hH hE hd
      (substPre_mono (close_le_goodCX hH hE) hq) hcons hts
    obtain ⟨s', f', c', oc, hrun, he, hm⟩ := cl hS hc
    obtain ⟨rfl, rfl⟩ := evRun_det_end_pre hrun (ends_stuck he s' f') ha hend
    exact ⟨rfl, .inl ⟨oc, he, hm⟩⟩
  · rw [cons_append] at hcons
    have hz := trapAt_of_trapC (P := profile o) (ans := (b, s₂))
      (close_le_trapC (tags := tags) (P := profile o) hH hE g s₁ args htr) hcons.2
    have cl : CoreLT tags (profile o) host s f stk es (q₁ ++ c₁) :=
      evalLXPh_trap (P := profile o) hH hE hd l₁ _ l₂ rfl q₁ c₁
        (substPre_mono (close_le_goodCX hH hE) hq₁) hz (cons_append.2 hcons) hts
    obtain ⟨s', f', c', oc, hrun, he, rfl⟩ := cl hS hc
    obtain ⟨rfl, rfl⟩ := evRun_det_end_pre hrun (ends_stuck he s' f') ha hend
    exact ⟨rfl, .inr ⟨ht, he⟩⟩

end End

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
