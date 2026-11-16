module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackSplit
public import Silmaril.Wasm.Interp.PProgress.Thms
public import Silmaril.Wasm.Interp.XProgress.Thms

/-!
# The logged backward simulation of the canonical relation: statements and glue (proofs)

In the deterministic profile `SingleThreaded.profile o`, a labelled Core run (`EvRunN`, with its
exact host-event log `cs`) of a typed problem (`Interp.TypedP tags`) to an end with no host-free
step that is not at a host call is a resolved logged canonical run (`BackOut`): an `EvalLXPh`
run whose calls resolve against the closure to exactly `cs` (`ResX`), ending as the Core run
does (`EndOK`, read off the forward simulation by determinism, `mkOut`).

* `BackG n es`: the statement for runs of at most `n` steps of the trees `es`;
* `CallG n`: the statement for runs of at most `n` steps from a typed call in any `call_ref` form
  (`callCode`): the callee returns in the closure, with a prefix of the log, and the run goes on
  strictly shorter from its answer (`ansCode`), or the callee traps in the closure with the
  whole log.

Glue: `wp_end` (a host-free run to a final form is where a labelled run ends, with no events),
`subst_pre`, `subst_pre_then` (resolutions from resolved prefixes), and the closure behaviours of
a Wasm callee (`close_wasm_flow`, `close_wasm_trap`, `close_wasm_tail`, `close_wasm_tailTrap`) and
of a host callee (`close_hostX`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {host : HostSemantics H}

/-! ## The statements -/

/-- The Core code of a tree problem. -/
abbrev tcode (stk : List Val) (es : List Binaryen.BExpr) : List Admin :=
  vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)

/-- **The logged backward conclusion**: a logged canonical run whose calls resolve to exactly
`cs`, ending as the Core configuration `c`. -/
def BackOut (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr)
    (cs : List (Call (wasmHostSig H))) (c : Config H) : Prop :=
  ∃ (l : List (OCall H)) (r : Store H × Frame × POut), EvalLXPh s f stk es l r ∧ ResX l r cs ∧
    EndOK r c

/-- **The logged backward simulation of trees**, for runs of `n` steps. -/
def BackG (tags : List TagInst) (o : GrowOracle) (host : HostSemantics H) (n : Nat)
    (es : List Binaryen.BExpr) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (c : Config H) (cs : List (Call (wasmHostSig H))),
    TypedP tags s f stk es → EvRunN (profile o) host n ⟨s, f, tcode stk es⟩ cs c →
    (∀ c', ¬ Step (profile o) Det.noHost c c') → decompose? c.store c.code = none →
    BackOut s f stk es cs c

/-- **The logged backward conclusion of a call**: the callee returns in the closure with a prefix
of the log, the run going on strictly shorter from its answer; or it traps with the whole log. -/
def CallOut (o : GrowOracle) (host : HostSemantics H) (n : Nat) (s₁ : Store H) (f₁ : Frame)
    (pre : List Val) (a : Nat) (us : List Val) (rest : List Admin)
    (cs : List (Call (wasmHostSig H))) (c : Config H) : Prop :=
  (∃ (q : List (Call (wasmHostSig H))) (b : List Val ⊕ Nat) (s₂ : Store H) (m : Nat)
      (cs₂ : List (Call (wasmHostSig H))), (q, .ret b s₂) ∈ Cl a s₁ us ∧ cs = q ++ cs₂ ∧ m < n ∧
      EvRunN (profile o) host m ⟨s₂, f₁, vals pre ++ ansCode b ++ rest⟩ cs₂ c) ∨
    (cs, .trap) ∈ Cl a s₁ us

/-- **The logged backward simulation of calls**, for runs of `n` steps. -/
def CallG (tags : List TagInst) (o : GrowOracle) (host : HostSemantics H) (n : Nat) : Prop :=
  ∀ (s₁ : Store H) (f₁ : Frame) (pre us : List Val) (a : Nat) (cr : Admin) (rest : List Admin)
    (c : Config H) (cs : List (Call (wasmHostSig H))), cr.IsCallRef → CallChkP tags s₁ a us →
    Sim.ContextTyped ⟨s₁, f₁, callCode pre us a cr rest⟩ →
    EvRunN (profile o) host n ⟨s₁, f₁, callCode pre us a cr rest⟩ cs c →
    (∀ c', ¬ Step (profile o) Det.noHost c c') → decompose? c.store c.code = none →
    CallOut o host n s₁ f₁ pre a us rest cs c

/-! ## Glue -/

section Glue

variable {o : GrowOracle}

/-- **A host-free run to a final form is where a labelled run ends**, with no events. -/
theorem wp_end {s : Store H} {f : Frame} {code : List Admin} {Q : Post H} {n : Nat}
    {cs : List (Call (wasmHostSig H))} {c : Config H}
    (hw : WP (profile o) NH s f code Q) (h : EvRunN (profile o) host n ⟨s, f, code⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') :
    cs = [] ∧ ∃ oc : Outcome, oc.Ends c.code ∧ Q c.store c.frame oc := by
  obtain ⟨s', f', c', oc, hs, he, hq⟩ := hw
  obtain ⟨m, -, h'⟩ := evRunN_through_steps hs h hend
  obtain ⟨rfl, rfl⟩ := evRunN_of_stuck (ends_stuck he s' f') h'
  exact ⟨rfl, oc, he, hq⟩

/-- A host-free run is a run with any host. -/
theorem steps_host {P : Silmaril.Wasm.Numerics.Profile} {c c' : Config H}
    (h : Steps P NH c c') : Steps P host c c' := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (Step.of_noHost host st)

/-- A labelled run passes through a host-free run, counted. -/
theorem through {K T c : Config H} {n : Nat} {cs : List (Call (wasmHostSig H))}
    (hs : Steps (profile o) NH K T) (h : EvRunN (profile o) host n K cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') :
    ∃ m ≤ n, EvRunN (profile o) host m T cs c :=
  evRunN_through_steps hs h hend

/-- The end of a resolved logged run, packaged. -/
theorem mkOut {tags : List TagInst} (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {cs : List (Call (wasmHostSig H))} {c : Config H} {n : Nat}
    (ht : TypedP tags s f stk es)
    (ha : EvRunN (profile o) host n ⟨s, f, tcode stk es⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (hd : EvalLXPh s f stk es l r) (hres : ResX l r cs) : BackOut s f stk es cs c := by
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := ht
  exact ⟨l, r, hd, hres, match_end hH hE hd hres (evRun_consistent (evRunN_evRun ha)) hts hS hc ha hend⟩

/-- The end of a resolved logged run whose log the Core run extends: no further event. -/
theorem mkOut' {tags : List TagInst} (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {cs cs' : List (Call (wasmHostSig H))} {c : Config H} {n : Nat}
    (ht : TypedP tags s f stk es)
    (ha : EvRunN (profile o) host n ⟨s, f, tcode stk es⟩ (cs ++ cs') c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (hd : EvalLXPh s f stk es l r) (hres : ResX l r cs) :
    cs' = [] ∧ BackOut s f stk es cs c := by
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := ht
  have hcons : Cons host cs := (cons_append.1 (evRun_consistent (evRunN_evRun ha))).1
  obtain ⟨h₁, h₂⟩ := match_end_pre hH hE hd hres hcons hts hS hc ha hend
  exact ⟨h₁, l, r, hd, hres, h₂⟩

/-- The end of a resolved logged run whose log the Core run extends, as the whole log. -/
theorem mkOut'' {tags : List TagInst} (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {cs cs' : List (Call (wasmHostSig H))} {c : Config H} {n : Nat}
    (ht : TypedP tags s f stk es)
    (ha : EvRunN (profile o) host n ⟨s, f, tcode stk es⟩ (cs ++ cs') c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (hd : EvalLXPh s f stk es l r) (hres : ResX l r cs) : BackOut s f stk es (cs ++ cs') c := by
  obtain ⟨rfl, h⟩ := mkOut' hH hE ht ha hend hd hres
  simpa using h

end Glue

/-! ## Resolutions -/

universe u

theorem subst_pre {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod} {R : Type u}
    {L : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} (h : Shape.SubstPre c L q)
    (e : End sh.S R) : Shape.Subst c L e (q, e) := by
  induction h with
  | nil => exact .nil e
  | ext _ ih => exact .ext ih
  | int hc _ ih => exact .int hc ih

theorem subst_pre_then {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod} {R : Type u}
    {L M : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} {e : End sh.S R}
    {y : CallBeh sh.E sh.S R} (h : Shape.SubstPre c L q) (hm : Shape.Subst c M e y) :
    Shape.Subst c (L ++ M) e (q ++ y.1, y.2) := by
  induction h with
  | nil => simpa using hm
  | ext _ ih => exact .ext ih
  | int hc _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact Shape.Subst.int hc ih

/-- A trapping resolution resolves the log to a trap, whatever the open end. -/
theorem subst_trapRes {l : List (OCall H)} {cs : List (Call (wasmHostSig H))}
    (h : TrapRes l cs) (e : End (Store H) (List Val ⊕ Nat)) :
    Shape.Subst Cl (l.map OCall.lift) e (cs, .trap) := by
  obtain ⟨l₁, l₂, g, args, s₁, b, s₂, q₁, c₁, rfl, h₁, hc, rfl⟩ := h
  rw [List.map_append, List.map_cons]
  have := subst_pre_then h₁ (Shape.Subst.intTrap (rest := l₂.map OCall.lift) (e := e)
    (ans := (b, s₂)) hc)
  exact this

/-! ## Closed behaviours of a callee -/

section Close

variable {s s' s₁ s₂ : Store H} {a a' n : Nat} {us args : List Val} {fi : FuncInst H} {fn : Func}
  {ps rs : List Validation.CValType} {f₂ : Frame} {l : List (OCall H)}
  {q q' : List (Call (wasmHostSig H))}

theorem close_of_open {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H)
      (List Val ⊕ Nat)} {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s us) (hs : Shape.Subst Cl x.1 x.2 y) : y ∈ Cl a s us := by
  show y ∈ Shape.close wasmHOpenXP a s us
  rw [← Shape.resolve_close]
  exact ⟨x, hx, hs⟩

/-- **A Wasm callee whose body ends in a flow**, its calls resolved. -/
theorem close_wasm_flow {bfl fl : Binaryen.Flow} (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l
      (s', f₂, .flow bfl))
    (hres : Shape.SubstPre Cl (l.map OCall.lift) q) (hx : exitFlow rs.length bfl = some fl) :
    (q, endOfFlow fl s') ∈ Cl a s us :=
  close_of_open (.inl ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hf, hcode, hty, hbody, hx, rfl⟩)
    (subst_pre hres _)

/-- **A Wasm callee whose body is cut at a trapping callee.** -/
theorem close_wasm_trap {bfl fl : Binaryen.Flow} (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l
      (s', f₂, .flow bfl))
    (hres : TrapRes l q) (hx : exitFlow rs.length bfl = some fl) : (q, .trap) ∈ Cl a s us :=
  close_of_open (.inl ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hf, hcode, hty, hbody, hx, rfl⟩)
    (subst_trapRes hres _)

/-- **A Wasm callee whose body ends in a pending tail call answered by a returning callee.** -/
theorem close_wasm_tail {b : List Val ⊕ Nat} (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l
      (s₁, f₂, .tail a' args n))
    (hres : Shape.SubstPre Cl (l.map OCall.lift) q) (hz : (q', .ret b s₂) ∈ Cl a' s₁ args) :
    (q ++ q', tailAns rs.length n b s₂) ∈ Cl a s us := by
  refine close_of_open (.inr (.inl ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, hf, hcode, hty,
    hbody, rfl⟩)) ?_
  rw [List.map_append, List.map_cons, List.map_nil]
  have h := subst_pre_then hres (Shape.Subst.int (rest := []) hz
    (Shape.Subst.nil (c := Cl) (tailAns rs.length n b s₂)))
  simp only [List.append_nil] at h
  exact h

/-- **A Wasm callee whose body ends in a pending tail call to a trapping callee.** -/
theorem close_wasm_tailTrap (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l
      (s₁, f₂, .tail a' args n))
    (hres : Shape.SubstPre Cl (l.map OCall.lift) q) (hz : (q', .trap) ∈ Cl a' s₁ args) :
    (q ++ q', .trap) ∈ Cl a s us := by
  refine close_of_open (.inr (.inl ⟨fi, fn, ps, rs, s₁, s₁, f₂, a', n, args, .inr 0, l, hf, hcode,
    hty, hbody, rfl⟩)) ?_
  rw [List.map_append, List.map_cons, List.map_nil]
  exact subst_pre_then hres (Shape.Subst.intTrap (rest := []) hz)

/-- An answered host function is its one host call, in the closure. -/
theorem close_hostX {hh : H} {r : Result} {fl : Binaryen.Flow} (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hx : exitFlow rs.length (resFlow r) = some fl) :
    ([⟨(hh, s, us), (s', r)⟩], endOfFlow fl s') ∈ Cl a s us :=
  close_of_open (.inr (.inr ⟨fi, hh, ps, rs, s', r, fl, hf, hcode, hty, hx, rfl⟩))
    (Shape.Subst.ext (.nil _))

/-- A pending tail call of the function's own arity, answered: the function ends as its callee. -/
theorem tailAns_eq {m : Nat} {b : List Val ⊕ Nat} {s : Store H}
    (hb : ∀ ws, b = .inl ws → ws.length ≤ m) : tailAns m m b s = .ret b s := by
  rcases b with ws | t
  · have hl := hb ws rfl
    simp only [tailAns, ansFlow, CallX.tailFlow, exitFlow, endOfFlow, End.ret.injEq, and_true,
      Sum.inl.injEq]
    rw [List.take_take, Nat.min_self, List.take_of_length_le (by simpa using hl)]
    simp
  · rfl

end Close

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
