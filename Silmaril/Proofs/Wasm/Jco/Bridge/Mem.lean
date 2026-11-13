module

public import Silmaril.Wasm.Jco.Bridge.Defs
public import Silmaril.Wasm.Jco.Wrap.Thms
public import Silmaril.Wasm.Jco.Thin.Canon.Thms
public import Silmaril.Wasm.Component.ABI.Thms

/-!
# The memory-based side of the bridge: proofs

On memory-free worlds the adaptor's export shims only forward (`run_plain`), and lowering
component values is `checkLower` (`lowerParams_val`), so:

* `wrap_memFree`: `wrap md` follows the C convention for **every** core instance, without the
  `Conforms` hypothesis of `wrap_correct` (the allocator is never called);
* `spec_pure`: over the instance of a pure module, the C convention is `RM.ofOption` of
  `pureCall`.

`exec_gets` and `take_reverse_full` restate (and re-prove) lemmas of the `Wrap` proofs, which
this topic does not import.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Bridge

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val checkLower lowerArgs)
open Silmaril.Wasm.Jco.Bridge (PMod pureCall liftRes)

variable (M : CoreInst) (md : Meta)

/-! ## The export shims -/

theorem exec_gets : ∀ (n : Nat) (ls st : List Flat), n ≤ ls.length →
    exec M (gets n) ⟨ls, st⟩ = pure ⟨ls, (ls.take n).reverse ++ st⟩
  | 0, ls, st, _ => by simp [gets]
  | n + 1, ls, st, h => by
    have hlt : n < ls.length := by omega
    have hn : ls[n]? = some ls[n] := List.getElem?_eq_getElem hlt
    have hg : gets (n + 1) = gets n ++ [.localGet n] := by
      simp only [gets, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    have htake : (ls.take (n + 1)).reverse ++ st = ls[n] :: ((ls.take n).reverse ++ st) := by
      simp only [List.take_add_one, hn, Option.toList_some, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [hg, exec_append, exec_gets n ls st (by omega), RM.pure_bind, exec_cons,
      step_localGet M hn, RM.pure_bind, exec_nil, htake]

theorem take_reverse_full (xs : List Flat) : (xs.reverse.take xs.length).reverse = xs := by
  rw [← List.length_reverse, List.take_length, List.reverse_reverse]

theorem run_plain (s : Sig) (h : inMem s.result = false) (xs : List Flat)
    (hx : xs.length = (flatParams s.params).length) :
    (exportShim md s).run M xs = M.call s.name xs := by
  have hfn : exportShim md s =
      { params := xs.length, body := gets xs.length ++ [.call s.name xs.length] } := by
    simp only [exportShim, h, hx]; rfl
  have hstep : (AInstr.call s.name xs.length).step M ⟨xs, xs.reverse⟩ =
      (M.call s.name xs >>= fun rs => pure ⟨xs, rs.reverse⟩) := by
    have hd : xs.reverse.drop xs.length = [] := List.drop_eq_nil_of_le (by simp)
    rw [step_call M s.name _ (by simp)]
    simp [take_reverse_full, hd]
  rw [hfn]
  simp only [AFn.run, beq_self_eq_true, RM.check_true, RM.pure_bind, List.replicate_zero,
    List.append_nil, exec_append, exec_gets M xs.length xs [] le_rfl, List.take_length,
    exec_cons, hstep, RM.bind_assoc, exec_nil, List.reverse_reverse, RM.bind_pure]

/-! ## Lowering on the memory-free fragment -/

theorem lowerParam_length (R : List Flat → RM M.St (List Flat)) (t : ValTy) (v : PVal) :
    Returns (lowerParam M R (.val t) v) fun xs => xs.length = t.flat.length := by
  cases v with
  | val v =>
    by_cases hc : t.check v = true
    · have hl : (t.lower v).length = t.flat.length := by
        rw [← ValTy.lower_types t v hc, List.length_map]
      simp only [lowerParam, hc, RM.check_true, RM.pure_bind]
      exact returns_pure (P := fun xs : List Flat => xs.length = t.flat.length) hl
    · simp only [Bool.not_eq_true] at hc
      simp only [lowerParam, hc, RM.check_false, RM.fail_bind]
      exact returns_fail
  | string _ => exact returns_fail
  | bytes _ => exact returns_fail

theorem lowerParams_length (R : List Flat → RM M.St (List Flat)) :
    ∀ (ps : List PTy) (vs : List PVal), ps.all PTy.memFree = true →
      Returns (lowerParams M R ps vs) fun xs => xs.length = (flatParams ps).length
  | [], [], _ => returns_pure rfl
  | .val t :: ts, v :: vs, h => by
    have hts : ts.all PTy.memFree = true := by simpa [PTy.memFree] using h
    refine returns_bind (lowerParam_length M R t v) fun a ha =>
      returns_bind (lowerParams_length R ts vs hts) fun b hb => returns_pure ?_
    simp only [flatParams, PTy.flat, List.length_append, ha, hb]
  | .string :: _, _ :: _, h | .bytes :: _, _ :: _, h => by simp [PTy.memFree] at h
  | [], _ :: _, _ | _ :: _, [], _ => returns_fail

theorem ofOption_bind_pure {σ α : Type} (o : Option (List α)) (a : List α) :
    (RM.ofOption o >>= fun b => (pure (a ++ b) : RM σ (List α))) =
      RM.ofOption (o.map (a ++ ·)) := by
  cases o <;> simp

theorem lowerParams_val (R : List Flat → RM M.St (List Flat)) :
    ∀ (ps : List PTy) (vs : List Val), ps.all PTy.memFree = true →
      lowerParams M R ps (vs.map PVal.val) =
        RM.ofOption (checkLower (ps.map Silmaril.Wasm.Jco.Bridge.PTy.toVal) vs)
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | .val t :: ts, v :: vs, h => by
    have hts : ts.all PTy.memFree = true := by simpa [PTy.memFree] using h
    have ih := lowerParams_val R ts vs hts
    by_cases hc : t.check v = true
    · have e : checkLower (Silmaril.Wasm.Jco.Bridge.PTy.toVal (.val t) ::
            ts.map Silmaril.Wasm.Jco.Bridge.PTy.toVal) (v :: vs) =
          (checkLower (ts.map Silmaril.Wasm.Jco.Bridge.PTy.toVal) vs).map (t.lower v ++ ·) := by
        simp [checkLower, ValTy.checkList, hc, Silmaril.Wasm.Jco.Bridge.PTy.toVal, lowerArgs,
          ValTy.lowerList]
      simp only [List.map_cons, lowerParams, lowerParam, hc, RM.check_true, RM.pure_bind, ih,
        ofOption_bind_pure]
      rw [e]
    · have e : checkLower (Silmaril.Wasm.Jco.Bridge.PTy.toVal (.val t) ::
            ts.map Silmaril.Wasm.Jco.Bridge.PTy.toVal) (v :: vs) = none := by
        simp [checkLower, ValTy.checkList, hc, Silmaril.Wasm.Jco.Bridge.PTy.toVal]
      simp only [Bool.not_eq_true] at hc
      simp only [List.map_cons, lowerParams, lowerParam, hc, RM.check_false, RM.fail_bind, e]
      rfl
  | .string :: _, _ :: _, h | .bytes :: _, _ :: _, h => by simp [PTy.memFree] at h

/-! ## `wrap` on memory-free worlds -/

theorem callRef_shim (i : Nat) (s : Sig) (hi : md.world[i]? = some s) :
    (wrap md).callRef M (.adapt (i + 1)) = (exportShim md s).run M := by
  funext xs
  have hf : (adaptorOf md).funcs[i + 1]? = some (s.name, exportShim md s) := by
    simp [adaptorOf, hi]
  simp only [Comp.callRef, wrap, hf]

/-- A lift of `wrap md` at a memory-free world function is the C convention's call, for every
instance. -/
theorem canonCall_wrap_memFree (i : Nat) (s : Sig) (hi : md.world[i]? = some s)
    (hp : s.params.all PTy.memFree = true) (hr : inMem s.result = false) (vs : List PVal) :
    canonCall M ((wrap md).callRef M (.adapt 0)) ((wrap md).callRef M (.adapt (i + 1))) s vs =
      md.specCall M s vs := by
  have hrun : ∀ xs, xs.length = (flatParams s.params).length →
      (wrap md).callRef M (.adapt (i + 1)) xs = M.call s.name xs := fun xs hx => by
    rw [callRef_shim M md i s hi, run_plain M md s hr xs hx]
  have hb := bind_congr_returns (lowerParams_length M ((wrap md).callRef M (.adapt 0)) s.params vs hp)
    (k := fun xs => (wrap md).callRef M (.adapt (i + 1)) xs >>= liftResult M s.result)
    (k' := fun xs => M.call s.name xs >>= liftResult M s.result) fun xs hx => by rw [hrun xs hx]
  unfold canonCall
  rw [hb]
  simp only [Meta.specCall, hr, Bool.false_eq_true, ↓reduceIte,
    lowerParams_memFree M md _ s.params vs hp]

theorem find_liftsFrom (name : String) : ∀ (k : Nat) (ws : List Sig) (l : Lift),
    (liftsFrom k ws).find? (·.sig.name == name) = some l →
      ∃ i s, ws[i]? = some s ∧ ws.find? (·.name == name) = some s ∧
        l = ⟨s, .adapt (k + i + 1), .adapt 0⟩
  | _, [], _, h => by cases h
  | k, s :: ws, l, h => by
    by_cases hn : (s.name == name) = true
    · have e : l = ⟨s, .adapt (k + 1), .adapt 0⟩ := by simpa [liftsFrom, hn] using h.symm
      exact ⟨0, s, rfl, by simp [hn], e⟩
    · have h' : (liftsFrom (k + 1) ws).find? (·.sig.name == name) = some l := by
        simpa [liftsFrom, hn] using h
      obtain ⟨i, s', hi, hf, e⟩ := find_liftsFrom name (k + 1) ws l h'
      refine ⟨i + 1, s', hi, by simp [hn, hf], ?_⟩
      rw [e]
      congr 2
      omega

theorem find_liftsFrom_none (name : String) : ∀ (k : Nat) (ws : List Sig),
    (liftsFrom k ws).find? (·.sig.name == name) = none → ws.find? (·.name == name) = none
  | _, [], _ => rfl
  | k, s :: ws, h => by
    by_cases hn : (s.name == name) = true
    · simp [liftsFrom, hn] at h
    · have h' : (liftsFrom (k + 1) ws).find? (·.sig.name == name) = none := by
        simpa [liftsFrom, hn] using h
      simpa [hn] using find_liftsFrom_none name (k + 1) ws h'

/-- **On memory-free worlds `wrap` follows the C convention, for every instance** (no
`Conforms` hypothesis: the allocator is never called). -/
theorem wrap_memFree (h : md.memFree = true) (name : String) (vs : List PVal) :
    (wrap md).callExport M name vs = md.spec M name vs := by
  unfold Comp.callExport Meta.spec
  rcases hl : (wrap md).lifts.find? (·.sig.name == name) with _ | l
  · rw [hl, find_liftsFrom_none name 0 md.world hl]
  · obtain ⟨i, s, hi, hf, rfl⟩ := find_liftsFrom name 0 md.world l hl
    have hs := memFree_mem md h (List.mem_of_getElem? hi)
    rw [hl, hf, Nat.zero_add]
    exact canonCall_wrap_memFree M md i s hi hs.1 hs.2 vs

/-! ## Pure modules -/

theorem liftResult_val (r : Option PTy) (hr : inMem r = false) (ys : List Flat) :
    liftResult M r ys = RM.ofOption (liftRes r ys) := by
  rcases r with _ | (t | _ | _)
  · cases ys <;> rfl
  · rcases ht : t.lift ys with _ | ⟨v, _ | ⟨y, rest⟩⟩ <;> simp [liftResult, liftRes, ht]
  · cases hr
  · cases hr

theorem ofOption_bind {σ α β : Type} (o : Option α) (f : α → Option β) :
    (RM.ofOption o >>= fun a => (RM.ofOption (f a) : RM σ β)) = RM.ofOption (o.bind f) := by
  cases o <;> simp

/-- Over the instance of a pure module, a memory-free world function under the C convention is
`pureCall`. -/
theorem specCall_pure (m : PMod) (s : Sig) (hp : s.params.all PTy.memFree = true)
    (hr : inMem s.result = false) (vs : List Val) :
    md.specCall m.inst s (vs.map PVal.val) = RM.ofOption (pureCall m s vs) := by
  have hl : md.specParams m.inst s.params (vs.map PVal.val) =
      RM.ofOption (checkLower (s.params.map Silmaril.Wasm.Jco.Bridge.PTy.toVal) vs) := by
    rw [← lowerParams_memFree m.inst md (m.inst.call "") s.params _ hp,
      lowerParams_val m.inst _ s.params vs hp]
  have hc : ∀ xs, m.inst.call s.name xs = RM.ofOption (m.callN s.name xs) := fun _ => rfl
  simp only [Meta.specCall, hr, Bool.false_eq_true, ↓reduceIte, hl, hc,
    liftResult_val m.inst s.result hr, ofOption_bind, pureCall]

end Silmaril.Proofs.Wasm.Jco.Bridge
