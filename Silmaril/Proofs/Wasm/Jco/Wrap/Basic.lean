module

public import Silmaril.Wasm.Jco.Wrap.Defs
public import Silmaril.Wasm.Jco.Adaptor.Thms
public import Silmaril.Wasm.Component.ABI.Thms

/-!
# The monadic construction: proofs

* `exec_gets`: `local.get 0 … local.get (n-1)` pushes the first `n` locals;
* `specParams_length`: the C convention passes `(flatParams ps).length` flat parameters;
* `callRef_realloc`, `lowerParams_wrap`: the canonical lowering through the adaptor's
  `cabi_realloc` is the C convention's copy through `alloc`;
* `run_plain`, `run_out`: the export shims forward to `M`, with an out-pointer when the result is
  in memory;
* `canonCall_wrap`: the lift of world function `i` behaves as `specCall`;
* `find_liftsFrom`, `wrap_callExport`: the component's exports are the world's functions.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val)

variable (M : CoreInst) (md : Meta)

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

theorem specBytes_length (limit : Nat) (bs : List UInt8) :
    Returns (md.specBytes M limit bs) fun xs => xs.length = 2 :=
  returns_bind returns_check fun _ _ => returns_bind (returns_true _) fun _ _ =>
    returns_bind (returns_true _) fun _ _ => returns_bind (returns_true _) fun _ _ =>
      returns_pure rfl

theorem specParam_length (t : PTy) (v : PVal) :
    Returns (md.specParam M t v) fun xs => xs.length = t.flat.length := by
  cases t <;> cases v
  case val.val t v =>
    by_cases hc : t.check v = true
    · have hl : (t.lower v).length = t.flat.length := by
        rw [← ValTy.lower_types t v hc, List.length_map]
      simp only [Meta.specParam, hc, RM.check_true, RM.pure_bind]
      exact returns_pure (P := fun xs : List Flat => xs.length = (PTy.val t).flat.length) hl
    · simp only [Bool.not_eq_true] at hc
      simp only [Meta.specParam, hc, RM.check_false, RM.fail_bind]
      exact returns_fail
  case string.string => exact specBytes_length M md _ _
  case bytes.bytes => exact specBytes_length M md _ _
  all_goals exact returns_fail

theorem specParams_length : ∀ (ps : List PTy) (vs : List PVal),
    Returns (md.specParams M ps vs) fun xs => xs.length = (flatParams ps).length
  | [], [] => returns_pure rfl
  | t :: ts, v :: vs => by
    refine returns_bind (specParam_length M md t v) fun a ha =>
      returns_bind (specParams_length ts vs) fun b hb => returns_pure ?_
    simp only [flatParams, List.length_append, ha, hb]
  | [], _ :: _ | _ :: _, [] => returns_fail

theorem callRef_realloc (a b c d : Flat) :
    (wrap md).callRef M (.adapt 0) [a, b, c, d] = M.call md.alloc [d, c] := by
  simp [Comp.callRef, wrap, adaptorOf, AFn.run, reallocShim, exec_cons, AInstr.step, RM.bind_assoc]

theorem lowerBytes_wrap (limit : Nat) (bs : List UInt8) :
    lowerBytes M ((wrap md).callRef M (.adapt 0)) limit bs = md.specBytes M limit bs := by
  simp only [lowerBytes, Meta.specBytes, callRef_realloc]

theorem lowerParams_wrap : ∀ (ps : List PTy) (vs : List PVal),
    lowerParams M ((wrap md).callRef M (.adapt 0)) ps vs = md.specParams M ps vs
  | [], [] => rfl
  | t :: ts, v :: vs => by
    have hp : lowerParam M ((wrap md).callRef M (.adapt 0)) t v = md.specParam M t v := by
      cases t <;> cases v <;> simp only [lowerParam, Meta.specParam, lowerBytes_wrap]
    simp only [lowerParams, Meta.specParams, hp, lowerParams_wrap ts vs]
  | [], _ :: _ | _ :: _, [] => rfl

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

/-- The instructions of an out-pointer shim after the allocation. -/
def outRest (name : String) (n : Nat) : List AInstr :=
  .localSet n :: (gets (n + 1) ++ [.call name (n + 1), .localGet n])

theorem outShimBody_eq (alloc name : String) (n : Nat) :
    outShimBody alloc name n = [.i32Const 8, .i32Const 4, .call alloc 2] ++ outRest name n := by
  simp [outShimBody, outRest]

theorem exec_alloc (alloc : String) (ls : List Flat) :
    exec M [.i32Const 8, .i32Const 4, .call alloc 2] ⟨ls, []⟩ =
      (M.call alloc [i32n 8, i32n 4] >>= fun r => pure ⟨ls, r.reverse⟩) := by
  simp [exec_cons, AInstr.step]

theorem set_last (xs : List Flat) (a b : Flat) : (xs ++ [a]).set xs.length b = xs ++ [b] := by
  simp

theorem exec_outRest (name : String) (xs : List Flat) (p : BitVec 32) :
    exec M (outRest name xs.length) ⟨xs ++ [i32n 0], [Flat.i32 p]⟩ =
      (M.call name (xs ++ [Flat.i32 p]) >>= fun rs =>
        exec M [.localGet xs.length] ⟨xs ++ [Flat.i32 p], rs.reverse⟩) := by
  have hlen : (xs ++ [Flat.i32 p]).length = xs.length + 1 := by simp
  have hset : (AInstr.localSet xs.length).step M ⟨xs ++ [i32n 0], [Flat.i32 p]⟩ =
      pure ⟨xs ++ [Flat.i32 p], []⟩ := by
    rw [step_localSet M (by simp), set_last]
  have hgets : exec M (gets (xs.length + 1)) ⟨xs ++ [Flat.i32 p], []⟩ =
      pure ⟨xs ++ [Flat.i32 p], (xs ++ [Flat.i32 p]).reverse⟩ := by
    rw [exec_gets M _ _ _ (by simp), ← hlen, List.take_length, List.append_nil]
  have hcall : (AInstr.call name (xs.length + 1)).step M
        ⟨xs ++ [Flat.i32 p], (xs ++ [Flat.i32 p]).reverse⟩ =
      (M.call name (xs ++ [Flat.i32 p]) >>= fun rs => pure ⟨xs ++ [Flat.i32 p], rs.reverse⟩) := by
    have hd : (xs ++ [Flat.i32 p]).reverse.drop (xs.length + 1) = [] :=
      List.drop_eq_nil_of_le (by simp)
    rw [step_call M name _ (by simp), ← hlen, take_reverse_full, hlen, hd]
    simp
  rw [outRest, exec_cons, hset, RM.pure_bind, exec_append, hgets, RM.pure_bind, exec_cons, hcall,
    RM.bind_assoc]
  simp only [RM.pure_bind]

theorem exec_get_out (xs : List Flat) (o : Flat) :
    exec M [.localGet xs.length] ⟨xs ++ [o], []⟩ = pure ⟨xs ++ [o], [o]⟩ := by
  rw [exec_cons, step_localGet M (v := o) (by simp), RM.pure_bind, exec_nil]

theorem run_out (hC : md.Conforms M) (s : Sig) (hs : s ∈ md.world) (h : inMem s.result = true)
    (xs : List Flat) (hx : xs.length = (flatParams s.params).length) :
    (exportShim md s).run M xs =
      (M.call md.alloc [i32n 8, i32n 4] >>= fun r => RM.ofOption (single32? r) >>= fun p =>
        M.call s.name (xs ++ [Flat.i32 p]) >>= fun _ => pure [Flat.i32 p]) := by
  have hfn : exportShim md s =
      { params := xs.length, locals := 1, body := outShimBody md.alloc s.name xs.length } := by
    simp only [exportShim, h, hx]; rfl
  have hstart : (exportShim md s).run M xs =
      (M.call md.alloc [i32n 8, i32n 4] >>= fun r =>
        exec M (outRest s.name xs.length) ⟨xs ++ [i32n 0], r.reverse⟩ >>= fun f =>
          pure f.stack.reverse) := by
    rw [hfn]
    simp only [AFn.run, beq_self_eq_true, RM.check_true, RM.pure_bind, List.replicate_one,
      outShimBody_eq, exec_append, exec_alloc, RM.bind_assoc]
  rw [hstart]
  refine RM.bind_congr_returns (hC.alloc _) ?_
  rintro r ⟨p, rfl⟩
  show (exec M (outRest s.name xs.length) ⟨xs ++ [i32n 0], [Flat.i32 p]⟩ >>= fun f =>
      pure f.stack.reverse) = (pure p >>= fun p =>
        M.call s.name (xs ++ [Flat.i32 p]) >>= fun _ => pure [Flat.i32 p])
  rw [exec_outRest, RM.bind_assoc, RM.pure_bind]
  refine RM.bind_congr_returns (hC.outPtr s hs h _) ?_
  rintro rs rfl
  rw [List.reverse_nil, exec_get_out, RM.pure_bind]
  rfl

theorem callRef_shim (i : Nat) (s : Sig) (hi : md.world[i]? = some s) :
    (wrap md).callRef M (.adapt (i + 1)) = (exportShim md s).run M := by
  funext xs
  simp [Comp.callRef, wrap, adaptorOf, hi]

/-- The lift of world function `i` behaves as the C convention's call. -/
theorem canonCall_wrap (hC : md.Conforms M) (i : Nat) (s : Sig) (hi : md.world[i]? = some s)
    (vs : List PVal) :
    canonCall M ((wrap md).callRef M (.adapt 0)) ((wrap md).callRef M (.adapt (i + 1))) s vs =
      md.specCall M s vs := by
  have hs : s ∈ md.world := List.mem_of_getElem? hi
  rw [callRef_shim M md i s hi]
  unfold canonCall Meta.specCall
  rw [lowerParams_wrap]
  refine RM.bind_congr_returns (specParams_length M md _ _) ?_
  intro xs hx
  cases h : inMem s.result
  · rw [run_plain M md s h xs hx]
    simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [run_out M md hC s hs h xs hx]
    simp only [↓reduceIte, RM.bind_assoc, RM.pure_bind]

/-- Looking up an export of the lifts of `ws`, numbered from `k`. -/
theorem find_liftsFrom (name : String) : ∀ (k : Nat) (ws : List Sig),
    (∀ s, ws.find? (·.name == name) = some s → ∃ i, ws[i]? = some s ∧
      (liftsFrom k ws).find? (·.sig.name == name) = some ⟨s, .adapt (k + i + 1), .adapt 0⟩) ∧
    (ws.find? (·.name == name) = none → (liftsFrom k ws).find? (·.sig.name == name) = none)
  | _, [] => ⟨fun _ h => by simp at h, fun _ => rfl⟩
  | k, w :: ws => by
    by_cases hw : (w.name == name) = true
    · have hs0 : ∀ s, (w :: ws).find? (·.name == name) = some s → w = s := by
        intro s hs
        simpa [List.find?_cons, hw] using hs
      have hl0 : (liftsFrom k (w :: ws)).find? (·.sig.name == name) =
          some ⟨w, .adapt (k + 0 + 1), .adapt 0⟩ := by
        simp [liftsFrom, hw]
      refine ⟨fun s hs => ⟨0, ?_, ?_⟩, fun hn => absurd hn (by simp [hw])⟩
      · rw [← hs0 s hs]
        rfl
      · rw [← hs0 s hs, hl0]
    · have hw' : (w.name == name) = false := by simpa using hw
      have ih := find_liftsFrom name (k + 1) ws
      refine ⟨fun s hs => ?_, fun hn => ?_⟩
      · have hs' : ws.find? (·.name == name) = some s := by simpa [List.find?_cons, hw'] using hs
        obtain ⟨i, hi, hl⟩ := ih.1 s hs'
        refine ⟨i + 1, by simpa using hi, ?_⟩
        have hidx : k + 1 + i + 1 = k + (i + 1) + 1 := by omega
        simpa [liftsFrom, List.find?_cons, hw', hidx] using hl
      · have hn' : ws.find? (·.name == name) = none := by simpa [List.find?_cons, hw'] using hn
        simpa [liftsFrom, List.find?_cons, hw'] using ih.2 hn'

/-- **The behaviour theorem.** The wrapper component's export `name` behaves as world function
`name` of `M` under the C convention. -/
theorem wrap_callExport (hC : md.Conforms M) (name : String) (vs : List PVal) :
    (wrap md).callExport M name vs = md.spec M name vs := by
  have hl : (wrap md).lifts = liftsFrom 0 md.world := rfl
  unfold Comp.callExport Meta.spec
  rw [hl]
  cases hf : md.world.find? (·.name == name) with
  | none => rw [(find_liftsFrom name 0 md.world).2 hf]
  | some s =>
    obtain ⟨i, hi, hfind⟩ := (find_liftsFrom name 0 md.world).1 s hf
    have hidx : 0 + i + 1 = i + 1 := by omega
    rw [hfind]
    simp only [hidx]
    exact canonCall_wrap M md hC i s hi vs

end Silmaril.Proofs.Wasm.Jco
