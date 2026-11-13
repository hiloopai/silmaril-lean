module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Call

/-!
# Calls and the ends of labels on Core 3.0

`call_run`: a call statement that `bexec` runs ends normally, with the results in their locals.
`lab_exit`: how a label (`block`, `if`, `loop`) ends after its body ended with `outCode o`
followed by any code (`junk`) the body did not reach: normally (`label-vals`), by a branch to
it (`br-label-zero`, which runs the label's continuation), by a branch further out
(`br-label-succ`), or by `return` (`return-label`); `labOut` is `KDrop.dexec.dlab` on the way
the body ended.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 upd)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix eCode sCode callCode biFn)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma nl : Nat}

theorem stackA_nil : stackA [] = ([] : List Admin) := rfl

theorem stackA_one (v : W) : stackA [v] = [(Val.i32 v).toAdmin] := rfl

theorem bexec_call {b : BI} {args : List E} {dst : List Nat} {f : Nat} {s s' : DSt} {o : Out}
    (h : bexec nl (.call b args dst) f s = some (o, s')) :
    ∃ as, args.mapM (cev nl s) = some as ∧ bcall nl b as dst s = some (o, s') := by
  cases hm : args.mapM (cev nl s) with
  | none => simp [bexec, hm] at h
  | some as => exact ⟨as, rfl, by simpa [bexec, hm] using h⟩

theorem bcall_inv {b : BI} {as dst : List Nat} {s s' : DSt} {o : Out}
    (h : bcall nl b as dst s = some (o, s')) :
    memOK MSZ b as = true ∧ ∃ q' m' res, bi b as (s.st, s.rp) s.m = some (q', m', res) ∧
      dst.length = res.length ∧ (∀ d ∈ dst, d < nl) ∧ (∀ r ∈ res, r < M32) ∧ o = .norm ∧
      s' = { s with st := q'.1, rp := q'.2, m := m', l := setLs s.l dst res } := by
  unfold bcall at h
  split at h
  · rename_i hok
    split at h
    · rename_i q' m' res hbi
      split at h
      · rename_i hc
        have he : (Out.norm, { s with st := q'.1, rp := q'.2, m := m', l := setLs s.l dst res }) =
            (o, s') := Option.some.inj h
        exact ⟨hok, q', m', res, hbi, hc.1, hc.2.1, hc.2.2, (Prod.mk.inj he).1.symm,
          (Prod.mk.inj he).2.symm⟩
      · cases h
    · cases h
  · cases h

/-- A `stream.read` or `stream.write` call: the result goes to the local `d`. -/
theorem call_rw {cs : Store H} {F : Frame} {s : DSt} (h : Rel hb nl ma cs F s) {b : BI}
    (hbrw : b = .streamRead ∨ b = .streamWrite) {args : List E} {as : List Nat}
    (hm : args.mapM (cev nl s) = some as) (hok : memOK MSZ b as = true) {q' : HQ}
    {m' : Nat → Nat} {d r : Nat} (hbi : bi b as (s.st, s.rp) s.m = some (q', m', [r]))
    (hd : d < nl) (hr : r < M32) (rest : List Admin) :
    ∃ cs' F', Rel hb nl ma cs' F' { s with st := q'.1, rp := q'.2, m := m', l := setLs s.l [d] [r] } ∧
      F'.module = F.module ∧ cs'.funcs = cs.funcs ∧
      HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, (sCode (.call b args [d])).map Admin.plain ++ rest⟩)
        (q', ⟨cs', F', rest⟩) := by
  obtain ⟨has, ra⟩ := args_run (Pf := Pf) (q := (s.st, s.rp)) h args hm
  obtain ⟨cs₁, hm₁, hg₁, hf₁, rh⟩ := host_run (Pf := Pf) h has hbi hok (.plain (.localSet (ix d)) :: rest)
  have hR₁ : Rel hb nl ma cs₁ F { s with st := q'.1, rp := q'.2, m := m' } := rel_mem h hm₁ hg₁ hf₁ rfl rfl
  obtain ⟨hix, hR₂⟩ := rel_setL hR₁ hd hr
  have hcode : sCode (.call b args [d]) =
      (args.map eCode).flatten ++ [Instr.call (ix (biFn b)), Instr.localSet (ix d)] := by
    rcases hbrw with rfl | rfl <;> rfl
  have e₀ : (sCode (.call b args [d])).map Admin.plain ++ rest = stackA [] ++
      ((args.map eCode).flatten.map Admin.plain ++
        (.plain (.call (ix (biFn b))) :: .plain (.localSet (ix d)) :: rest)) := by
    rw [hcode]; simp [stackA_nil]
  have ra' := ra [] (.plain (.call (ix (biFn b))) :: .plain (.localSet (ix d)) :: rest)
  rw [List.append_nil] at ra'
  have rl : HSteps Pf hb ma (q', ⟨cs₁, F, stackA ([r].map w).reverse ++ .plain (.localSet (ix d)) :: rest⟩)
      (q', ⟨cs₁, F.setLocal (ix d) (Val.i32 (w r)), rest⟩) := by
    simpa [stackA_nil] using r_lset (Pf := Pf) (hb := hb) (ma := ma) (q := q') (s := cs₁) (v := w r) hix [] rest
  exact ⟨cs₁, _, hR₂, rfl, hf₁, e₀ ▸ ra'.trans (rh.trans rl)⟩

/-- A drop: no result. -/
theorem call_drop {cs : Store H} {F : Frame} {s : DSt} (h : Rel hb nl ma cs F s) {b : BI}
    (hbd : b = .dropR ∨ b = .dropW) {args : List E} {as : List Nat}
    (hm : args.mapM (cev nl s) = some as) (hok : memOK MSZ b as = true) {q' : HQ}
    {m' : Nat → Nat} (hbi : bi b as (s.st, s.rp) s.m = some (q', m', [])) (rest : List Admin) :
    ∃ cs' F', Rel hb nl ma cs' F' { s with st := q'.1, rp := q'.2, m := m', l := setLs s.l [] [] } ∧
      F'.module = F.module ∧ cs'.funcs = cs.funcs ∧
      HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, (sCode (.call b args [])).map Admin.plain ++ rest⟩)
        (q', ⟨cs', F', rest⟩) := by
  obtain ⟨has, ra⟩ := args_run (Pf := Pf) (q := (s.st, s.rp)) h args hm
  obtain ⟨cs₁, hm₁, hg₁, hf₁, rh⟩ := host_run (Pf := Pf) h has hbi hok rest
  have hR₁ : Rel hb nl ma cs₁ F { s with st := q'.1, rp := q'.2, m := m' } := rel_mem h hm₁ hg₁ hf₁ rfl rfl
  have hcode : sCode (.call b args []) = (args.map eCode).flatten ++ [Instr.call (ix (biFn b))] := by
    rcases hbd with rfl | rfl <;> rfl
  have e₀ : (sCode (.call b args [])).map Admin.plain ++ rest = stackA [] ++
      ((args.map eCode).flatten.map Admin.plain ++ (.plain (.call (ix (biFn b))) :: rest)) := by
    rw [hcode]; simp [stackA_nil]
  have ra' := ra [] (.plain (.call (ix (biFn b))) :: rest)
  rw [List.append_nil] at ra'
  have rh' : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA (as.map w).reverse ++
      .plain (.call (ix (biFn b))) :: rest⟩) (q', ⟨cs₁, F, rest⟩) := by simpa [stackA_nil] using rh
  exact ⟨cs₁, F, hR₁, rfl, hf₁, e₀ ▸ ra'.trans rh'⟩

/-- **A built-in call** that `bexec` runs: its Core code, `KCoreEmit.callCode`, ends normally
with the host state, memory and result locals `bexec` gives. -/
theorem call_run {cs : Store H} {F : Frame} {s : DSt} (h : Rel hb nl ma cs F s) {b : BI}
    {args : List E} {dst : List Nat} {f : Nat} {o : Out} {s' : DSt}
    (hx : bexec nl (.call b args dst) f s = some (o, s')) (rest : List Admin) :
    o = .norm ∧ ∃ cs' F', Rel hb nl ma cs' F' s' ∧ F'.module = F.module ∧ cs'.funcs = cs.funcs ∧
      HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, (sCode (.call b args dst)).map Admin.plain ++ rest⟩)
        ((s'.st, s'.rp), ⟨cs', F', rest⟩) := by
  obtain ⟨as, hm, hbc⟩ := bexec_call hx
  obtain ⟨hok, q', m', res, hbi, hlen, hdl, hrl, rfl, rfl⟩ := bcall_inv hbc
  refine ⟨rfl, ?_⟩
  rcases (bi_shape hbi).2 with ⟨⟨r, rfl⟩, hbrw⟩ | ⟨rfl, hbd⟩
  · obtain ⟨d, rfl⟩ : ∃ d, dst = [d] := by
      match dst, hlen with
      | [d], _ => exact ⟨d, rfl⟩
    exact call_rw h hbrw hm hok hbi (hdl d (by simp)) (hrl r (by simp)) rest
  · obtain rfl : dst = [] := List.eq_nil_of_length_eq_zero hlen
    exact call_drop h hbd hm hok hbi rest

/-! ## The end of a label -/

/-- `dexec.dlab` on how the body ended. -/
def labOut : Out → Out
  | .br 0 => .norm
  | .br (k + 1) => .br k
  | o => o

theorem dlab_some (o : Out) (s : DSt) : dexec.dlab (some (o, s)) = some (labOut o, s) := by
  rcases o with _ | _ | _ | k
  all_goals first | rfl | (cases ‹Nat› <;> rfl)

theorem labelPred_ix {k : Nat} (hk : k + 1 < M32) : labelPred (ix (k + 1)) = ix k := by
  unfold labelPred
  congr 1
  apply Fin.ext
  show (ix (k + 1) : LabelIdx).toNat - 1 = k % 2 ^ 32
  rw [ix_toNat hk, Nat.mod_eq_of_lt (by unfold M32 at hk; omega)]
  rfl

theorem step_app {q : HQ} {s : Store H} {f : Frame} {X Y : List Admin}
    (h : Step Pf noHost ⟨s, f, X⟩ ⟨s, f, Y⟩) (rest : List Admin) :
    HSteps Pf hb ma (q, ⟨s, f, X ++ rest⟩) (q, ⟨s, f, Y ++ rest⟩) :=
  hsteps_app rest (hcore h)

/-- **The end of a label** whose body ended with `outCode o`, then code it did not reach. -/
theorem lab_exit {q : HQ} {s : Store H} {f : Frame} (cont : List Instr) {o : Out}
    (h0 : o = .br 0 → cont = []) (hk : ∀ k, o = .br k → k < M32) (junk : List Admin)
    (hj : o = .norm → junk = []) (rest : List Admin) :
    HSteps Pf hb ma (q, ⟨s, f, .label 0 cont (outCode o ++ junk) :: rest⟩)
      (q, ⟨s, f, outCode (labOut o) ++ rest⟩) := by
  rcases o with _ | k | v
  · rw [hj rfl]
    exact step_app (Step.labelVals (vs := [])) rest
  · cases k with
    | zero =>
      rw [h0 rfl]
      have := Step.brLabelZero (P := Pf) (host := noHost) (s := s) (f := f) (n := 0) (cont := [])
        (vs' := []) (vs := []) (l := ix 0) (rest := junk) rfl rfl
      exact step_app (by simpa [vals, outCode, expression] using this) rest
    | succ k =>
      have hk1 := hk (k + 1) rfl
      have := Step.brLabelSucc (P := Pf) (host := noHost) (s := s) (f := f) (n := 0) (cont := cont)
        (vs := []) (l := ix (k + 1)) (rest := junk) (by rw [ix_toNat hk1]; omega)
      rw [labelPred_ix hk1] at this
      exact step_app (by simpa [vals, outCode] using this) rest
  · have := Step.returnLabel (P := Pf) (host := noHost) (s := s) (f := f) (n := 0) (cont := cont)
      (vs := [Val.i32 (w v)]) (rest := junk)
    exact step_app (by simpa [vals, outCode] using this) rest

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
