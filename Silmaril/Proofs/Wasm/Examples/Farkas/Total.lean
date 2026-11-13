module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Complete
public import Silmaril.Wasm.Logic.Total.Thms

@[expose] public section

/-!
# The Farkas checker: total correctness

At every profile and for every host relation (`TWP`, total correctness):

* `row_twp`, `entry_twp` (symbolic execution, `Common.Wp.exec_eq` at `Corr.total`) and
  `check_twp` (`TWP.block` and `TWP.loop` with the invariant `LInv` and the variant
  `nVars - i`): the bodies terminate, with the same results as their `HWP` specifications;
* `tspec_valid`: every export call terminates with typed results from a store holding a
  machine state (`TotPre`), and leaves such a store (`TFSpecAt.of_body`);
* `farkas_total`: every sequence of export calls is a session (each call runs to an answer);
* `farkas_accepts`: for every sequence of calls followed by `check`, there is a session, and
  its `check` answers `1` whenever the calls passed the bounds and loaded a valid certificate;
* `cert_session`: the session of the calls loading `x₀ ≤ 1, -x₀ ≤ -2` with multipliers `1, 1`,
  then `check`, exists and its `check` answers `1`.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Logic.Hoare (TWP TSafe TFSpecAt FSpec labelPostT seqPostT loopPostT bodyPostT
  callPost Exits)
open Silmaril.Wasm.Spec.Multi (Call Session)
open Silmaril.Wasm.Examples.Common (Wp.exec_eq bodyPost)
open Silmaril.Logic.LinArith (WRows)

variable {P : Profile} {host : HostSemantics Nat} {s₀ : Store Nat} {m : Mach}

/-! ## The bodies -/

theorem row_twp (y b : BitVec 64) {Q : Post Nat}
    (hQ : ∀ f', Q (withMach s₀ (rowM m y b)) f' (.normal [])) :
    TWP P host (withMach s₀ m) (Frame.forCall farkasMI [.i64 y, .i64 b] [.i64]) (expression rowBody) Q := by
  rw [frame_row]
  have h := Wp.exec_eq (m := .total) (P := P) (host := host) (vs := []) (rest := []) (Q := Q)
    (exec_row (s₀ := s₀) (m := m) y b) (by simpa using Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := .total) (hQ _))
  simpa using h

theorem entry_twp (hB : m.mem.size = 65536) (j : BitVec 32) (a : BitVec 64) {Q : Post Nat}
    (hQ : ∀ f', Q (withMach s₀ (entryM m j a)) f' (.normal [])) :
    TWP P host (withMach s₀ m) (Frame.forCall farkasMI [.i32 j, .i64 a] [.i32, .i64])
      (expression entryBody) Q := by
  rw [frame_entry]
  have h := Wp.exec_eq (m := .total) (P := P) (host := host) (vs := []) (rest := []) (Q := Q)
    (exec_entry (s₀ := s₀) hB j a) (by simpa using Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := .total) (hQ _))
  simpa using h

/-- The loop counter of a scan frame. -/
def iOf (f : Frame) : Nat :=
  match f.locals with
  | some (.num ⟨.int .i32, i⟩) :: _ => BitVec.toNat i
  | _ => 0

/-- The variant of the scan loop. -/
def scanV (_ : Store Nat) (f : Frame) (_ : List Val) : Nat := nVars - iOf f

theorem tail_twp {Q : Post Nat} {i nz : BitVec 32} {B : ByteArray}
    (hQ : ∀ f', Q (withMach s₀ (checkEnd B)) f' (.normal [Val.i32 (checkRes m nz)])) :
    TWP P host (withMach s₀ { m with mem := B }) (scanFrame i nz) (vals [] ++ expression checkTail) Q := by
  have h := Wp.exec_eq (m := .total) (P := P) (host := host) (vs := []) (rest := []) (Q := Q)
    (exec_tail (s₀ := s₀) (m := { m with mem := B }) i nz)
    (by simpa using Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := .total) (hQ _))
  simpa using h

theorem scanV_lt {i : BitVec 32} (hi : i.toNat < nVars) (nz nz' : BitVec 32) (s s' : Store Nat) :
    scanV s' (scanFrame (i + 1) nz') [] < scanV s (scanFrame i nz) [] := by
  have hi' : i.toNat < 8192 := hi
  have hsucc : (i + 1).toNat = i.toNat + 1 := by
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1]
    omega
  show nVars - (i + 1).toNat < nVars - i.toNat
  rw [hsucc]
  simp only [nVars] at hi ⊢
  omega

/-- One round of the scan loop, for total correctness. -/
theorem loop_twp {Q : Post Nat}
    (hQ : ∀ B nz f', ScanDone m.mem B nz →
      Q (withMach s₀ (checkEnd B)) f' (.normal [Val.i32 (checkRes m nz)]))
    (s : Store Nat) (f : Frame) (vs : List Val) (hI : LInv s₀ m s f vs) :
    TWP P host s f (vals vs ++ expression loopBody)
      (loopPostT 0 [] (LInv s₀ m) scanV (scanV s f vs)
        (labelPostT P host 0 [] [] (seqPostT P host (expression checkTail) Q))) := by
  obtain ⟨rfl, i, nz, B, rfl, rfl, hL⟩ := hI
  rw [loopBody_eq, expression, List.map_append, List.map_cons, ← expression, ← expression,
    ← List.append_assoc]
  refine Wp.exec_eq (m := .total) (vs := []) (exec_test _ i nz) ?_
  refine Silmaril.Wasm.Logic.Hoare.TWP.brIf (us := []) (fun hc => ?_) (fun hc => ?_)
  · -- `i ≥ nVars`: leave the block and run the tail
    have hd : ScanDone m.mem B nz := hL.exit (geU_ne_zero hc)
    refine ⟨[], [], rfl, rfl, ?_⟩
    exact .exit (.normal []) rfl (tail_twp (hQ B nz · hd))
  · -- `i < nVars`: scan slot `i` and go round
    have hi : i.toNat < nVars := geU_eq_zero.1 hc
    rw [expression, List.map_append, ← expression, ← List.append_assoc]
    refine Wp.exec_eq (m := .total) (vs := []) (exec_scan (m := { m with mem := B }) hL.size hi) ?_
    exact Silmaril.Wasm.Logic.Hoare.Wp.br (m := .total)
      ⟨[], [], rfl, rfl, ⟨rfl, i + 1, scanNz B i nz, setSlot B i.toNat 0, rfl, rfl, hL.step hi⟩,
        scanV_lt hi nz _ _ _⟩

/-- **The body of `check`**, for total correctness. -/
theorem check_twp (hB : m.mem.size = 65536) {Q : Post Nat}
    (hQ : ∀ B nz f', ScanDone m.mem B nz →
      Q (withMach s₀ (checkEnd B)) f' (.normal [Val.i32 (checkRes m nz)])) :
    TWP P host (withMach s₀ m) (Frame.forCall farkasMI [] [.i32, .i32]) (expression checkBody) Q := by
  rw [frame_check, checkBody_eq]
  have hloop := Silmaril.Wasm.Logic.Hoare.TWP.loop (P := P) (host := host) (us := []) (Inv := LInv s₀ m)
    (V := scanV) (bt := .empty) (body := loopBody) (t₁ := []) (t₂ := [])
    (Q := labelPostT P host 0 [] [] (seqPostT P host (expression checkTail) Q))
    (fun _ _ _ _ => rfl) (fun _ _ _ h => h.1 ▸ rfl) (loop_twp hQ)
    (s := withMach s₀ m) (f := scanFrame 0 0) (vs := []) ⟨rfl, 0, 0, m.mem, rfl, rfl, LoopInv.init hB⟩
  have hblock := Silmaril.Wasm.Logic.Hoare.TWP.block (P := P) (host := host) (us := []) (vs := [])
    (bt := .empty) (body := [.loop .empty loopBody]) (rest := expression checkTail) (Q := Q)
    (t₁ := []) (t₂ := []) rfl rfl (by simpa [expression] using hloop)
  simpa [expression] using hblock

/-! ## Export calls -/

/-- `bodyPost` gives the total body postcondition of a call. -/
theorem bodyPost_bodyPostT {n : Nat} {R : Store Nat → Outcome → Prop} {f : Frame}
    {vs₀ : List Val} {s : Store Nat} {F : Frame} {o : Outcome} (h : bodyPost n R s F o) :
    bodyPostT P host n f vs₀ (callPost f vs₀ R) s F o := by
  rcases o with res | _ | _ | _ | _ | _
  · exact ⟨by simpa using h.1, rfl, .inl ⟨res, rfl, h.2⟩⟩
  all_goals first | exact h.elim | exact ⟨rfl, .inr (.inl ⟨rfl, h⟩)⟩

/-- The store holds a machine state with a page of memory. -/
def TotPre (s : Store Nat) : Prop := ∃ m, Holds s m ∧ m.mem.size = 65536

/-- **The total specification of an export call**: it returns typed values and leaves a store
holding a machine state. -/
def tspec (f : farkasI.F.Op) : FSpec Nat where
  pre s args := args = f.2.1 ∧ TotPre s
  post _ _ s' o := ∃ vs, o = .normal vs ∧
    List.Forall₂ ScalarType.HasVal (farkasI.exports.get f.1).results vs ∧ TotPre s'

theorem tpre_funcs {f : farkasI.F.Op} {s : Store Nat} {args : List Val} (h : (tspec f).pre s args) :
    s.funcs = farkasStore.funcs := by
  obtain ⟨-, m, hH, -⟩ := h
  exact hH.funcs

theorem tpre_len {f : farkasI.F.Op} {s : Store Nat} {args : List Val} (h : (tspec f).pre s args) :
    args.length = (Ty.ofList ((farkasExports.get f.1).params.map ScalarType.toC)).length := by
  rw [h.1, Ty.length_ofList, List.length_map]
  exact f.2.2.length_eq.symm

/-- **`row` terminates.** -/
theorem tspec_row (args : Typed (farkasExports.get ⟨0, by decide⟩).params) :
    TFSpecAt P host (farkasI.addr ⟨0, by decide⟩) (tspec ⟨⟨0, by decide⟩, args⟩) := by
  obtain ⟨fi₀, fi₁, fi₂, hfs, hm₀, -, -, hc₀, -, -, ht₀, -, -⟩ := farkasStore_funcs
  obtain ⟨y, b, hargs⟩ := typed_row args.2
  refine Silmaril.Wasm.Logic.Hoare.TFSpecAt.of_body (fi := fi₀) (code := ⟨⟨0⟩, [.i64], rowBody⟩)
    (fun s _ h => by rw [tpre_funcs h, hfs]; rfl) hc₀ (FnType.expand_of_ofDefType? ht₀)
    (fun _ _ h => tpre_len h) (fun s args' hpre f vs₀ => ?_)
  obtain ⟨rfl, m, ⟨s₀, hs₀, rfl⟩, hB⟩ := hpre
  rw [hm₀, hargs]
  exact (row_twp y b fun _ => ⟨rfl, [], rfl, .nil, rowM m y b, holds_withMach hs₀ _, hB⟩).post_mono
    fun _ _ _ h => bodyPost_bodyPostT h

/-- **`entry` terminates.** -/
theorem tspec_entry (args : Typed (farkasExports.get ⟨1, by decide⟩).params) :
    TFSpecAt P host (farkasI.addr ⟨1, by decide⟩) (tspec ⟨⟨1, by decide⟩, args⟩) := by
  obtain ⟨fi₀, fi₁, fi₂, hfs, -, hm₁, -, -, hc₁, -, -, ht₁, -⟩ := farkasStore_funcs
  obtain ⟨j, a, hargs⟩ := typed_entry args.2
  refine Silmaril.Wasm.Logic.Hoare.TFSpecAt.of_body (fi := fi₁) (code := ⟨⟨1⟩, [.i32, .i64], entryBody⟩)
    (fun s _ h => by rw [tpre_funcs h, hfs]; rfl) hc₁ (FnType.expand_of_ofDefType? ht₁)
    (fun _ _ h => tpre_len h) (fun s args' hpre f vs₀ => ?_)
  obtain ⟨rfl, m, ⟨s₀, hs₀, rfl⟩, hB⟩ := hpre
  rw [hm₁, hargs]
  have hB' : (entryM m j a).mem.size = 65536 := size_setSlot hB (Nat.mod_lt _ (by decide)) _
  exact (entry_twp hB j a fun _ => ⟨rfl, [], rfl, .nil, entryM m j a, holds_withMach hs₀ _, hB'⟩).post_mono
    fun _ _ _ h => bodyPost_bodyPostT h

/-- **`check` terminates.** -/
theorem tspec_check (args : Typed (farkasExports.get ⟨2, by decide⟩).params) :
    TFSpecAt P host (farkasI.addr ⟨2, by decide⟩) (tspec ⟨⟨2, by decide⟩, args⟩) := by
  obtain ⟨fi₀, fi₁, fi₂, hfs, -, -, hm₂, -, -, hc₂, -, -, ht₂⟩ := farkasStore_funcs
  have hargs := typed_nil args.2
  refine Silmaril.Wasm.Logic.Hoare.TFSpecAt.of_body (fi := fi₂) (code := ⟨⟨2⟩, [.i32, .i32], checkBody⟩)
    (fun s _ h => by rw [tpre_funcs h, hfs]; rfl) hc₂ (FnType.expand_of_ofDefType? ht₂)
    (fun _ _ h => tpre_len h) (fun s args' hpre f vs₀ => ?_)
  obtain ⟨rfl, m, ⟨s₀, hs₀, rfl⟩, hB⟩ := hpre
  rw [hm₂, hargs]
  exact (check_twp hB fun B nz _ hd => ⟨rfl, _, rfl, .cons ⟨_, rfl⟩ .nil, checkEnd B,
    holds_withMach hs₀ _, hd.size⟩).post_mono fun _ _ _ h => bodyPost_bodyPostT h

/-- **Every export call terminates** with typed results, at every profile and for every host. -/
theorem tspec_valid (f : farkasI.F.Op) : TFSpecAt P host (farkasI.addr f.1) (tspec f) := by
  obtain ⟨⟨j, hj⟩, args⟩ := f
  have hj' : j < 3 := hj
  match j, hj, hj', args with
  | 0, _, _, args => exact tspec_row args
  | 1, _, _, args => exact tspec_entry args
  | 2, _, _, args => exact tspec_check args

/-! ## Sessions exist -/

/-- A totally correct configuration has a run to an exit satisfying the postcondition. -/
theorem TSafe.exists_run {Q : Post Nat} {c : Config Nat} (h : TSafe P host Q c) :
    ∃ c', Steps P host c c' ∧ ∃ o, Exits o c'.code ∧ Q c'.store c'.frame o := by
  induction h with
  | exit o he hq => exact ⟨_, .refl, o, he, hq⟩
  | step hex _ ih =>
    obtain ⟨c₁, hs⟩ := hex
    obtain ⟨c', hs', o, he, hq⟩ := ih c₁ hs
    exact ⟨c', Relation.ReflTransGen.head hs hs', o, he, hq⟩

/-- **An export call runs to typed values** from a store holding a machine state. -/
theorem call_run (f : farkasI.F.Op) {s : Store Nat} (hs : TotPre s) :
    ∃ (c' : Config Nat) (res : List Val), Steps P host (invoke s (farkasI.addr f.1) f.2.1) c' ∧
      c'.code = (Result.values res).toAdmin ∧
      List.Forall₂ ScalarType.HasVal (farkasI.exports.get f.1).results res ∧ TotPre c'.store := by
  have h : TSafe P host (callPost {} [] ((tspec f).post s f.2.1)) (invoke s (farkasI.addr f.1) f.2.1) :=
    tspec_valid f s f.2.1 ⟨rfl, hs⟩ {} [] _ trivial
  obtain ⟨c', run, o, he, -, hp⟩ := TSafe.exists_run h
  rcases hp with ⟨res, rfl, vs, hvs, hty, hs'⟩ | ⟨rfl, vs, hvs, -⟩ | ⟨a, rfl, vs, hvs, -⟩
  · obtain rfl : res = vs := Outcome.normal.inj hvs
    exact ⟨c', res, run, he, hty, hs'⟩
  · cases hvs
  · cases hvs

/-- The answer of typed values. -/
theorem ofResult_values' {ft : FnType} {vs : List Val}
    (h : List.Forall₂ ScalarType.HasVal ft.results vs) :
    Answer.ofResult? ft (.values vs) = some (.values ⟨vs, h⟩) := by
  simp only [Answer.ofResult?, h, dite_true]

/-- **Every sequence of export calls is a session**: from a store holding a machine state, each
call runs to an answer (every profile, every environment). -/
theorem farkas_total {K : Env farkasI.E} :
    ∀ (fs : List farkasI.F.Op) {s : Store Nat}, TotPre s →
      ∃ l : List (Call farkasI), l.map Sigma.fst = fs ∧ Session P farkasI K s l
  | [], s, _ => ⟨[], rfl, .nil s⟩
  | f :: fs, _, hs => by
    obtain ⟨c', res, run, hcode, hty, hs'⟩ := call_run (P := P) (host := hostOf farkasI.imports K) f hs
    obtain ⟨l, hl, hS⟩ := farkas_total fs hs'
    exact ⟨⟨f, .values ⟨res, hty⟩⟩ :: l, congrArg (f :: ·) hl,
      .cons c' (.values res) run hcode (ofResult_values' hty) hS⟩

theorem totPre_init : TotPre farkasI.store := ⟨Mach.init, farkasStore_holds, size_zeroBytes⟩

/-- **Total completeness over sessions**: for every sequence of export calls followed by `check`
there is a session from the instance's store, and its `check` answers `1` whenever the calls
passed the bounds and loaded a valid Farkas certificate. -/
theorem farkas_accepts {K : Env farkasI.E} (fs : List farkasI.F.Op) :
    ∃ (l₁ : List (Call farkasI)) (w : farkasI.F.Ar checkOp), l₁.map Sigma.fst = fs ∧
      Session P farkasI K farkasI.store (l₁ ++ [⟨checkOp, w⟩]) ∧
      (LoadsOk l₁ → WRows.IsCert (loaded l₁) →
        Answer.toResult (ft := farkasI.exports.get checkOp.1) w = .values [Val.i32 1]) := by
  obtain ⟨l, hl, hS⟩ := farkas_total (P := P) (K := K) (fs ++ [checkOp]) totPre_init
  obtain ⟨l₁, c, rfl⟩ : ∃ l₁ c, l = l₁ ++ [c] := by
    rcases List.eq_nil_or_concat l with rfl | ⟨l₁, c, rfl⟩
    · simp at hl
    · exact ⟨l₁, c, List.concat_eq_append⟩
  rw [List.map_append, List.map_singleton] at hl
  obtain ⟨h₁, h₂⟩ := List.append_inj' hl rfl
  obtain ⟨f, w⟩ := c
  obtain rfl : f = checkOp := List.singleton_inj.mp h₂
  exact ⟨l₁, w, h₁, hS, fun hok hc => farkas_complete hS rfl hok hc⟩

/-- **The positive test, with total correctness**: there is a session (every profile and
environment) loading `x₀ ≤ 1, -x₀ ≤ -2` with the multipliers `1, 1` and then calling `check`,
and in every such session `check` answers `1`. -/
theorem cert_session {K : Env farkasI.E} :
    ∃ w₁ w₂ w₃ w₄ w, Session P farkasI K farkasI.store (certCalls w₁ w₂ w₃ w₄ ++ [⟨checkOp, w⟩]) ∧
      Answer.toResult (ft := farkasI.exports.get checkOp.1) w = .values [Val.i32 1] := by
  obtain ⟨l₁, w, hl, hS, -⟩ := farkas_accepts (P := P) (K := K)
    [rowOp 1 1, entryOp 0 1, rowOp 1 (-2), entryOp 0 (-1)]
  match l₁, hl with
  | [⟨_, w₁⟩, ⟨_, w₂⟩, ⟨_, w₃⟩, ⟨_, w₄⟩], rfl => exact ⟨w₁, w₂, w₃, w₄, w, hS, cert_accepted w₁ w₂ w₃ w₄ w hS⟩

end Silmaril.Wasm.Examples.Farkas
