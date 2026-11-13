module

public import Silmaril.Proofs.Wasm.Models.FXCoreSave.Save
public import Silmaril.Proofs.Wasm.Models.FXCoreSave.Restore
public import Silmaril.Wasm.Models.FXDispatch.Thms

/-!
# The unwinding check and the rewinding dispatch of `fstep`, against Core 3.0 `Step`

* `localsAre_setLocals`: after the restore code, the locals hold the saved values;
* `bufIs_save`: after the save code, the buffer global heads a chain with the new record on top;
* **`unwind_chk_step`**: one unwinding step of `fstep` at a call-site check, and the Core 3.0
  check that saves the same record (the linked buffer is the reverse of `fstep`'s buffer);
* **`rewind_step`**: one rewinding step of `fstep` (dispatch on the next record's resume index),
  and the Core 3.0 restore code followed by the `br_table` prologue, which joins the code of the
  function written to start at that resume point, with the locals restored and the record popped.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXCoreSave

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FXCoreSave
open Silmaril.Wasm.Models.FXAsync (SV Res Prog)
open Silmaril.Wasm.Models.FXDispatch (prologue)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Setting the locals from position `i` on leaves the locals below `i`. -/
theorem setLocals_below (f : Frame) :
    ∀ (ls : List Val) (i k : Nat), k < i → i + ls.length ≤ 2 ^ 32 →
      (setLocals f ls i).locals[k]? = f.locals[k]? := by
  intro ls
  induction ls generalizing f with
  | nil => intro i k _ _; rfl
  | cons v vs ih =>
    intro i k hk h32
    simp only [setLocals]
    rw [ih _ (i + 1) k (by omega) (by simp at h32; omega)]
    simp only [Frame.setLocal]
    rw [ix_toNat (k := .local) (j := i) (by simp at h32; omega)]
    exact List.getElem?_set_ne (by omega)

/-- **After the restore code the locals hold the saved values.** -/
theorem localsAre_setLocals (f : Frame) :
    ∀ (ls : List Val) (i : Nat), i + ls.length ≤ f.locals.length → i + ls.length ≤ 2 ^ 32 →
      ∀ j (hj : j < ls.length), (setLocals f ls i).local? (ix (i + j)) = some (some ls[j]) := by
  intro ls i hlen h32 j hj
  induction ls generalizing f i j with
  | nil => simp at hj
  | cons v vs ih =>
    show (setLocals (f.setLocal (ix i) v) vs (i + 1)).local? (ix (i + j)) =
      some (some (v :: vs)[j])
    have hl : i + 1 + vs.length ≤ f.locals.length := by simpa [Nat.add_assoc, Nat.add_comm 1]
      using hlen
    have hl32 : i + 1 + vs.length ≤ 2 ^ 32 := by simpa [Nat.add_assoc, Nat.add_comm 1] using h32
    have hix : (ix i : LocalIdx).toNat = i := ix_toNat (by omega)
    cases j with
    | zero =>
      show (setLocals (f.setLocal (ix i) v) vs (i + 1)).locals[(ix i : LocalIdx).toNat]? =
        some (some v)
      have hbelow : (setLocals (f.setLocal (ix i) v) vs (i + 1)).locals[i]? =
          (f.setLocal (ix i) v).locals[i]? :=
        setLocals_below _ vs (i + 1) i (by omega) hl32
      have hset : (f.setLocal (ix i) v).locals[i]? = some (some v) := by
        simp only [Frame.setLocal, hix]
        exact List.getElem?_set_self (by omega)
      rw [hix, hbelow, hset]
    | succ j =>
      show (setLocals (f.setLocal (ix i) v) vs (i + 1)).local? (ix (i + (j + 1))) =
        some (some (v :: vs)[j + 1])
      have hj' : j < vs.length := by simpa using hj
      have hlen' : i + 1 + vs.length ≤ (f.setLocal (ix i) v).locals.length := by
        simp only [Frame.setLocal, List.length_set]; exact hl
      have h : (setLocals (f.setLocal (ix i) v) vs (i + 1)).local? (ix (i + 1 + j)) =
          some (some vs[j]) := ih (f.setLocal (ix i) v) (i + 1) hlen' hl32 j hj'
      rw [show i + (j + 1) = i + 1 + j by omega]
      exact h

theorem localsAre_restored (f : Frame) (ls : List Val) (hlen : ls.length ≤ f.locals.length)
    (h32 : ls.length ≤ 2 ^ 32) : LocalsAre (setLocals f ls 0) ls := by
  intro j hj
  have h := localsAre_setLocals f ls 0 (by omega) (by omega) j hj
  simpa only [Nat.zero_add] using h

/-- After the save code, the buffer global heads a chain with the new record on top. -/
theorem bufIs_save {s : Store H} {v : Val} {qs : List CRec} (h : BufIs s v qs) (d : DefType)
    (q : CRec) (ab : Nat) :
    BufIs (saveStore s d q v ab) (.ref (.struct s.structs.length)) (q :: qs) := by
  refine .cons (si := ⟨d, (q.fields v).map .val⟩) ?_ rfl ?_
  · simp [saveStore, structs_setGlobal, Store.addStruct]
  · exact bufIs_setGlobal _ _ (bufIs_addStruct _ h)

/-- **An unwinding step at a call-site check.** `fstep` (through `funwind`) appends the record
`p` of the frame to its buffer `buf`; the Core 3.0 check with its save code, in a non-zero mode,
pushes the related struct `q` on the linked buffer, which stays the reverse of `buf`, and reaches
`return`. The mode global is left as it was. -/
theorem unwind_chk_step {V : Type} (PA : Prog (Silmaril.Wasm.Models.FXAsyncPC.AIns V))
    (hp : List (Option (List (Silmaril.Wasm.Models.FXAsyncPC.Rec V)))) (t : Nat) (pay : List (SV V))
    (buf : List (Silmaril.Wasm.Models.FXAsyncPC.Rec V)) (fn r : Nat) (ops : List (SV V))
    (c : List (Silmaril.Wasm.Models.FXAsyncPC.AIns V)) (st : List (Silmaril.Wasm.Models.FXAsyncPC.AFrame V))
    {s : Store H} {f : Frame} {m : GlobalIdx} {am : Nat} {gm : GlobalInst}
    (hm : s.global? f m = some (am, gm)) {k : BitVec 32} (hv : gm.value = .i32 k) (hk : k ≠ 0)
    {x : TypeIdx} {b : GlobalIdx} {n : Nat} (hx : RecTy f x n) {ab : Nat} {gb : GlobalInst}
    (hb : s.global? f b = some (ab, gb)) (hmb : ab ≠ am) {qs : List CRec}
    (hbuf : BufIs s gb.value qs) (q : CRec) (hL : LocalsAre f q.locals)
    (hn : q.locals.length = n) (rest : List Admin) :
    Silmaril.Wasm.Models.FXAsyncPC.funwind PA hp t pay buf ⟨.chk fn r :: c, ops⟩ st =
        .next ⟨hp, 1, t, pay, buf ++ [⟨fn, r, ops⟩], st⟩ ∧
      ∃ d, Steps P host ⟨s, f, expression (chkCode m x b n q.fn q.r) ++ rest⟩
          ⟨saveStore s d q gb.value ab, f, [.plain .return_] ++ rest⟩ ∧
        BufIs (saveStore s d q gb.value ab) (.ref (.struct s.structs.length)) (q :: qs) ∧
        (saveStore s d q gb.value ab).global? f b =
          some (ab, { gb with value := .ref (.struct s.structs.length) }) ∧
        (saveStore s d q gb.value ab).global? f m = some (am, gm) := by
  refine ⟨rfl, ?_⟩
  obtain ⟨d, hrun⟩ := chk_unwind (P := P) (host := host) hm hv hk hx hb q hL hn rest
  refine ⟨d, hrun, bufIs_save hbuf d q ab, ?_, ?_⟩
  · exact global?_setGlobal_self (by rw [global?_addStruct]; exact hb) _
  · exact global?_setGlobal_ne (by rw [global?_addStruct]; exact hm) hmb _

/-- The related buffers grow together: `fstep` appends, the linked list pushes. -/
theorem recRel_unwind {buf : List (Silmaril.Wasm.Models.FXAsyncPC.Rec Val)} {qs : List CRec}
    (h : List.Forall₂ RecRel qs buf.reverse) {q : CRec} {p : Silmaril.Wasm.Models.FXAsyncPC.Rec Val}
    (hq : RecRel q p) : List.Forall₂ RecRel (q :: qs) (buf ++ [p]).reverse := by
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  exact .cons hq h

/-- **A rewinding step.** `fstep` in mode `2` with records `p :: p' :: ps` (bottom first)
re-enters `p` at the code `disp B p.fn p.r` and keeps rewinding `p' :: ps`. In Core 3.0 the
restore code followed by the dispatch prologue `prologue g segs` (with `q`, related to `p`, at
the head of the linked buffer) reaches the same configuration as the function body written to
start at resume point `q.r`, from a frame whose locals hold the saved values and a buffer whose
head is the next record. -/
theorem rewind_step {V : Type} (PA : Prog (Silmaril.Wasm.Models.FXAsyncPC.AIns V))
    (B : Nat → Option (List (Silmaril.Wasm.Models.FXAsync.TIns V))) (test : V → Bool)
    (hp : List (Option (List (Silmaril.Wasm.Models.FXAsyncPC.Rec V)))) (t : Nat) (pay : List (SV V))
    (p p' : Silmaril.Wasm.Models.FXAsyncPC.Rec V) (ps : List (Silmaril.Wasm.Models.FXAsyncPC.Rec V))
    (st : List (Silmaril.Wasm.Models.FXAsyncPC.AFrame V))
    {code : List (Silmaril.Wasm.Models.FXAsyncPC.AIns V)}
    (hd : Silmaril.Wasm.Models.FXAsyncPC.disp B p.fn p.r = some code)
    {s : Store H} {f : Frame} {x : TypeIdx} {b g : GlobalIdx} {n : Nat} (hx : RecTy f x n)
    (h32 : n + 3 ≤ 2 ^ 32) {ab : Nat} {gb : GlobalInst} (hb : s.global? f b = some (ab, gb))
    {ag : Nat} {gg : GlobalInst} (hg : s.global? f g = some (ag, gg)) (hne : ag ≠ ab)
    {q : CRec} {qs : List CRec} (hbuf : BufIs s gb.value (q :: qs)) (hn : q.locals.length = n)
    (hloc : n ≤ f.locals.length) (segs : List (List Instr)) (hr : q.r.toNat < segs.length) :
    Silmaril.Wasm.Models.FXAsyncPC.fstep PA B test ⟨hp, 2, t, pay, p :: p' :: ps, st⟩ =
        .next ⟨hp, 2, t, pay, p' :: ps, ⟨code, p.ops⟩ :: st⟩ ∧
      ∃ nx cfg, BufIs (restoreStore s q nx ag ab) nx qs ∧
        LocalsAre (setLocals f q.locals 0) q.locals ∧
        Steps P host ⟨s, f, expression (restoreCode x b g n ++ prologue g segs)⟩ cfg ∧
        Steps P host ⟨restoreStore s q nx ag ab, setLocals f q.locals 0,
          expression (Silmaril.Wasm.Models.FXDispatch.resumeAt segs q.r.toNat)⟩ cfg := by
  refine ⟨by simp only [Silmaril.Wasm.Models.FXAsyncPC.fstep, hd], ?_⟩
  obtain ⟨nx, hbuf', hrun⟩ := restore_run (P := P) (host := host) hx h32 hb hg hne hbuf hn hloc
    (expression (prologue g segs))
  have hmod := setLocals_module f q.locals 0
  have hg' : (restoreStore s q nx ag ab).global? (setLocals f q.locals 0) g =
      some (ag, { gg with value := .i32 q.r }) := by
    rw [global?_module hmod]
    exact global?_setGlobal_ne (global?_setGlobal_self hg _) (Ne.symm hne) _
  obtain ⟨cfg, h1, h2⟩ := Silmaril.Wasm.Models.FXDispatch.dispatch_joins P host
    (restoreStore s q nx ag ab) (setLocals f q.locals 0) hg' rfl segs hr
  refine ⟨nx, cfg, hbuf', localsAre_restored f q.locals (by omega) (by omega), ?_, h2⟩
  have e : expression (restoreCode x b g n ++ prologue g segs) =
      expression (restoreCode x b g n) ++ expression (prologue g segs) := by
    simp [expression]
  rw [e]
  exact hrun.trans h1

end Silmaril.Proofs.Wasm.Models.FXCoreSave
