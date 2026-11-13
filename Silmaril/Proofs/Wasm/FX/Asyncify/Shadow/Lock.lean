module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Rel
public import Silmaril.Wasm.FX.Asyncify.RelSim.Thms

/-!
# The shadow-stack strategy runs in lock step with `fstep`

`fstep` (records in a heap and a register) and `mstep` (records encoded in one memory) take the
same steps from `MR`-related configurations, one each (**`lock`**):

* normal mode (`exec_rel`): the same instruction, with `alloc` writing a one-record buffer
  (`alloc_rel`), `startUnwind` writing the first record (`startUnwind_rel`) and `startRewind`
  turning a table entry into the reading registers (`startRewind_rel`);
* unwinding (`unwind_rel`): a check appends a record to the memory (`unwind_save`), a handling
  `rchk` turns the buffer just written into a table entry (`rchk_rel`);
* rewinding (`rewind_rel`): the record read back from the memory (`rewind_pop`) is the next
  record of the register.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Shadow

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC Silmaril.Wasm.FX.Asyncify.Shadow
open Silmaril.Wasm.FX.Asyncify.RelSim

variable {V : Type} {P : Prog (AIns V)} {B : Nat → Option (List (TIns V))} {test : V → Bool}

theorem mr_normal {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (cnt top : Nat) (st : List (AFrame V)) :
    MR ⟨h, 0, t, p, b, st⟩ ⟨mem, tbl, 0, t, p, cnt, top, st⟩ :=
  ⟨hh, rfl, rfl, rfl, rfl, trivial⟩

/-! ## Normal mode -/

theorem call_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (cnt top : Nat) (st : List (AFrame V)) (f : Nat) (ops : List (SV V))
    (c : List (AIns V)) (rest : List (AFrame V)) :
    RRes MR (fcall P h t p b f ops c rest) (mcall P ⟨mem, tbl, 0, t, p, cnt, top, st⟩ f ops c rest) := by
  simp only [fcall, mcall]
  rcases P f with _ | ⟨np, body⟩
  · exact .stop _
  · dsimp only
    rcases popN np ops with _ | ⟨args, o⟩
    · exact .stop _
    · exact .next (mr_normal hh t p b cnt top _)

theorem alloc_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (cnt top : Nat) (fr : AFrame V) (f : Nat) (c : List (AIns V))
    (rest : List (AFrame V)) :
    RRes MR (fexec P test h t p b fr (.alloc f) c rest)
      (mexec P test ⟨mem, tbl, 0, t, p, cnt, top, fr :: rest⟩ fr (.alloc f) c rest) := by
  have hlen : h.length = tbl.length := hh.length_eq
  have hh' : HeapR (mem ++ enc ⟨f + 1, 0, []⟩) (h ++ [some [⟨f + 1, 0, []⟩]])
      (tbl ++ [some ((mem ++ enc ⟨f + 1, 0, []⟩).length, 1)]) :=
    Silmaril.Wasm.FX.Asyncify.RelSim.forall₂_append_one (heapR_append hh _) (.some (saved_one mem _))
  simp only [fexec, mexec, hlen]
  rcases P f with _ | ⟨np, body⟩
  · exact .stop _
  · exact .next (mr_normal hh' t p _ cnt top _)

theorem startUnwind_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (cnt top : Nat) (fr : AFrame V) (t' n fn r : Nat) (c : List (AIns V))
    (rest : List (AFrame V)) :
    RRes MR (fexec P test h t p b fr (.startUnwind t' n fn r) c rest)
      (mexec P test ⟨mem, tbl, 0, t, p, cnt, top, fr :: rest⟩ fr (.startUnwind t' n fn r) c rest) := by
  simp only [fexec, mexec]
  rcases popN n fr.ops with _ | ⟨p', o⟩
  · exact .stop _
  · have hm : mem ++ enc ⟨fn, r, o⟩ = mem ++ encBuf [⟨fn, r, o⟩] := by rw [encBuf_single]
    exact .next ⟨heapR_append hh _, rfl, rfl, rfl, rfl, rfl, mem, hm⟩

/-- A saved buffer read by `startRewind`: the reading registers. -/
theorem saved_mr {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hset : HeapR mem h tbl) {t : Nat} {args : List (SV V)}
    {st : List (AFrame V)} {q : Rec V} {seg : List (Rec V)} {e' : Nat}
    (hs : Saved mem (q :: seg) (e', seg.length + 1)) :
    MR ⟨h, 2, t, args, (q :: seg).reverse, st⟩ ⟨mem, tbl, 2, t, args, seg.length + 1, e', st⟩ := by
  obtain ⟨-, pre, rst, hm, he⟩ := hs
  have hm' : mem = pre ++ encBuf (q :: seg).reverse.reverse ++ rst := by
    rw [List.reverse_reverse]; exact hm
  have he' : e' = (pre ++ encBuf (q :: seg).reverse.reverse).length := by
    rw [List.reverse_reverse]; exact he
  have hlen : seg.length + 1 = (q :: seg).reverse.length := by
    rw [List.length_reverse, List.length_cons]
  exact ⟨hset, rfl, rfl, rfl, rfl, hlen, pre, rst, hm', he'⟩

/-- A table entry read by `startRewind`. -/
theorem rewind_entry {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (k : Nat) (t : Nat)
    (args : List (SV V)) (c : List (AIns V)) (o' : List (SV V)) (rest : List (AFrame V))
    {a : Option (Option (List (Rec V)))} {e : Option (Option (Nat × Nat))}
    (hk : Option.Rel (Option.Rel (Saved mem)) a e) :
    RRes MR
      (match (generalizing := false) a with
        | some (some (top' :: seg)) =>
          .next ⟨h.set k none, 2, t, args, (top' :: seg).reverse, ⟨c, o'⟩ :: rest⟩
        | _ => (.stop .trap : Res (FCfg V) V))
      (match (generalizing := false) e with
        | some (some (e', m + 1)) =>
          .next (⟨mem, tbl.set k none, 2, t, args, m + 1, e', ⟨c, o'⟩ :: rest⟩ : MCfg V)
        | _ => (.stop .trap : Res (MCfg V) V)) := by
  have hset : HeapR mem (h.set k none) (tbl.set k none) :=
    Silmaril.Wasm.FX.Asyncify.RelSim.forall₂_set hh .none k
  cases hk with
  | none => exact .stop _
  | some hk' =>
    cases hk' with
    | none => exact .stop _
    | @some recs ent hs =>
      obtain ⟨e', n⟩ := ent
      cases recs with
      | nil =>
        have hn0 : n = 0 := hs.1
        rw [hn0]; exact .stop _
      | cons q seg =>
        have hn1 : n = seg.length + 1 := hs.1
        rw [hn1] at hs ⊢
        exact .next (saved_mr hset hs)

theorem startRewind_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (cnt top : Nat) (fr : AFrame V) (n : Nat) (c : List (AIns V))
    (rest : List (AFrame V)) :
    RRes MR (fexec P test h t p b fr (.startRewind n) c rest)
      (mexec P test ⟨mem, tbl, 0, t, p, cnt, top, fr :: rest⟩ fr (.startRewind n) c rest) := by
  simp only [fexec, mexec]
  rcases fr.ops with _ | ⟨_ | k, o⟩
  · exact .stop _
  · exact .stop _
  · dsimp only
    rcases popN n o with _ | ⟨args, o'⟩
    · exact .stop _
    · exact rewind_entry hh k t args c o' rest
        (Silmaril.Wasm.FX.Asyncify.RelSim.forall₂_getElem? hh k)

theorem prim_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (cnt top : Nat) (fr : AFrame V) (n : Nat) (op : List V → List V)
    (c : List (AIns V)) (rest : List (AFrame V)) :
    RRes MR (fexec P test h t p b fr (.prim n op) c rest)
      (mexec P test ⟨mem, tbl, 0, t, p, cnt, top, fr :: rest⟩ fr (.prim n op) c rest) := by
  simp only [fexec, mexec]
  rcases popN n fr.ops with _ | ⟨a, o⟩
  · exact .stop _
  · dsimp only
    rcases allVals a with _ | vs
    · exact .stop _
    · exact .next (mr_normal hh t p b cnt top _)

theorem drop_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (cnt top : Nat) (fr : AFrame V) (c : List (AIns V))
    (rest : List (AFrame V)) :
    RRes MR (fexec P test h t p b fr .drop c rest)
      (mexec P test ⟨mem, tbl, 0, t, p, cnt, top, fr :: rest⟩ fr .drop c rest) := by
  simp only [fexec, mexec]
  rcases fr.ops with _ | ⟨_, o⟩
  · exact .stop _
  · exact .next (mr_normal hh t p b cnt top _)

theorem cond_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (cnt top : Nat) (fr : AFrame V) (f g : Nat) (c : List (AIns V))
    (rest : List (AFrame V)) :
    RRes MR (fexec P test h t p b fr (.cond f g) c rest)
      (mexec P test ⟨mem, tbl, 0, t, p, cnt, top, fr :: rest⟩ fr (.cond f g) c rest) := by
  simp only [fexec, mexec]
  rcases fr.ops with _ | ⟨_ | _, o⟩
  · exact .stop _
  · exact call_rel hh t p b cnt top _ _ o c rest
  · exact .stop _

/-- **One normal-mode instruction.** -/
theorem exec_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (cnt top : Nat) (fr : AFrame V) (i : AIns V) (c : List (AIns V))
    (rest : List (AFrame V)) :
    RRes MR (fexec P test h t p b fr i c rest)
      (mexec P test ⟨mem, tbl, 0, t, p, cnt, top, fr :: rest⟩ fr i c rest) := by
  cases i with
  | push v => exact .next (mr_normal hh t p b cnt top _)
  | prim n op => exact prim_rel hh t p b cnt top fr n op c rest
  | drop => exact drop_rel hh t p b cnt top fr c rest
  | call f => exact call_rel hh t p b cnt top _ f fr.ops c rest
  | cond f g => exact cond_rel hh t p b cnt top fr f g c rest
  | alloc f => exact alloc_rel hh t p b cnt top fr f c rest
  | startRewind n => exact startRewind_rel hh t p b cnt top fr n c rest
  | startUnwind t' n fn r => exact startUnwind_rel hh t p b cnt top fr t' n fn r c rest
  | chk fn r => exact .next (mr_normal hh t p b cnt top _)
  | rchk hs fn r => exact .next (mr_normal hh t p b cnt top _)

/-! ## Unwinding -/

/-- A check saves its frame: one more record at the end of the memory. -/
theorem unwind_save {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) {t : Nat} {p : List (SV V)}
    {b : List (Rec V)} {cnt top : Nat} {st : List (AFrame V)}
    (hb : RBuf 1 b ⟨mem, tbl, 1, t, p, cnt, top, st⟩) (q : Rec V) (rest : List (AFrame V)) :
    MR ⟨h, 1, t, p, b ++ [q], rest⟩ ⟨mem ++ enc q, tbl, 1, t, p, cnt + 1, top, rest⟩ := by
  obtain ⟨hc, pre, hm⟩ : cnt = b.length ∧ ∃ pre, mem = pre ++ encBuf b := hb
  have hm' : mem ++ enc q = pre ++ encBuf (b ++ [q]) := by
    rw [hm, encBuf_append, encBuf_single, List.append_assoc]
  have hc' : cnt + 1 = (b ++ [q]).length := by
    rw [hc, List.length_append, List.length_singleton]
  exact ⟨heapR_append hh _, rfl, rfl, rfl, rfl, hc', pre, hm'⟩

/-- An unwinding step at an `rchk`. -/
theorem rchk_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) {t : Nat} {p : List (SV V)}
    {b : List (Rec V)} {cnt top : Nat} {st : List (AFrame V)}
    (hb : RBuf 1 b ⟨mem, tbl, 1, t, p, cnt, top, st⟩) (hs : List Clause) (fn r : Nat)
    (c : List (AIns V)) (ops : List (SV V)) (rest : List (AFrame V)) :
    RRes MR (funwind P h t p b ⟨.rchk hs fn r :: c, ops⟩ rest)
      (munwind P ⟨mem, tbl, 1, t, p, cnt, top, st⟩ ⟨.rchk hs fn r :: c, ops⟩ rest) := by
  obtain ⟨hc, pre, hm⟩ : cnt = b.length ∧ ∃ pre, mem = pre ++ encBuf b := hb
  have hlen : h.length = tbl.length := hh.length_eq
  have hsv : Saved mem b (mem.length, cnt) := hc ▸ saved_end hm
  have hh' : HeapR mem (h ++ [some b]) (tbl ++ [some (mem.length, cnt)]) :=
    Silmaril.Wasm.FX.Asyncify.RelSim.forall₂_append_one hh (.some hsv)
  simp only [funwind, munwind, hlen]
  rcases lookup t hs with _ | hf
  · exact .next (unwind_save (st := st) hh ⟨hc, pre, hm⟩ ⟨fn, r, ops⟩ rest)
  · dsimp only
    rcases P hf with _ | ⟨np, body⟩
    · exact .stop _
    · exact .next ⟨hh', rfl, rfl, rfl, rfl, trivial⟩

/-- **An unwinding step.** -/
theorem unwind_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) {t : Nat} {p : List (SV V)}
    {b : List (Rec V)} {cnt top : Nat} {st : List (AFrame V)}
    (hb : RBuf 1 b ⟨mem, tbl, 1, t, p, cnt, top, st⟩) :
    RRes MR (fstep P B test ⟨h, 1, t, p, b, st⟩) (mstep P B test ⟨mem, tbl, 1, t, p, cnt, top, st⟩) := by
  rcases st with _ | ⟨⟨code, ops⟩, rest⟩
  · exact .stop _
  · simp only [fstep, mstep]
    rcases code with _ | ⟨i, c⟩
    · exact .stop _
    · cases i
      case chk fn r => exact .next (unwind_save hh hb ⟨fn, r, ops⟩ rest)
      case rchk hs fn r => exact rchk_rel hh hb hs fn r c ops rest
      all_goals exact .stop _

/-! ## Rewinding -/

/-- **The record read back** is the next one of the register. -/
theorem rewind_pop {mem pre rst : List (Cell V)} {q : Rec V} {qs : List (Rec V)} {top : Nat}
    (hm : mem = pre ++ encBuf (q :: qs).reverse ++ rst)
    (htop : top = (pre ++ encBuf (q :: qs).reverse).length) :
    popRev (mem.take top).reverse = some (q, (pre ++ encBuf qs.reverse).reverse) := by
  have h1 : encBuf (q :: qs).reverse = encBuf qs.reverse ++ enc q := by
    rw [List.reverse_cons, encBuf_append, encBuf_single]
  have h2 : mem.take top = pre ++ encBuf qs.reverse ++ enc q := by
    rw [hm, htop, List.take_left, h1, List.append_assoc]
  rw [h2]
  exact popRev_enc _ q

/-- The last record: back to normal mode. -/
theorem rewind_last {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) {t : Nat} {p : List (SV V)}
    {q : Rec V} {cnt top : Nat} {st : List (AFrame V)}
    (hb : RBuf 2 [q] ⟨mem, tbl, 2, t, p, cnt, top, st⟩) :
    RRes MR (fstep P B test ⟨h, 2, t, p, [q], st⟩)
      (mstep P B test ⟨mem, tbl, 2, t, p, cnt, top, st⟩) := by
  obtain ⟨hc, pre, rst, hm, htop⟩ : cnt = [q].length ∧ ∃ pre rst,
      mem = pre ++ encBuf [q].reverse ++ rst ∧ top = (pre ++ encBuf [q].reverse).length := hb
  have hpop := rewind_pop (qs := []) hm htop
  have hc1 : cnt = 0 + 1 := hc
  simp only [fstep, mstep, mrewind, hc1, hpop]
  rcases disp B q.fn q.r with _ | code
  · exact .stop _
  · exact .next ⟨hh, rfl, rfl, rfl, rfl, trivial⟩

/-- A record with more below it: keep rewinding. -/
theorem rewind_more {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) {t : Nat} {p : List (SV V)}
    {q q' : Rec V} {qs : List (Rec V)} {cnt top : Nat} {st : List (AFrame V)}
    (hb : RBuf 2 (q :: q' :: qs) ⟨mem, tbl, 2, t, p, cnt, top, st⟩) :
    RRes MR (fstep P B test ⟨h, 2, t, p, q :: q' :: qs, st⟩)
      (mstep P B test ⟨mem, tbl, 2, t, p, cnt, top, st⟩) := by
  obtain ⟨hc, pre, rst, hm, htop⟩ : cnt = (q :: q' :: qs).length ∧ ∃ pre rst,
      mem = pre ++ encBuf (q :: q' :: qs).reverse ++ rst ∧
        top = (pre ++ encBuf (q :: q' :: qs).reverse).length := hb
  have hpop := rewind_pop hm htop
  have hc2 : cnt = qs.length + 1 + 1 := hc
  have hm' : mem = pre ++ encBuf (q' :: qs).reverse ++ (enc q ++ rst) := by
    rw [hm, List.reverse_cons (a := q), encBuf_append, encBuf_single]
    simp only [List.append_assoc]
  have htop' : (pre ++ encBuf (q' :: qs).reverse).reverse.length =
      (pre ++ encBuf (q' :: qs).reverse).length := List.length_reverse
  simp only [fstep, mstep, mrewind, hc2, hpop]
  rcases disp B q.fn q.r with _ | code
  · exact .stop _
  · exact .next ⟨hh, rfl, rfl, rfl, rfl, rfl, pre, enc q ++ rst, hm', htop'⟩

/-- **A rewinding step.** -/
theorem rewind_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) {t : Nat} {p : List (SV V)}
    {buf : List (Rec V)} {cnt top : Nat} {st : List (AFrame V)}
    (hb : RBuf 2 buf ⟨mem, tbl, 2, t, p, cnt, top, st⟩) :
    RRes MR (fstep P B test ⟨h, 2, t, p, buf, st⟩)
      (mstep P B test ⟨mem, tbl, 2, t, p, cnt, top, st⟩) := by
  rcases buf with _ | ⟨q, _ | ⟨q', qs⟩⟩
  · have hc : cnt = 0 := hb.1
    simp only [fstep, mstep, mrewind, hc]
    exact .stop _
  · exact rewind_last hh hb
  · exact rewind_more hh hb

/-! ## The lock step -/

/-- Normal mode. -/
theorem normal_rel {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (cnt top : Nat) (st : List (AFrame V)) :
    RRes MR (fstep P B test ⟨h, 0, t, p, b, st⟩) (mstep P B test ⟨mem, tbl, 0, t, p, cnt, top, st⟩) := by
  rcases st with _ | ⟨⟨code, ops⟩, rest⟩
  · exact .stop _
  · rcases code with _ | ⟨i, c⟩
    · rcases rest with _ | ⟨b', rest'⟩
      · exact .stop _
      · exact .next (mr_normal hh t p b cnt top _)
    · exact exec_rel hh t p b cnt top _ i c rest

/-- **`fstep` and `mstep` run in lock step.** -/
theorem lock : LockStep MR (fstep P B test) (mstep P B test) := by
  rintro ⟨h, m, t, p, b, st⟩ ⟨mem, tbl, m', t', p', cnt, top, st'⟩ ⟨hh, hm, ht, hp, hs, hb⟩
  have hm' : m' = m := hm.symm
  have ht' : t' = t := ht.symm
  have hp' : p' = p := hp.symm
  have hs' : st' = st := hs.symm
  rw [hm', ht', hp', hs']
  rw [hm', ht', hp', hs'] at hb
  rcases m with _ | _ | _ | m
  · exact normal_rel hh t p b cnt top st
  · exact unwind_rel hh hb
  · exact rewind_rel hh hb
  · exact .stop _

end Silmaril.Proofs.Wasm.FX.Asyncify.Shadow
