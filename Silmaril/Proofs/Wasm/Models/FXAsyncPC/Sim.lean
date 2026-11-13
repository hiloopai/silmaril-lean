module

public import Silmaril.Proofs.Wasm.Models.FXAsyncPC.Rel

/-!
# The asyncify machine and its first-order version run in lock step

For a target function table `Q`, root code `R` and the code table `B = bodies Q R`:

* `lock_call`: calls;
* `lock_exec`: one instruction in normal mode;
* `lock_unwind`: one unwinding step;
* **`lock_step`**: `RCfg B`-related configurations of `tstep Q` and `fstep (annP Q) B` step to
  related results, each machine taking exactly one step;
* `beh_eq_pc`: so related configurations have the same behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncPC

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC

variable {V : Type} {Q : Prog (TIns V)} {R : List (TIns V)}

/-- Heaps related pointwise. -/
abbrev HRel (B : Nat → Option (List (TIns V))) :=
  List.Forall₂ (Option.Rel (List.Forall₂ (RRec B)))

theorem bodies_succ {f np : Nat} {body : List (TIns V)} (h : Q f = some (np, body)) :
    bodies Q R (f + 1) = some body := by
  simp only [bodies, h, Option.map_some]

theorem annP_some {f np : Nat} {body : List (TIns V)} (h : Q f = some (np, body)) :
    annP Q f = some (np, ann (f + 1) 0 body) := by
  simp only [annP, h, Option.map_some]

theorem annP_none {f : Nat} (h : Q f = none) : annP Q f = none := by
  simp only [annP, h, Option.map_none]

theorem lock_call {h : List (Option (List (TFrame V)))} {h' : List (Option (List (Rec V)))}
    (hh : HRel (bodies Q R) h h') (t : Nat) (p : List (SV V)) (b : List (Rec V)) (f : Nat)
    (o : List (SV V)) {c : List (TIns V)} {c' : List (AIns V)}
    (hc : RCode (bodies Q R) c c') {rest : List (TFrame V)} {rest' : List (AFrame V)}
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') :
    ResRel (RCfg (bodies Q R)) (tcall Q h f o c rest) (fcall (annP Q) h' t p b f o c' rest') := by
  cases hQ : Q f with
  | none => simp only [tcall, fcall, hQ, annP_none hQ]; exact .stop _
  | some x =>
    obtain ⟨np, body⟩ := x
    simp only [tcall, fcall, hQ, annP_some hQ]
    cases popN np o with
    | none => exact .stop _
    | some y =>
      exact .next ⟨hh, .cons ⟨rcode_entry (bodies_succ hQ), rfl⟩ (.cons ⟨hc, rfl⟩ hr), rfl⟩

/-- The heap after `alloc f`. -/
theorem heap_alloc {h : List (Option (List (TFrame V)))} {h' : List (Option (List (Rec V)))}
    (hh : HRel (bodies Q R) h h') {f np : Nat} {body : List (TIns V)}
    (hQ : Q f = some (np, body)) :
    HRel (bodies Q R) (h ++ [some [⟨body, []⟩]]) (h' ++ [some [⟨f + 1, 0, []⟩]]) :=
  forall₂_append_one hh (.some (.cons (rrec_even (pc := 0) (bodies_succ hQ) []) .nil))

/-- `startRewind` from related heaps. -/
theorem lock_rewind_start {h : List (Option (List (TFrame V)))}
    {h' : List (Option (List (Rec V)))} (hh : HRel (bodies Q R) h h') (t : Nat) (k : Nat)
    (args o' : List (SV V)) {c : List (TIns V)} {c' : List (AIns V)}
    (hc : RCode (bodies Q R) c c') {rest : List (TFrame V)} {rest' : List (AFrame V)}
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') :
    ResRel (RCfg (bodies Q R))
      (match h[k]? with
        | some (some (top :: seg)) =>
          .next ⟨h.set k none, .rewind (top :: seg).reverse args, ⟨c, o'⟩ :: rest⟩
        | _ => (.stop .trap : Res (TCfg V) V))
      (match h'[k]? with
        | some (some (top :: seg)) =>
          .next ⟨h'.set k none, 2, t, args, (top :: seg).reverse, ⟨c', o'⟩ :: rest'⟩
        | _ => (.stop .trap : Res (FCfg V) V)) := by
  have hk := forall₂_getElem? hh k
  have hset := forall₂_set hh (Option.Rel.none) k
  generalize h[k]? = u at hk
  generalize h'[k]? = u' at hk
  cases hk with
  | none => exact .stop _
  | some hl =>
    cases hl with
    | none => exact .stop _
    | some hs =>
      cases hs with
      | nil => exact .stop _
      | cons hq hseg =>
        exact .next ⟨hset, .cons ⟨hc, rfl⟩ hr, rfl, rfl, forall₂_reverse (.cons hq hseg)⟩

section exec

variable {h : List (Option (List (TFrame V)))} {h' : List (Option (List (Rec V)))}
  {c : List (TIns V)} {c' : List (AIns V)} {rest : List (TFrame V)} {rest' : List (AFrame V)}

theorem lock_prim (hh : HRel (bodies Q R) h h') (hc : RCode (bodies Q R) c c')
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') (test : V → Bool) (t : Nat)
    (p : List (SV V)) (b : List (Rec V)) (code : List (TIns V)) (code' : List (AIns V))
    (ops : List (SV V)) (n : Nat) (op : List V → List V) :
    ResRel (RCfg (bodies Q R)) (texec Q test h ⟨code, ops⟩ (.prim n op) c rest)
      (fexec (annP Q) test h' t p b ⟨code', ops⟩ (.prim n op) c' rest') := by
  simp only [texec, fexec]
  cases popN n ops with
  | none => exact .stop _
  | some x =>
    show ResRel _ (match allVals x.1 with | none => _ | some vs => _)
      (match allVals x.1 with | none => _ | some vs => _)
    cases allVals x.1 with
    | none => exact .stop _
    | some vs => exact .next ⟨hh, .cons ⟨hc, rfl⟩ hr, rfl⟩

theorem lock_drop (hh : HRel (bodies Q R) h h') (hc : RCode (bodies Q R) c c')
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') (test : V → Bool) (t : Nat)
    (p : List (SV V)) (b : List (Rec V)) (code : List (TIns V)) (code' : List (AIns V))
    (ops : List (SV V)) :
    ResRel (RCfg (bodies Q R)) (texec Q test h ⟨code, ops⟩ .drop c rest)
      (fexec (annP Q) test h' t p b ⟨code', ops⟩ .drop c' rest') := by
  simp only [texec, fexec]
  cases ops with
  | nil => exact .stop _
  | cons _ o => exact .next ⟨hh, .cons ⟨hc, rfl⟩ hr, rfl⟩

theorem lock_cond (hh : HRel (bodies Q R) h h') (hc : RCode (bodies Q R) c c')
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') (test : V → Bool) (t : Nat)
    (p : List (SV V)) (b : List (Rec V)) (code : List (TIns V)) (code' : List (AIns V))
    (ops : List (SV V)) (f g : Nat) :
    ResRel (RCfg (bodies Q R)) (texec Q test h ⟨code, ops⟩ (.cond f g) c rest)
      (fexec (annP Q) test h' t p b ⟨code', ops⟩ (.cond f g) c' rest') := by
  simp only [texec, fexec]
  cases ops with
  | nil => exact .stop _
  | cons v o =>
    cases v with
    | val v => exact lock_call hh t p b _ o hc hr
    | cont _ => exact .stop _

theorem lock_alloc (hh : HRel (bodies Q R) h h') (hc : RCode (bodies Q R) c c')
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') (test : V → Bool) (t : Nat)
    (p : List (SV V)) (b : List (Rec V)) (code : List (TIns V)) (code' : List (AIns V))
    (ops : List (SV V)) (f : Nat) :
    ResRel (RCfg (bodies Q R)) (texec Q test h ⟨code, ops⟩ (.alloc f) c rest)
      (fexec (annP Q) test h' t p b ⟨code', ops⟩ (.alloc f) c' rest') := by
  have hlen : h.length = h'.length := hh.length_eq
  simp only [texec, fexec]
  cases hQ : Q f with
  | none => simp only [annP_none hQ]; exact .stop _
  | some x =>
    simp only [annP_some hQ, hlen]
    exact .next ⟨heap_alloc hh hQ, .cons ⟨hc, rfl⟩ hr, rfl⟩

theorem lock_srew (hh : HRel (bodies Q R) h h') (hc : RCode (bodies Q R) c c')
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') (test : V → Bool) (t : Nat)
    (p : List (SV V)) (b : List (Rec V)) (code : List (TIns V)) (code' : List (AIns V))
    (ops : List (SV V)) (n : Nat) :
    ResRel (RCfg (bodies Q R)) (texec Q test h ⟨code, ops⟩ (.startRewind n) c rest)
      (fexec (annP Q) test h' t p b ⟨code', ops⟩ (.startRewind n) c' rest') := by
  simp only [texec, fexec]
  cases ops with
  | nil => exact .stop _
  | cons v o =>
    cases v with
    | val _ => exact .stop _
    | cont k =>
      show ResRel _ (match popN n o with | none => _ | some (args, o') => _)
        (match popN n o with | none => _ | some (args, o') => _)
      cases popN n o with
      | none => exact .stop _
      | some x => exact lock_rewind_start hh t k x.1 x.2 hc hr

theorem lock_sunw (hh : HRel (bodies Q R) h h') {fn pc : Nat} {body : List (TIns V)}
    (hb : bodies Q R fn = some body) (hd : body.drop (pc + 1) = c)
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') (test : V → Bool) (t : Nat)
    (p : List (SV V)) (b : List (Rec V)) (code : List (TIns V)) (code' : List (AIns V))
    (ops : List (SV V)) (t' n : Nat) :
    ResRel (RCfg (bodies Q R)) (texec Q test h ⟨code, ops⟩ (.startUnwind t' n) c rest)
      (fexec (annP Q) test h' t p b ⟨code', ops⟩ (.startUnwind t' n fn (2 * (pc + 1))) c'
        rest') := by
  simp only [texec, fexec]
  cases popN n ops with
  | none => exact .stop _
  | some x =>
    have hrec : RRec (bodies Q R) ⟨c, x.2⟩ ⟨fn, 2 * (pc + 1), x.2⟩ := hd ▸ rrec_even hb x.2
    exact .next ⟨hh, hr, rfl, rfl, rfl, .cons hrec .nil⟩

/-- **One instruction in normal mode.** -/
theorem lock_exec (test : V → Bool) (hh : HRel (bodies Q R) h h') (t : Nat) (p : List (SV V))
    (b : List (Rec V)) (code : List (TIns V)) (code' : List (AIns V)) (ops : List (SV V))
    {i : TIns V} {fn pc : Nat} {body : List (TIns V)} (hb : bodies Q R fn = some body)
    (hd : body.drop pc = i :: c) (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') :
    ResRel (RCfg (bodies Q R)) (texec Q test h ⟨code, ops⟩ i c rest)
      (fexec (annP Q) test h' t p b ⟨code', ops⟩ (annI fn pc i) (ann fn (pc + 1) c) rest') := by
  have hd' : body.drop (pc + 1) = c := drop_succ_of_cons hd
  have hc : RCode (bodies Q R) c (ann fn (pc + 1) c) := rcode_suffix hb hd'
  cases i with
  | push v => exact .next ⟨hh, .cons ⟨hc, rfl⟩ hr, rfl⟩
  | prim n op => exact lock_prim hh hc hr test t p b code code' ops n op
  | drop => exact lock_drop hh hc hr test t p b code code' ops
  | call f => exact lock_call hh t p b f ops hc hr
  | cond f g => exact lock_cond hh hc hr test t p b code code' ops f g
  | alloc f => exact lock_alloc hh hc hr test t p b code code' ops f
  | startRewind n => exact lock_srew hh hc hr test t p b code code' ops n
  | startUnwind t' n => exact lock_sunw hh hb hd' hr test t p b code code' ops t' n
  | chk => exact .next ⟨hh, .cons ⟨hc, rfl⟩ hr, rfl⟩
  | rchk hs => exact .next ⟨hh, .cons ⟨hc, rfl⟩ hr, rfl⟩

end exec

/-- The handled case of an unwinding step at an `rchk`. -/
theorem lock_handle {h : List (Option (List (TFrame V)))} {h' : List (Option (List (Rec V)))}
    (hh : HRel (bodies Q R) h h') {t : Nat} {p : List (SV V)} {buf : List (TFrame V)}
    {buf' : List (Rec V)} (hbuf : List.Forall₂ (RRec (bodies Q R)) buf buf') (hf : Nat)
    {ops : List (SV V)} {c : List (TIns V)} {hs : List Clause} {fn pc : Nat}
    {body : List (TIns V)} (hb : bodies Q R fn = some body) (hd : body.drop pc = .rchk hs :: c)
    {rest : List (TFrame V)} {rest' : List (AFrame V)}
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') :
    ResRel (RCfg (bodies Q R))
      (match Q hf with
        | none => (.stop .trap : Res (TCfg V) V)
        | some (_, hbody) =>
          .next ⟨h ++ [some buf], .normal,
            ⟨hbody, .cont h.length :: p⟩ :: ⟨.chk :: c, ops⟩ :: rest⟩)
      (match annP Q hf with
        | none => (.stop .trap : Res (FCfg V) V)
        | some (_, hbody) =>
          .next ⟨h' ++ [some buf'], 0, t, p, buf',
            ⟨hbody, .cont h'.length :: p⟩ ::
              ⟨.chk fn (2 * pc + 1) :: ann fn (pc + 1) c, ops⟩ :: rest'⟩) := by
  have hlen : h.length = h'.length := hh.length_eq
  cases hQ : Q hf with
  | none => simp only [annP_none hQ]; exact .stop _
  | some x =>
    obtain ⟨np, hbody⟩ := x
    simp only [annP_some hQ, hlen]
    exact .next ⟨forall₂_append_one hh (.some hbuf),
      .cons ⟨rcode_entry (bodies_succ hQ), rfl⟩
        (.cons ⟨⟨fn, body, pc, hb, .inr ⟨hs, c, hd, rfl, rfl⟩⟩, rfl⟩ hr), rfl⟩

section unwind

variable {h : List (Option (List (TFrame V)))} {h' : List (Option (List (Rec V)))}
  {buf : List (TFrame V)} {buf' : List (Rec V)} {rest : List (TFrame V)}
  {rest' : List (AFrame V)}

/-- An unwinding step at an `rchk`. -/
theorem lock_unwind_rchk (hh : HRel (bodies Q R) h h') (t : Nat) (p : List (SV V))
    (hbuf : List.Forall₂ (RRec (bodies Q R)) buf buf') (ops : List (SV V))
    {c : List (TIns V)} {hs : List Clause} {fn pc : Nat} {body : List (TIns V)}
    (hb : bodies Q R fn = some body) (hd : body.drop pc = .rchk hs :: c)
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') :
    ResRel (RCfg (bodies Q R)) (tunwind Q h t p buf ⟨.rchk hs :: c, ops⟩ rest)
      (funwind (annP Q) h' t p buf' ⟨annI fn pc (.rchk hs) :: ann fn (pc + 1) c, ops⟩ rest') := by
  have hrec : RRec (bodies Q R) ⟨.rchk hs :: c, ops⟩ ⟨fn, 2 * pc, ops⟩ := hd ▸ rrec_even hb ops
  simp only [tunwind, funwind, annI]
  cases lookup t hs with
  | none => exact .next ⟨hh, hr, rfl, rfl, rfl, forall₂_append_one hbuf hrec⟩
  | some hf => exact lock_handle hh hbuf hf hb hd hr

/-- An unwinding step at a frame whose code is related to the code at `pc`. -/
theorem lock_unwind_at (hh : HRel (bodies Q R) h h') (t : Nat) (p : List (SV V))
    (hbuf : List.Forall₂ (RRec (bodies Q R)) buf buf') (ops : List (SV V)) {i : TIns V}
    {c : List (TIns V)} {fn pc : Nat} {body : List (TIns V)} (hb : bodies Q R fn = some body)
    (hd : body.drop pc = i :: c) (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') :
    ResRel (RCfg (bodies Q R)) (tunwind Q h t p buf ⟨i :: c, ops⟩ rest)
      (funwind (annP Q) h' t p buf' ⟨annI fn pc i :: ann fn (pc + 1) c, ops⟩ rest') := by
  cases i with
  | chk =>
    have hrec : RRec (bodies Q R) ⟨.chk :: c, ops⟩ ⟨fn, 2 * pc, ops⟩ := hd ▸ rrec_even hb ops
    exact .next ⟨hh, hr, rfl, rfl, rfl, forall₂_append_one hbuf hrec⟩
  | rchk hs => exact lock_unwind_rchk hh t p hbuf ops hb hd hr
  | push _ | prim _ _ | drop | call _ | cond _ _ | alloc _ | startRewind _ | startUnwind _ _ =>
    exact .stop _

/-- **One unwinding step.** -/
theorem lock_unwind (hh : HRel (bodies Q R) h h') (t : Nat) (p : List (SV V))
    (hbuf : List.Forall₂ (RRec (bodies Q R)) buf buf') (code : List (TIns V))
    (code' : List (AIns V)) (ops : List (SV V)) (hc : RCode (bodies Q R) code code')
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') :
    ResRel (RCfg (bodies Q R)) (tunwind Q h t p buf ⟨code, ops⟩ rest)
      (funwind (annP Q) h' t p buf' ⟨code', ops⟩ rest') := by
  cases code with
  | nil => rw [rcode_nil hc]; exact .stop _
  | cons i c =>
    obtain ⟨fn, body, pc, hb, -, ⟨hd, rfl⟩ | ⟨hs, hd, rfl, rfl⟩⟩ := rcode_cons hc
    · exact lock_unwind_at hh t p hbuf ops hb hd hr
    · exact .next ⟨hh, hr, rfl, rfl, rfl, forall₂_append_one hbuf (rrec_odd hb hd ops)⟩

end unwind

/-- A step in normal mode. -/
theorem lock_normal (test : V → Bool) {h : List (Option (List (TFrame V)))}
    {h' : List (Option (List (Rec V)))} (hh : HRel (bodies Q R) h h') (t : Nat)
    (p : List (SV V)) (b : List (Rec V)) {code : List (TIns V)} {code' : List (AIns V)}
    (ops : List (SV V)) (hc : RCode (bodies Q R) code code') {rest : List (TFrame V)}
    {rest' : List (AFrame V)} (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') :
    ResRel (RCfg (bodies Q R)) (tstep Q test ⟨h, .normal, ⟨code, ops⟩ :: rest⟩)
      (fstep (annP Q) (bodies Q R) test ⟨h', 0, t, p, b, ⟨code', ops⟩ :: rest'⟩) := by
  cases code with
  | nil =>
    rw [rcode_nil hc]
    cases hr with
    | nil => exact .stop _
    | cons hb hrest => exact .next ⟨hh, .cons ⟨hb.1, by rw [hb.2]⟩ hrest, rfl⟩
  | cons i c =>
    obtain ⟨fn, body, pc, hb, hdc, ⟨hd, rfl⟩ | ⟨hs, hd, rfl, rfl⟩⟩ := rcode_cons hc
    · exact lock_exec test hh t p b (i :: c) _ ops hb hd hr
    · exact .next ⟨hh, .cons ⟨rcode_suffix hb hdc, rfl⟩ hr, rfl⟩

theorem lock_normal_fr (test : V → Bool) {h : List (Option (List (TFrame V)))}
    {h' : List (Option (List (Rec V)))} (hh : HRel (bodies Q R) h h') (t : Nat)
    (p : List (SV V)) (b : List (Rec V)) {fr : TFrame V} {fa : AFrame V}
    (hfr : RFr (bodies Q R) fr fa) {rest : List (TFrame V)} {rest' : List (AFrame V)}
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') :
    ResRel (RCfg (bodies Q R)) (tstep Q test ⟨h, .normal, fr :: rest⟩)
      (fstep (annP Q) (bodies Q R) test ⟨h', 0, t, p, b, fa :: rest'⟩) := by
  obtain ⟨code, ops⟩ := fr
  obtain ⟨code', ops'⟩ := fa
  obtain ⟨hc, rfl⟩ := hfr
  exact lock_normal test hh t p b ops hc hr

theorem lock_unwind_fr {h : List (Option (List (TFrame V)))}
    {h' : List (Option (List (Rec V)))} (hh : HRel (bodies Q R) h h') (t : Nat)
    (p : List (SV V)) {buf : List (TFrame V)} {buf' : List (Rec V)}
    (hbuf : List.Forall₂ (RRec (bodies Q R)) buf buf') {fr : TFrame V} {fa : AFrame V}
    (hfr : RFr (bodies Q R) fr fa) {rest : List (TFrame V)} {rest' : List (AFrame V)}
    (hr : List.Forall₂ (RFr (bodies Q R)) rest rest') :
    ResRel (RCfg (bodies Q R)) (tunwind Q h t p buf fr rest)
      (funwind (annP Q) h' t p buf' fa rest') := by
  obtain ⟨code, ops⟩ := fr
  obtain ⟨code', ops'⟩ := fa
  obtain ⟨hc, rfl⟩ := hfr
  exact lock_unwind hh t p hbuf code code' ops hc hr

/-- A rewinding step. -/
theorem lock_rewind (test : V → Bool) {h : List (Option (List (TFrame V)))}
    {h' : List (Option (List (Rec V)))} (hh : HRel (bodies Q R) h h') (t : Nat)
    (args : List (SV V)) {pend : List (TFrame V)} {buf : List (Rec V)}
    (hbuf : List.Forall₂ (RRec (bodies Q R)) pend buf) {st : List (TFrame V)}
    {st' : List (AFrame V)} (hst : List.Forall₂ (RFr (bodies Q R)) st st') :
    ResRel (RCfg (bodies Q R)) (tstep Q test ⟨h, .rewind pend args, st⟩)
      (fstep (annP Q) (bodies Q R) test ⟨h', 2, t, args, buf, st'⟩) := by
  cases hbuf with
  | nil => exact .stop _
  | cons hq htail =>
    obtain ⟨hops, c', hdisp, hrc⟩ := hq
    cases htail with
    | nil =>
      simp only [tstep, fstep, hdisp]
      exact .next ⟨hh, .cons ⟨hrc, by rw [hops]⟩ hst, rfl⟩
    | cons hq' htail' =>
      simp only [tstep, fstep, hdisp]
      exact .next ⟨hh, .cons ⟨hrc, hops⟩ hst, rfl, rfl, .cons hq' htail'⟩

/-- **Lock step.** -/
theorem lock_step (test : V → Bool) (x : TCfg V) (y : FCfg V) (hxy : RCfg (bodies Q R) x y) :
    ResRel (RCfg (bodies Q R)) (tstep Q test x) (fstep (annP Q) (bodies Q R) test y) := by
  obtain ⟨h, m, st⟩ := x
  obtain ⟨h', m', t', p', b', st'⟩ := y
  obtain ⟨hh, hst, hm⟩ := hxy
  cases m with
  | normal =>
    obtain rfl : m' = 0 := hm
    cases hst with
    | nil => exact .stop _
    | cons hfr hrest => exact lock_normal_fr test hh t' p' b' hfr hrest
  | unwind t p buf =>
    obtain ⟨rfl, rfl, rfl, hbuf⟩ := hm
    cases hst with
    | nil => exact .stop _
    | cons hfr hrest => exact lock_unwind_fr hh t' p' hbuf hfr hrest
  | rewind pend args =>
    obtain ⟨rfl, rfl, hbuf⟩ := hm
    exact lock_rewind test hh t' p' hbuf hst

/-- **Equal behaviours.** -/
theorem beh_eq_pc (test : V → Bool) {x : TCfg V} {y : FCfg V} (hxy : RCfg (bodies Q R) x y) :
    beh (tstep Q test) x = beh (fstep (annP Q) (bodies Q R) test) y :=
  beh_eq_of_lock (lock_step test) hxy

/-- The initial configurations are related. -/
theorem rcfg_init (f : Nat) (args : List (SV V)) :
    RCfg (bodies Q (rootCode f)) (tInit f args) (fInit f args) :=
  ⟨.nil, .cons ⟨rcode_entry (fn := 0) rfl, rfl⟩ .nil, rfl⟩

end Silmaril.Proofs.Wasm.Models.FXAsyncPC
