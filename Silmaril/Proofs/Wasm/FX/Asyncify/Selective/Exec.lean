module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Selective.Rel
public import Silmaril.Wasm.FX.Asyncify.RelSim.Thms

/-!
# Selective instrumentation: one normal-mode instruction

For each instruction `i` of the top frame, the optimized step (`texec (optP S Q)` on the code
`opt S (after S i) c`) and the instrumented step (`texec Q` on `c`) give related results
(`texec_rel`). Calls of functions in `S` leave a flagged frame (`tcall_rel`); `startUnwind` and
`startRewind` are not safe, so no frame below them is flagged (`forall₂_of_stk`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Selective

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.RelSim Silmaril.Wasm.FX.Asyncify.Selective

variable {V : Type} {S : Nat → Bool} {Q : Prog (TIns V)} {test : V → Bool}

/-- Related heaps: pointwise, with unflagged frames. -/
abbrev HR (S : Nat → Bool) (h' h : List (Option (List (TFrame V)))) : Prop :=
  List.Forall₂ (Option.Rel (List.Forall₂ (FR S false))) h' h

theorem sr_normal {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h)
    {c : List (TIns V)} {ops : List (SV V)} {os us : List (TFrame V)}
    (hstk : Stk S (SafeCode S c) os us) :
    SR S ⟨h', .normal, ⟨opt S false c, ops⟩ :: os⟩ ⟨h, .normal, ⟨c, ops⟩ :: us⟩ :=
  ⟨hh, trivial, ⟨rfl, rfl⟩, hstk⟩

theorem stk_next {i : TIns V} {c : List (TIns V)} {os us : List (TFrame V)}
    (h : Stk S (SafeCode S (i :: c)) os us) : Stk S (SafeCode S c) os us :=
  stk_mono (stk_step h (B := True) fun _ => trivial) fun h' => h'.2

theorem body_safe (hQ : SafeProg S Q) {f np : Nat} {body : List (TIns V)}
    (hq : Q f = some (np, body)) (hf : S f = true) : SafeCode S body := by
  obtain ⟨np', body', hq', hs⟩ := hQ f hf
  have he : some (np, body) = some (np', body') := hq.symm.trans hq'
  cases he
  exact hs

theorem optP_some {f np : Nat} {body : List (TIns V)} (hq : Q f = some (np, body)) :
    optP S Q f = some (np, opt S false body) := by
  simp only [optP, hq, Option.map_some]

theorem optP_none {f : Nat} (hq : Q f = none) : optP S Q f = none := by
  simp only [optP, hq, Option.map_none]

/-- **A call**, leaving the caller's frame with flag `b` (set only for a function in `S`). -/
theorem tcall_rel (hQ : SafeProg S Q) {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h)
    {i : TIns V} {f : Nat} {b : Bool} (hb : b = true → S f = true)
    (hsafe : safeI S i = true → S f = true) {c : List (TIns V)} {os us : List (TFrame V)}
    (hstk : Stk S (SafeCode S (i :: c)) os us) (ops : List (SV V)) :
    RRes (SR S) (tcall (optP S Q) h' f ops (opt S b c) os) (tcall Q h f ops c us) := by
  rcases hq : Q f with _ | ⟨np, body⟩
  · show RRes (SR S) (tcall (optP S Q) h' f ops (opt S b c) os) (tcall Q h f ops c us)
    simp only [tcall, hq, optP_none hq]
    exact .stop _
  · show RRes (SR S) (tcall (optP S Q) h' f ops (opt S b c) os) (tcall Q h f ops c us)
    have hbody : S f = true → SafeCode S body := body_safe hQ hq
    have htl : Stk S (SafeCode S body ∧ SafeCode S c) os us :=
      stk_step hstk fun h1 => hbody (hsafe h1)
    rcases hp : popN np ops with _ | ⟨args, o⟩
    · simp only [tcall, hq, optP_some hq, hp]
      exact .stop _
    · have hw : Stk S (SafeCode S body) (⟨opt S b c, o⟩ :: os) (⟨c, o⟩ :: us) :=
        .cons ⟨rfl, rfl⟩ (fun h1 => hbody (hb h1)) htl
      simp only [tcall, hq, optP_some hq, hp]
      exact .next ⟨hh, trivial, ⟨rfl, rfl⟩, hw⟩

theorem alloc_rel {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h) {f : Nat}
    {c : List (TIns V)} {os us : List (TFrame V)} (hstk : Stk S (SafeCode S c) os us)
    (fo fu : TFrame V) (hops : fo.ops = fu.ops) :
    RRes (SR S) (texec (optP S Q) test h' fo (.alloc f) (opt S false c) os)
      (texec Q test h fu (.alloc f) c us) := by
  rcases hq : Q f with _ | ⟨np, body⟩
  · show RRes (SR S) (texec (optP S Q) test h' fo (.alloc f) (opt S false c) os) _
    simp only [texec, hq, optP_none hq]
    exact .stop _
  · show RRes (SR S) (texec (optP S Q) test h' fo (.alloc f) (opt S false c) os) _
    have hrec : Option.Rel (List.Forall₂ (FR S false)) (some [⟨opt S false body, []⟩])
        (some [⟨body, []⟩]) := .some (.cons ⟨rfl, rfl⟩ .nil)
    have hh' : HR S (h' ++ [some [⟨opt S false body, []⟩]]) (h ++ [some [⟨body, []⟩]]) :=
      forall₂_append_one hh hrec
    have hlen : h'.length = h.length := hh.length_eq
    simp only [texec, hq, optP_some hq, hops, hlen]
    exact .next (sr_normal hh' hstk)

theorem not_safe_of {i : TIns V} {c : List (TIns V)} (hi : safeI S i = false) :
    ¬SafeCode S (i :: c) := fun h => by
  have h1 : safeI S i = true := safeCode_head h
  rw [hi] at h1
  cases h1

/-- The records of a consumed continuation, for `startRewind`. -/
theorem rewind_lookup {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h) (k : Nat)
    {c : List (TIns V)} {o' : List (SV V)} {os us : List (TFrame V)}
    (hall : List.Forall₂ (FR S false) os us) (args : List (SV V)) :
    RRes (SR S)
      (match h'[k]? with
        | some (some (top :: seg)) =>
          .next ⟨h'.set k none, .rewind (top :: seg).reverse args, ⟨opt S false c, o'⟩ :: os⟩
        | _ => (.stop .trap : Res (TCfg V) V))
      (match h[k]? with
        | some (some (top :: seg)) =>
          .next ⟨h.set k none, .rewind (top :: seg).reverse args, ⟨c, o'⟩ :: us⟩
        | _ => (.stop .trap : Res (TCfg V) V)) := by
  have hk : Option.Rel (Option.Rel (List.Forall₂ (FR S false))) h'[k]? h[k]? :=
    forall₂_getElem? hh k
  have hset : HR S (h'.set k none) (h.set k none) := forall₂_set hh .none k
  have hst : List.Forall₂ (FR S false) (⟨opt S false c, o'⟩ :: os) (⟨c, o'⟩ :: us) :=
    .cons ⟨rfl, rfl⟩ hall
  generalize h'[k]? = a at hk ⊢
  generalize h[k]? = b at hk ⊢
  cases hk with
  | none => exact .stop _
  | some hk' =>
    cases hk' with
    | none => exact .stop _
    | some hl =>
      cases hl with
      | nil => exact .stop _
      | cons htop hseg => exact .next ⟨hset, ⟨rfl, forall₂_reverse (.cons htop hseg)⟩, hst⟩

theorem startRewind_rel {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h) {n : Nat}
    {c : List (TIns V)} {os us : List (TFrame V)}
    (hstk : Stk S (SafeCode S (.startRewind n :: c)) os us) (fo fu : TFrame V)
    (hops : fo.ops = fu.ops) :
    RRes (SR S) (texec (optP S Q) test h' fo (.startRewind n) (opt S false c) os)
      (texec Q test h fu (.startRewind n) c us) := by
  have hall : List.Forall₂ (FR S false) os us := forall₂_of_stk hstk (not_safe_of rfl)
  simp only [texec, hops]
  rcases fu.ops with _ | ⟨_ | k, o⟩
  · exact .stop _
  · exact .stop _
  · dsimp only
    rcases popN n o with _ | ⟨args, o'⟩
    · exact .stop _
    · exact rewind_lookup hh k hall args

theorem startUnwind_rel {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h) {t n : Nat}
    {c : List (TIns V)} {os us : List (TFrame V)}
    (hstk : Stk S (SafeCode S (.startUnwind t n :: c)) os us) (fo fu : TFrame V)
    (hops : fo.ops = fu.ops) :
    RRes (SR S) (texec (optP S Q) test h' fo (.startUnwind t n) (opt S false c) os)
      (texec Q test h fu (.startUnwind t n) c us) := by
  have hall : List.Forall₂ (FR S false) os us := forall₂_of_stk hstk (not_safe_of rfl)
  simp only [texec, hops]
  rcases popN n fu.ops with _ | ⟨p, o⟩
  · exact .stop _
  · exact .next ⟨hh, ⟨rfl, rfl, .cons ⟨rfl, rfl⟩ .nil⟩, hall⟩

theorem prim_rel {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h) {n : Nat}
    {op : List V → List V} {c : List (TIns V)} {os us : List (TFrame V)}
    (hstk : Stk S (SafeCode S c) os us) (fo fu : TFrame V) (hops : fo.ops = fu.ops) :
    RRes (SR S) (texec (optP S Q) test h' fo (.prim n op) (opt S false c) os)
      (texec Q test h fu (.prim n op) c us) := by
  simp only [texec, hops]
  rcases popN n fu.ops with _ | ⟨a, o⟩
  · exact .stop _
  · dsimp only
    rcases allVals a with _ | vs
    · exact .stop _
    · exact .next (sr_normal hh hstk)

theorem drop_rel {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h)
    {c : List (TIns V)} {os us : List (TFrame V)}
    (hstk : Stk S (SafeCode S c) os us) (fo fu : TFrame V) (hops : fo.ops = fu.ops) :
    RRes (SR S) (texec (optP S Q) test h' fo .drop (opt S false c) os)
      (texec Q test h fu .drop c us) := by
  simp only [texec, hops]
  rcases fu.ops with _ | ⟨_, o⟩
  · exact .stop _
  · exact .next (sr_normal hh hstk)

theorem cond_rel (hQ : SafeProg S Q) {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h)
    {f g : Nat} {c : List (TIns V)} {os us : List (TFrame V)}
    (hstk : Stk S (SafeCode S (.cond f g :: c)) os us) (fo fu : TFrame V)
    (hops : fo.ops = fu.ops) :
    RRes (SR S) (texec (optP S Q) test h' fo (.cond f g) (opt S (S f && S g) c) os)
      (texec Q test h fu (.cond f g) c us) := by
  have hpick : ∀ v : V, (S f && S g) = true → S (if test v then f else g) = true := by
    intro v hfg
    have hf : S f = true ∧ S g = true := Bool.and_eq_true_iff.mp hfg
    split
    · exact hf.1
    · exact hf.2
  simp only [texec, hops]
  rcases fu.ops with _ | ⟨v | _, o⟩
  · exact .stop _
  · exact tcall_rel (i := .cond f g) hQ hh (hpick v) (hpick v) hstk o
  · exact .stop _

/-- **One normal-mode instruction.** -/
theorem texec_rel (hQ : SafeProg S Q) {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h)
    {i : TIns V} {c : List (TIns V)} {os us : List (TFrame V)}
    (hstk : Stk S (SafeCode S (i :: c)) os us) (fo fu : TFrame V) (hops : fo.ops = fu.ops) :
    RRes (SR S) (texec (optP S Q) test h' fo i (opt S (after S i) c) os)
      (texec Q test h fu i c us) := by
  cases i with
  | push v => simp only [texec, hops]; exact .next (sr_normal hh (stk_next hstk))
  | prim n op => exact prim_rel hh (stk_next hstk) fo fu hops
  | drop => exact drop_rel hh (stk_next hstk) fo fu hops
  | call f => simp only [texec, hops]; exact tcall_rel hQ hh id id hstk fu.ops
  | cond f g => exact cond_rel hQ hh hstk fo fu hops
  | alloc f => exact alloc_rel hh (stk_next hstk) fo fu hops
  | startRewind n => exact startRewind_rel hh hstk fo fu hops
  | startUnwind t n => exact startUnwind_rel hh hstk fo fu hops
  | chk => simp only [texec, hops]; exact .next (sr_normal hh (stk_next hstk))
  | rchk hs => simp only [texec, hops]; exact .next (sr_normal hh (stk_next hstk))

end Silmaril.Proofs.Wasm.FX.Asyncify.Selective
