module

public import Silmaril.Wasm.Spec.Harness.Defs

@[expose] public section

/-!
# Harness reduction: proofs

Prefix closure of linked traces, the per-trace reading of pulled sentences, and soundness and
completeness of the most general return-postcondition harness. Summary in
`Silmaril.Wasm.Spec.Harness.Thms`.
-/

namespace Silmaril.Wasm.Spec

variable {Ty A R : Type} {Xp Xh Xl : Iface Ty} {W : Wiring Xp Xh Xl}

/-! ## Linked traces -/

/-- A prefix of a linked trace is a linked trace of prefixes. -/
theorem Link.of_prefix :
    ∀ {tp : List (Event A R Xp)} {th : List (Event A R Xh)} {tl s : List (Event A R Xl)},
      Link W tp th tl → s <+: tl → ∃ tp', tp' <+: tp ∧ ∃ th', th' <+: th ∧ Link W tp' th' s
  | _, _, _, s, .nil, hs => by
    rw [List.prefix_nil.1 hs]
    exact ⟨[], List.nil_prefix, [], List.nil_prefix, .nil⟩
  | _, _, _, s, .pimp e h, hs => by
    rcases s with _ | ⟨x, s⟩
    · exact ⟨[], List.nil_prefix, [], List.nil_prefix, .nil⟩
    · obtain ⟨rfl, hs'⟩ := List.cons_prefix_cons.1 hs
      obtain ⟨tp', htp, th', hth, hl⟩ := Link.of_prefix h hs'
      exact ⟨_, List.cons_prefix_cons.2 ⟨rfl, htp⟩, th', hth, .pimp e hl⟩
  | _, _, _, s, .hown e h, hs => by
    rcases s with _ | ⟨x, s⟩
    · exact ⟨[], List.nil_prefix, [], List.nil_prefix, .nil⟩
    · obtain ⟨rfl, hs'⟩ := List.cons_prefix_cons.1 hs
      obtain ⟨tp', htp, th', hth, hl⟩ := Link.of_prefix h hs'
      exact ⟨tp', htp, _, List.cons_prefix_cons.2 ⟨rfl, hth⟩, .hown e hl⟩
  | _, _, _, s, .hexp e h, hs => by
    rcases s with _ | ⟨x, s⟩
    · exact ⟨[], List.nil_prefix, [], List.nil_prefix, .nil⟩
    · obtain ⟨rfl, hs'⟩ := List.cons_prefix_cons.1 hs
      obtain ⟨tp', htp, th', hth, hl⟩ := Link.of_prefix h hs'
      exact ⟨tp', htp, _, List.cons_prefix_cons.2 ⟨rfl, hth⟩, .hexp e hl⟩
  | _, _, _, _, .sync e h, hs => by
    obtain ⟨tp', htp, th', hth, hl⟩ := Link.of_prefix h hs
    exact ⟨_, List.cons_prefix_cons.2 ⟨rfl, htp⟩, _, List.cons_prefix_cons.2 ⟨rfl, hth⟩,
      .sync e hl⟩

/-- **Linked trace sets of good trace sets are good.** -/
theorem Good.linkTraces {Tp : Set (List (Event A R Xp))} {Th : Set (List (Event A R Xh))}
    (hp : Good Tp) (hh : Good Th) : Good (Spec.linkTraces W Tp Th) where
  nil_mem := ⟨[], hp.nil_mem, [], hh.nil_mem, .nil⟩
  of_prefix := by
    rintro s t ⟨tp, htp, th, hth, hl⟩ hs
    obtain ⟨tp', htp', th', hth', hl'⟩ := Link.of_prefix hl hs
    exact ⟨tp', hp.of_prefix htp htp', th', hh.of_prefix hth hth', hl'⟩

/-- **The satisfaction condition of the harness corridor.** -/
theorem sat_link_iff (L : Logic Ty A R) (Tp : Set (List (Event A R Xp)))
    (Th : Set (List (Event A R Xh))) (ψ : L.Fm Xl) :
    (semLogic Ty A R).Sat Tp (pull W Th L ψ) ↔ L.Sat (Spec.linkTraces W Tp Th) ψ := Iff.rfl

/-- For per-trace sentences, the pulled property is the per-trace property `pullTrace`. -/
theorem ofTrace_sat_linkTraces_iff {Fm : Iface Ty → Type}
    {holds : ∀ {X : Iface Ty}, Fm X → List (Event A R X) → Prop}
    (Tp : Set (List (Event A R Xp))) (Th : Set (List (Event A R Xh))) (ψ : Fm Xl) :
    (Logic.ofTrace Fm holds).Sat (Spec.linkTraces W Tp Th) ψ ↔
      ∀ tp ∈ Tp, pullTrace W Th (holds ψ) tp := by
  constructor
  · intro h tp htp th hth tl hl
    exact h tl ⟨tp, htp, th, hth, hl⟩
  · rintro h tl ⟨tp, htp, th, hth, hl⟩
    exact h tp htp th hth tl hl

/-! ## The most general return-postcondition harness -/

namespace RetHarness

variable (H : RetHarness W A R)

/-- The harness traces are good. -/
theorem traces_good : Good H.traces where
  nil_mem := ⟨[], List.nil_prefix⟩
  of_prefix := fun ⟨u, hu⟩ hs => ⟨u, hs.trans hu⟩

/-- The program trace, the harness run mirroring it and their linked run are linked. -/
theorem link_drive : ∀ tp : List (Event A R Xp), Link W tp (H.drive (exportEvents tp)) (H.linkOf tp)
  | [] => .nil
  | .inl x :: tp => .pimp x (link_drive tp)
  | .inr (.ask j a) :: tp => .sync (.ask j a) (link_drive tp)
  | .inr (.ans j r) :: tp => by
    show Link W (.inr (.ans j r) :: tp) (.inl (.ans (W.ph j) r) ::
      ((if j = H.e then [.inl (.ask (W.oh H.chk) (H.verdict r)), .inl (.ans (W.oh H.chk) H.ok)]
        else []) ++ H.drive (exportEvents tp)))
      ((if j = H.e then [.inl (.ask (W.ol H.chk) (H.verdict r)), .inl (.ans (W.ol H.chk) H.ok)]
        else []) ++ H.linkOf tp)
    refine .sync (.ans j r) ?_
    by_cases hj : j = H.e
    · simp only [hj, ↓reduceIte, List.cons_append, List.nil_append]
      exact .hown (.ask H.chk (H.verdict r)) (.hown (.ans H.chk H.ok) (link_drive tp))
    · simp only [hj, ↓reduceIte, List.nil_append]
      exact link_drive tp

/-- Every return of `e` in the program trace is checked in the linked run. -/
theorem chk_mem_linkOf {r : R} :
    ∀ {tp : List (Event A R Xp)}, Event.ret H.e r ∈ tp →
      (Event.icall (W.ol H.chk) (H.verdict r) : Event A R Xl) ∈ H.linkOf tp
  | [], h => absurd h List.not_mem_nil
  | .inl x :: tp, h => by
    have h' : Event.ret H.e r ∈ tp := by
      rcases List.mem_cons.1 h with h | h
      · cases h
      · exact h
    exact List.mem_cons_of_mem _ (chk_mem_linkOf h')
  | .inr (.ask j a) :: tp, h => by
    have h' : Event.ret H.e r ∈ tp := by
      rcases List.mem_cons.1 h with h | h
      · cases h
      · exact h
    show _ ∈ H.linkOf tp
    exact chk_mem_linkOf h'
  | .inr (.ans j r') :: tp, h => by
    show _ ∈ (if j = H.e then [Event.icall (W.ol H.chk) (H.verdict r'),
      Event.iret (W.ol H.chk) H.ok] else []) ++ H.linkOf tp
    rcases List.mem_cons.1 h with h | h
    · simp only [Event.ret, Sum.inr.injEq, SideEv.ans.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · exact List.mem_append_right _ (chk_mem_linkOf h)

/-- A check in the linked run comes from the harness (the program's imports are not the check). -/
theorem Link.chk_mem (hpl : ∀ k, W.pl k ≠ W.ol H.chk) (hol : Function.Injective W.ol) {a : A} :
    ∀ {tp : List (Event A R Xp)} {th : List (Event A R Xh)} {tl : List (Event A R Xl)},
      Link W tp th tl → Event.icall (W.ol H.chk) a ∈ tl → Event.icall (W.oh H.chk) a ∈ th
  | _, _, _, .nil, h => absurd h List.not_mem_nil
  | _, _, _, .pimp x hl, h => by
    rcases List.mem_cons.1 h with h | h
    · rcases x with ⟨k, b⟩ | ⟨k, b⟩
      · simp only [SideEv.rename, Event.icall, Sum.inl.injEq, SideEv.ask.injEq] at h
        exact absurd h.1.symm (hpl k)
      · cases h
    · exact Link.chk_mem hpl hol hl h
  | _, _, _, .hown x hl, h => by
    rcases List.mem_cons.1 h with h | h
    · rcases x with ⟨k, b⟩ | ⟨k, b⟩
      · simp only [SideEv.rename, Event.icall, Sum.inl.injEq, SideEv.ask.injEq] at h
        obtain ⟨hk, rfl⟩ := h
        have hk' : k = H.chk := hol hk.symm
        subst hk'
        exact List.mem_cons_self
      · cases h
    · exact List.mem_cons_of_mem _ (Link.chk_mem hpl hol hl h)
  | _, _, _, .hexp x hl, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · exact List.mem_cons_of_mem _ (Link.chk_mem hpl hol hl h)
  | _, _, _, .sync x hl, h => List.mem_cons_of_mem _ (Link.chk_mem hpl hol hl h)

/-- A harness answer from the program comes from the program trace. -/
theorem Link.ph_mem (hph : ∀ j k, W.ph j ≠ W.oh k) (hinj : Function.Injective W.ph) {j : Xp.Exp}
    {r : R} : ∀ {tp : List (Event A R Xp)} {th : List (Event A R Xh)} {tl : List (Event A R Xl)},
      Link W tp th tl → (Event.iret (W.ph j) r : Event A R Xh) ∈ th → Event.ret j r ∈ tp
  | _, _, _, .nil, h => absurd h List.not_mem_nil
  | _, _, _, .pimp _ hl, h => List.mem_cons_of_mem _ (Link.ph_mem hph hinj hl h)
  | _, _, _, .hown x hl, h => by
    rcases List.mem_cons.1 h with h | h
    · rcases x with ⟨k, b⟩ | ⟨k, b⟩
      · cases h
      · simp only [SideEv.rename, Event.iret, Sum.inl.injEq, SideEv.ans.injEq] at h
        exact absurd h.1 (hph j k)
    · exact Link.ph_mem hph hinj hl h
  | _, _, _, .hexp _ hl, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · exact Link.ph_mem hph hinj hl h
  | _, _, _, .sync x hl, h => by
    rcases List.mem_cons.1 h with h | h
    · rcases x with ⟨k, b⟩ | ⟨k, b⟩
      · cases h
      · simp only [SideEv.rename, Event.iret, Sum.inl.injEq, SideEv.ans.injEq] at h
        obtain ⟨hk, rfl⟩ := h
        rw [hinj hk]
        exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (Link.ph_mem hph hinj hl h)

/-- The check block after a return of `e`: a check in a prefix of it, followed by more of the
harness run, is that return's check or a later one. -/
theorem chk_block {a : A} {r : R} {u : List (Event A R Xh)} {s : List (Event A R Xh)}
    (hs : s <+: Event.icall (W.oh H.chk) (H.verdict r) :: Event.iret (W.oh H.chk) H.ok :: u)
    (h : Event.icall (W.oh H.chk) a ∈ s) :
    a = H.verdict r ∨ ∃ s', s' <+: u ∧ Event.icall (W.oh H.chk) a ∈ s' ∧ s' ⊆ s := by
  rcases s with _ | ⟨y, s⟩
  · exact absurd h List.not_mem_nil
  · obtain ⟨rfl, hs₁⟩ := List.cons_prefix_cons.1 hs
    rcases List.mem_cons.1 h with h₁ | h₁
    · exact .inl (Sum.inl.inj h₁ |> SideEv.ask.inj).2
    · rcases s with _ | ⟨z, s⟩
      · exact absurd h₁ List.not_mem_nil
      · obtain ⟨rfl, hs₂⟩ := List.cons_prefix_cons.1 hs₁
        rcases List.mem_cons.1 h₁ with h₂ | h₂
        · cases h₂
        · refine .inr ⟨s, hs₂, h₂, fun x hx => ?_⟩
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)

/-- A check in a prefix of a harness run follows the return of `e` it checks. -/
theorem drive_chk (hph : ∀ j k, W.ph j ≠ W.oh k) {a : A} :
    ∀ (u : List (SideEv A R Xp.exports.length)) (s : List (Event A R Xh)), s <+: H.drive u →
      Event.icall (W.oh H.chk) a ∈ s → ∃ r, a = H.verdict r ∧ Event.iret (W.ph H.e) r ∈ s
  | [], s, hs, h => by
    have hnil : s = [] := List.prefix_nil.1 hs
    rw [hnil] at h
    exact absurd h List.not_mem_nil
  | _ :: _, [], _, h => absurd h List.not_mem_nil
  | .ask j b :: u, x :: s, hs, h => by
    obtain ⟨hx, hs'⟩ : x = .inl (.ask (W.ph j) b) ∧ s <+: H.drive u := List.cons_prefix_cons.1 hs
    rcases List.mem_cons.1 h with h | h
    · rw [hx] at h
      have hph' : W.oh H.chk = W.ph j := (Sum.inl.inj h |> SideEv.ask.inj).1
      exact absurd hph'.symm (hph j H.chk)
    · obtain ⟨r, hr, hm⟩ := drive_chk hph u s hs' h
      exact ⟨r, hr, List.mem_cons_of_mem _ hm⟩
  | .ans j r :: u, x :: s, hs, h => by
    have hs₀ := List.cons_prefix_cons.1 hs
    obtain ⟨hx, hs'⟩ : x = .inl (.ans (W.ph j) r) ∧ s <+: (if j = H.e then
        [Event.icall (W.oh H.chk) (H.verdict r), Event.iret (W.oh H.chk) H.ok] else []) ++
        H.drive u := hs₀
    have htail : Event.icall (W.oh H.chk) a ∈ s := by
      rcases List.mem_cons.1 h with h | h
      · rw [hx] at h
        cases h
      · exact h
    by_cases hj : j = H.e
    · show ∃ r', a = H.verdict r' ∧ Event.iret (W.ph H.e) r' ∈ x :: s
      have hs'' : s <+: Event.icall (W.oh H.chk) (H.verdict r) ::
          Event.iret (W.oh H.chk) H.ok :: H.drive u := by
        simpa only [hj, ↓reduceIte, List.cons_append, List.nil_append] using hs'
      have hhead : Event.iret (W.ph H.e) r ∈ x :: s := by
        rw [hx, ← hj]
        exact List.mem_cons_self
      rcases H.chk_block hs'' htail with ha | ⟨s', hs', hm, hsub⟩
      · exact ⟨r, ha, hhead⟩
      · obtain ⟨r', hr', hm'⟩ := drive_chk hph u s' hs' hm
        exact ⟨r', hr', List.mem_cons_of_mem _ (hsub hm')⟩
    · have hs'' : s <+: H.drive u := by
        simpa only [hj, ↓reduceIte, List.nil_append] using hs'
      obtain ⟨r', hr', hm⟩ := drive_chk hph u s hs'' htail
      exact ⟨r', hr', List.mem_cons_of_mem _ hm⟩

/-- **Soundness of the harness reduction**: if every linked run of the program trace with the
most general harness passes its checks, every return of `e` satisfies `Q`. -/
theorem sound {okArg : A → Prop} {Q : R → Prop} (hv : ∀ r, okArg (H.verdict r) → Q r)
    {tp : List (Event A R Xp)}
    (hpull : pullTrace W H.traces (CallPre.holds ⟨W.ol H.chk, okArg⟩) tp) :
    RetPost.holds ⟨H.e, Q⟩ tp := by
  intro r hr
  have hth : (.inr (.ask H.main H.arg) :: H.drive (exportEvents tp)) ∈ H.traces :=
    ⟨exportEvents tp, List.prefix_refl _⟩
  have hl : Link W tp (.inr (.ask H.main H.arg) :: H.drive (exportEvents tp))
      (.inr (.ask (W.hx H.main) H.arg) :: H.linkOf tp) :=
    .hexp (.ask H.main H.arg) (H.link_drive tp)
  have hchk : okArg (H.verdict r) :=
    hpull _ hth _ hl (H.verdict r) (List.mem_cons_of_mem _ (H.chk_mem_linkOf hr))
  exact hv r hchk

/-- **Completeness of the harness reduction**: if every return of `e` satisfies `Q`, every
linked run with the most general harness passes its checks (given that the check import is not
a program import, the program's exports are not harness-own imports, and the wiring is
injective where it must be). -/
theorem complete {okArg : A → Prop} {Q : R → Prop} (hv : ∀ r, Q r → okArg (H.verdict r))
    (hpl : ∀ k, W.pl k ≠ W.ol H.chk) (hol : Function.Injective W.ol)
    (hph : ∀ j k, W.ph j ≠ W.oh k) (hinj : Function.Injective W.ph) {tp : List (Event A R Xp)}
    (htp : RetPost.holds ⟨H.e, Q⟩ tp) :
    pullTrace W H.traces (CallPre.holds ⟨W.ol H.chk, okArg⟩) tp := by
  rintro th ⟨u, hu⟩ tl hl a ha
  have hth : Event.icall (W.oh H.chk) a ∈ th := Link.chk_mem H hpl hol hl ha
  obtain ⟨th', hth', hm⟩ : ∃ th', th' <+: H.drive u ∧ Event.icall (W.oh H.chk) a ∈ th' ∧
      th' ⊆ th := by
    rcases th with _ | ⟨y, th'⟩
    · exact absurd hth List.not_mem_nil
    · obtain ⟨rfl, hpre⟩ := List.cons_prefix_cons.1 hu
      rcases List.mem_cons.1 hth with h | h
      · cases h
      · exact ⟨th', hpre, h, fun x hx => List.mem_cons_of_mem _ hx⟩
  obtain ⟨r, rfl, hret⟩ := drive_chk H hph u th' hth' hm.1
  have hret' : Event.ret H.e r ∈ tp := Link.ph_mem hph hinj hl (hm.2 hret)
  exact hv r (htp r hret')

end RetHarness

end Silmaril.Wasm.Spec
