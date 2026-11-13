module

public import Silmaril.Wasm.Tools.Component.ValArgs.Defs

/-!
# The argument parser: laws

* `parse_nil`: no arguments parse to no options and no positionals;
* `parse_fits`: **every successful parse fits the command**: at most `maxPos` positionals,
  and every recorded option occurrence is one of the command's options (`Parsed.Fits`); so
  the subcommands never see an option or a positional their upstream counterpart lacks;
* `add_repeat`: a second occurrence of a non-repeatable option is refused;
* `input_dash`: the positional `-` reads stdin, like no positional.

Concrete behaviour on strings (clap's messages, clusters, `--name=value`) is tested by
`tools/wasm-tools/tests/compval/args.sh` against the pinned upstream binary: string functions
such as `String.startsWith` do not reduce in the kernel.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.ValArgs

/-- A parse result fits a command. -/
def Parsed.Fits (spec : CmdSpec) (p : Parsed) : Prop :=
  p.pos.length ≤ spec.maxPos ∧ ∀ x ∈ p.occs, ∃ o ∈ spec.opts, o.long = x.1

theorem fits_empty (spec : CmdSpec) : ({} : Parsed).Fits spec :=
  ⟨Nat.zero_le _, fun _ h => by simp at h⟩

theorem parse_nil (spec : CmdSpec) : parse spec [] = .ok {} := rfl

theorem add_fits {spec : CmdSpec} {p q : Parsed} {o : OptSpec} {v : String}
    (ho : o ∈ spec.opts) (hp : p.Fits spec) (h : p.add spec o v = .ok q) : q.Fits spec := by
  unfold Parsed.add at h
  split at h
  · cases h
  · cases h
    refine ⟨hp.1, fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hp.2 x hx
    · simp only [List.mem_singleton] at hx
      exact ⟨o, ho, by rw [hx]⟩

theorem add_repeat {spec : CmdSpec} {p : Parsed} {o : OptSpec} {v : String}
    (hm : o.multi = false) (hx : p.occs.any (·.1 == o.long) = true) :
    p.add spec o v = .error (repeated spec o) := by
  simp [Parsed.add, hm, hx]

theorem addPos_fits {spec : CmdSpec} {p q : Parsed} {a : String} (hp : p.Fits spec)
    (h : p.addPos spec a = .ok q) : q.Fits spec := by
  unfold Parsed.addPos at h
  split at h
  · next hl =>
    cases h
    exact ⟨by simp only [List.length_append, List.length_singleton]; omega, hp.2⟩
  · cases h

theorem find_mem {spec : CmdSpec} {f : OptSpec → Bool} {o : OptSpec}
    (h : spec.opts.find? f = some o) : o ∈ spec.opts := List.mem_of_find?_eq_some h

/-- An `Except` bind that succeeded came from a success of its first part. -/
theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem addNext_fits {spec : CmdSpec} {p q : Parsed} {o : OptSpec} {v : String}
    {rest rest' : List String} (ho : o ∈ spec.opts) (hp : p.Fits spec)
    (h : addNext spec p o v rest = .ok (.next q rest')) : q.Fits spec := by
  unfold addNext at h
  split at h
  · next q' hq => cases h; exact add_fits ho hp hq
  · cases h

theorem nextValue_fits {spec : CmdSpec} {p q : Parsed} {o : OptSpec}
    {rest rest' : List String} (ho : o ∈ spec.opts) (hp : p.Fits spec)
    (h : nextValue spec p o rest = .ok (.next q rest')) : q.Fits spec := by
  unfold nextValue at h
  split at h
  · split at h
    · cases h
    · exact addNext_fits ho hp h
  · cases h

theorem shortValue_fits {spec : CmdSpec} {p q : Parsed} {o : OptSpec}
    {cs : List Char} {rest rest' : List String} (ho : o ∈ spec.opts) (hp : p.Fits spec)
    (h : shortValue spec p o cs rest = .ok (.next q rest')) : q.Fits spec := by
  unfold shortValue at h
  split at h
  · exact nextValue_fits ho hp h
  · exact addNext_fits ho hp h
  · exact addNext_fits ho hp h

theorem longValue_fits {spec : CmdSpec} {p q : Parsed} {o : OptSpec}
    {inl : Option String} {rest rest' : List String} (ho : o ∈ spec.opts) (hp : p.Fits spec)
    (h : longValue spec p o inl rest = .ok (.next q rest')) : q.Fits spec := by
  unfold longValue at h
  split at h
  · exact addNext_fits ho hp h
  · cases h
  · exact addNext_fits ho hp h
  · exact nextValue_fits ho hp h

theorem shortCluster_fits (spec : CmdSpec) (whole : String) :
    ∀ (cs : List Char) (p q : Parsed) (rest rest' : List String), p.Fits spec →
      shortCluster spec p whole cs rest = .ok (.next q rest') → q.Fits spec
  | [], p, q, rest, rest', hp, h => by
    simp only [shortCluster, Except.ok.injEq, Step.next.injEq] at h
    rw [← h.1]; exact hp
  | c :: cs, p, q, rest, rest', hp, h => by
    unfold shortCluster at h
    split at h
    · cases h
    · split at h
      · cases h
      · next o ho =>
        have hm := find_mem ho
        split at h
        · split at h
          · next p' hp' => exact shortCluster_fits spec whole cs p' q rest rest' (add_fits hm hp hp') h
          · cases h
        · exact shortValue_fits hm hp h

theorem step_fits {spec : CmdSpec} {p q : Parsed} {a : String} {rest rest' : List String}
    (hp : p.Fits spec) (h : step spec p a rest = .ok (.next q rest')) : q.Fits spec := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · next o ho => exact longValue_fits (find_mem ho) hp h
    · split at h
      · exact shortCluster_fits spec a _ p q rest rest' hp h
      · split at h
        · next q' hq => cases h; exact addPos_fits hp hq
        · cases h

theorem allPos_fits (spec : CmdSpec) :
    ∀ (as : List String) (p q : Parsed), p.Fits spec → allPos spec p as = .ok q → q.Fits spec
  | [], p, q, hp, h => by cases h; exact hp
  | a :: as, p, q, hp, h => by
    obtain ⟨p', hp', hn⟩ := bind_ok h
    exact allPos_fits spec as p' q (addPos_fits hp hp') hn

theorem go_nil (spec : CmdSpec) (n : Nat) (p : Parsed) : go spec n p [] = .ok p := by
  cases n <;> rfl

theorem go_dash_fits {spec : CmdSpec} {p q : Parsed} {rest : List String} (hp : p.Fits spec)
    (h : (match allPos spec p rest with
      | .ok p => Outcome.ok p
      | .error e => .usage e) = .ok q) : q.Fits spec := by
  cases hq : allPos spec p rest with
  | ok q' =>
    rw [hq] at h
    cases h
    exact allPos_fits spec rest p _ hp hq
  | error e => rw [hq] at h; cases h

theorem go_fits (spec : CmdSpec) :
    ∀ (n : Nat) (p q : Parsed) (args : List String), p.Fits spec →
      go spec n p args = .ok q → q.Fits spec
  | n, p, q, [], hp, h => by
    rw [go_nil] at h
    cases h; exact hp
  | 0, _, _, _ :: _, _, h => by cases h
  | n + 1, p, q, a :: rest, hp, h => by
    unfold go at h
    split at h
    · exact go_dash_fits hp h
    · split at h
      · cases h
      · cases h
      · next p' rest' hs => exact go_fits spec n p' q rest' (step_fits hp hs) h

/-- **Every successful parse fits the command.** -/
theorem parse_fits {spec : CmdSpec} {args : List String} {p : Parsed}
    (h : parse spec args = .ok p) : p.Fits spec :=
  go_fits spec _ {} p args (fits_empty spec) h

theorem input_dash (p : Parsed) (rest : List String) :
    ({ p with pos := "-" :: rest } : Parsed).input? = none := rfl

end Silmaril.Wasm.Tools.Component.ValArgs
