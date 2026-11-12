module

public import Silmaril.Wasi.Versions.Adapter.Strict.Defs
public import Silmaril.Wasi.Versions.Adapter.Thms

@[expose] public section

/-!
# The adapter is not a model of the strict descriptor theory

PROVED:

* `pStep_step`, `oStep_step`, **`drive_reach`**: driving a stateful component yields a reachable
  play.
* `strictPlay_reach`: the play `strictPlay` (`fd_close(1)`, then `fd_write(1, [])`) is a play of
  the adapter; `strictPlay_p2Th`: its host answers satisfy the adapter's 0.2 theory `p2Th`;
  `strictPlay_returns`: the adapter answers `ok` and then `ok(0)`.
* `strictPlay_th`: its returns satisfy the preview1 theory `P1.th` (whose descriptor sentences
  exempt empty iovec lists, as `adapter_sat` requires).
* **`adapter_not_strict`**: `¬ (agP p2Th (retG P1.fdsStrict)).holds adapter`: the adapter is not
  an implementation of the strict descriptor theory, refuted by `strictPlay`.
-/

namespace Silmaril.Wasi.Versions

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

variable {S : Type} {I X : Set FnName}

/-- The component's own move is a move. -/
theorem pStep_step {h : SBody S I X} {c c' : SCSt S I X} {o : Move (nsig I) (nsig X)}
    (hp : pStep c = some (o, c')) : SStep h c o c' := by
  match c, hp with
  | .run q (.call m k), hp =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
    exact .call q m k
  | .run q (.pure (s, r)), hp =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
    exact .ret q s r

/-- An Opponent input is a move. -/
theorem oStep_step {h : SBody S I X} {c c' : SCSt S I X} {i : In X} {o : Move (nsig I) (nsig X)}
    (hp : oStep h c i = some (o, c')) : SStep h c o c' := by
  match c, i, hp with
  | .idle s, .call q, hp =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
    exact .ask s q
  | .wait q m k, .ans n, hp =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
    exact .reply q m k n

/-- **Driving a stateful component yields a reachable play.** -/
theorem drive_reach {h : SBody S I X} {s₀ : S} :
    ∀ (is : List (In X)) {t : List (Move (nsig I) (nsig X))} {c : SCSt S I X},
      SReach h s₀ t c → SReach h s₀ (t ++ (drive h c is).1) (drive h c is).2
  | [], t, c, ht => by simpa [drive] using ht
  | i :: is, t, c, ht => by
    cases ho : oStep h c i with
    | none => simpa [drive, ho] using ht
    | some oc =>
      have h1 : SReach h s₀ (t ++ [oc.1]) oc.2 := ht.snoc (oStep_step ho)
      cases hp : pStep oc.2 with
      | none =>
        have h2 := drive_reach is h1
        simpa [drive, ho, hp] using h2
      | some oc' =>
        have h2 : SReach h s₀ (t ++ [oc.1] ++ [oc'.1]) oc'.2 := h1.snoc (pStep_step hp)
        have h3 := drive_reach is h2
        simpa [drive, ho, hp] using h3

namespace Adapter

/-- `strictPlay` is a play of the adapter. -/
theorem strictPlay_reach : ∃ c, SReach body ASt.init strictPlay c :=
  ⟨_, (List.nil_append _) ▸ drive_reach (h := body) strictIns SReach.nil⟩

/-- The host's answers in `strictPlay` satisfy the adapter's 0.2 theory. -/
theorem strictPlay_p2Th : p2Th.Accepts (hostView (wtrace strictPlay)) :=
  (Protocol.acceptsB_iff _ _).1 (by decide)

/-- The adapter's returns in `strictPlay`: `fd_close(1)` is `ok`, `fd_write(1, [])` is
`ok(0)`. -/
theorem strictPlay_returns : retAsImp (wtrace strictPlay) =
    [.imp (P1.fn "fd_close") [.u32 1] (P1.okAns none),
     .imp (P1.fn "fd_write") [.u32 1, .record []] (P1.okAns (sizeV 0))] := by
  rfl

/-- The returns satisfy the preview1 theory (empty iovec lists are exempt). -/
theorem strictPlay_th : (retG P1.th).Accepts (wtrace strictPlay) :=
  (Protocol.acceptsB_iff _ _).1 (by decide)

/-- The returns violate the strict descriptor theory: success on a closed descriptor. -/
theorem strictPlay_not_strict : ¬ (retG P1.fdsStrict).Accepts (wtrace strictPlay) := fun h =>
  absurd ((Protocol.acceptsB_iff _ _).2 h) (by decide)

/-- **The adapter is not an implementation of the strict descriptor theory.** -/
theorem adapter_not_strict : ¬ (agP p2Th (retG P1.fdsStrict)).holds adapter := fun h =>
  let ⟨c, hc⟩ := strictPlay_reach
  strictPlay_not_strict (h _ ⟨c, hc⟩ strictPlay_p2Th)

end Adapter

end Silmaril.Wasi.Versions
