module

public import Silmaril.Wasm.Component.Algebra.StreamGame.Defs
public import Silmaril.Wasm.Component.Algebra.Kahn.Thms
public import Silmaril.Wasm.Component.Algebra.Pipe.Thms
public import Mathlib.Logic.Function.Basic
public import Silmaril.Wasm.Component.Async.Thms
import Silmaril.Proofs.Wasm.Component.Algebra.StreamGame

/-!
# The concrete stream semantics: theorems

**The three conditions of `Algebra.StreamSem`**, proved for the Kahn semantics `den` of
`Silmaril.Wasm.Component.Algebra.StreamGame.Defs` (on `Val` items, width `1`):

* **`den_comp`**: `den (T.comp U) = (den T).comp (den U)`: composite transformers are denoted by
  composite strategies (`kahn_comp` and `ans_comp`);
* **`den_congr`**: `T ≈ₜ U → den T = den U` (`ans_congr`);
* **`den_id`**: `den Tr.id = Strategy.ofHandler (maskH 1)`: the identity transformer is copycat
  (`kahn_id` and `ans_id`).

**The pipeline lemmas of `Algebra.Pipe.Thms` without the `StreamSem` hypothesis**, for this
semantics: `Realizes.seq` (plugging realises composition), `Realizes.congr`, `Realizes.of_equiv`,
`Realizes.equiv`, `realizes_ident`, `realizes_pipe`, `seq_fuse`, `seq_commute`, `seq_map_map`,
`seq_filter_filter`, `seq_map_filter`, `seq_map_take` and `plug_realizes` (`wac plug` of two
stream components realises the composite transformer). These hold for every core semantics `C`;
the remaining hypotheses are the realisations of the stages, i.e. that the components'
denotations are the transformers' strategies.

**Refuted: a faithful `Algebra.StreamSem`.** `StreamSem.not_faithful`: every `StreamSem` (whose
`den` is defined on transformers between arbitrary types) identifies two inequivalent
transformers, by Cantor's theorem (there are more inequivalent transformers on `Set X` than
strategies `X`). This is why `den` is defined on `Val` items.
-/

public section

namespace Silmaril.Wasm.Component.Algebra.StreamGame

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Streams Silmaril.Wasm.Wac
open Silmaril.Wasm.Component.Algebra.Kahn
open Silmaril.Proofs.Wasm.Component.Algebra.StreamGame (ans_mono ans_comp ans_congr ans_id)

variable {σ τ ρ : Type}

/-! ## The conditions of a stream semantics -/

/-- **Composite transformers are denoted by composite strategies.** -/
theorem den_comp (T : Tr σ Val Val) (U : Tr τ Val Val) : den (T.comp U) = (den T).comp (den U) := by
  rw [den, den, den, kahn_comp (ans_mono T) (ans_mono U)]
  exact kahn_congr (ans_comp T U)

/-- **Equivalent transformers have the same strategy.** -/
theorem den_congr {T : Tr σ Val Val} {U : Tr τ Val Val} (h : T.Equiv U) : den T = den U :=
  kahn_congr (ans_congr h)

/-- **The identity transformer is copycat** on the stream interface. -/
theorem den_id : den (Tr.id : Tr Unit Val Val) = Strategy.ofHandler (maskH 1) := by
  rw [den, ← kahn_id]
  exact kahn_congr ans_id

/-! ## Realisations: the pipeline lemmas without hypothesis -/

variable {M : Type} [CoreModule M] {C : CoreSem M}

/-- **Plugging realises composition.** -/
theorem Realizes.seq {c d : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val}
    (hc : Realizes C c T) (hd : Realizes C d U) : Realizes C (Algebra.seq c d) (T.comp U) :=
  ⟨hc.1, (Algebra.sizes_seq c d).2.trans hd.2.1, by
    rw [Algebra.denU_seq, hc.2.2, hd.2.2, den_comp]⟩

/-- A realisation of `T` realises every transformer equivalent to `T`. -/
theorem Realizes.congr {c : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val}
    (hc : Realizes C c T) (h : T.Equiv U) : Realizes C c U :=
  ⟨hc.1, hc.2.1, hc.2.2.trans (den_congr h)⟩

/-- Components equivalent to a realisation are realisations. -/
theorem Realizes.of_equiv {c d : Comp M} {T : Tr σ Val Val} (hc : Realizes C c T)
    (h : Algebra.CompEquiv C c d) : Realizes C d T :=
  ⟨h.1.1 ▸ hc.1, h.1.2 ▸ hc.2.1, h.2 ▸ hc.2.2⟩

/-- **Realisations of equivalent transformers are equivalent components.** -/
theorem Realizes.equiv {c d : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val}
    (hc : Realizes C c T) (hd : Realizes C d U) (h : T.Equiv U) : Algebra.CompEquiv C c d :=
  ⟨⟨hc.1.trans hd.1.symm, hc.2.1.trans hd.2.1.symm⟩, by rw [hc.2.2, hd.2.2, den_congr h]⟩

/-- The identity component of a one-function interface realises the identity transformer. -/
theorem realizes_ident {I : Iface} (hI : I.length = 1) :
    Realizes C (Algebra.ident I : Comp M) (Tr.id : Tr Unit Val Val) :=
  ⟨hI, by
    simp only [Algebra.ident, Comp.exports_mk, Algebra.length_reexport, Algebra.ifaceExports,
      List.length_map, hI],
    by rw [Algebra.denU_ident, hI, den_id]⟩

/-- **A pipeline realises the composite of its stages.** -/
theorem realizes_pipe :
    ∀ {I : Iface} {cs : List (Comp M)} {ts : List (Σ σ : Type, Tr σ Val Val)},
      I.length = 1 → List.Forall₂ (fun c t => Realizes C c t.2) cs ts →
        Realizes C (Algebra.pipe I cs) (Algebra.chain ts).2
  | _, [], [], hI, .nil => realizes_ident hI
  | _, c :: _, _ :: _, _, .cons hc hs =>
    Realizes.seq hc (realizes_pipe ((Algebra.length_exportIface c).trans hc.2.1) hs)

/-- **Fusion**: if `T` then `U` is equivalent to `V`, plugging a realisation of `T` into one of
`U` is equivalent to a realisation of `V`. -/
theorem seq_fuse {c d e : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val} {V : Tr ρ Val Val}
    (hc : Realizes C c T) (hd : Realizes C d U) (he : Realizes C e V)
    (h : (T.comp U).Equiv V) : Algebra.CompEquiv C (Algebra.seq c d) e :=
  (Realizes.seq hc hd).equiv he h

/-- **Commutation of stages.** -/
theorem seq_commute {σ' τ' : Type} {c d c' d' : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val}
    {T' : Tr σ' Val Val} {U' : Tr τ' Val Val} (hc : Realizes C c T) (hd : Realizes C d U)
    (hc' : Realizes C c' T') (hd' : Realizes C d' U') (h : (T.comp U).Equiv (T'.comp U')) :
    Algebra.CompEquiv C (Algebra.seq c d) (Algebra.seq c' d') :=
  (Realizes.seq hc hd).equiv (Realizes.seq hc' hd') h

/-- **Map fusion**: `map f` plugged into `map g` is `map (g ∘ f)`. -/
theorem seq_map_map {f g : Val → Val} {c d e : Comp M} (hc : Realizes C c (Tr.map f))
    (hd : Realizes C d (Tr.map g)) (he : Realizes C e (Tr.map (g ∘ f))) :
    Algebra.CompEquiv C (Algebra.seq c d) e :=
  seq_fuse hc hd he (Tr.map_map f g)

/-- **Filter fusion**: `filter p` plugged into `filter q` is `filter (p ∧ q)`. -/
theorem seq_filter_filter {p q : Val → Bool} {c d e : Comp M}
    (hc : Realizes C c (Tr.filter p)) (hd : Realizes C d (Tr.filter q))
    (he : Realizes C e (Tr.filter fun x => p x && q x)) :
    Algebra.CompEquiv C (Algebra.seq c d) e :=
  seq_fuse hc hd he (Tr.filter_filter p q)

/-- **Filter after map** commutes to map after a filter on the original items. -/
theorem seq_map_filter {f : Val → Val} {p : Val → Bool} {c d c' d' : Comp M}
    (hc : Realizes C c (Tr.map f)) (hd : Realizes C d (Tr.filter p))
    (hc' : Realizes C c' (Tr.filter (p ∘ f))) (hd' : Realizes C d' (Tr.map f)) :
    Algebra.CompEquiv C (Algebra.seq c d) (Algebra.seq c' d') :=
  seq_commute hc hd hc' hd' (Tr.map_filter f p)

/-- **Take after map** commutes to map after take. -/
theorem seq_map_take {f : Val → Val} {n : Nat} {c d c' d' : Comp M}
    (hc : Realizes C c (Tr.map f)) (hd : Realizes C d (Tr.take (α := Val) n))
    (hc' : Realizes C c' (Tr.take (α := Val) n)) (hd' : Realizes C d' (Tr.map f)) :
    Algebra.CompEquiv C (Algebra.seq c d) (Algebra.seq c' d') :=
  seq_commute hc hd hc' hd' (Tr.map_take f n)

/-- **`wac plug` of two stream components realises the composite transformer**, when the
socket imports the plug's exports by name and in order. -/
theorem plug_realizes (P : Nat → Comp M) {T : Tr σ Val Val} {U : Tr τ Val Val}
    (h₀ : Realizes C (P 0) T) (h₁ : Realizes C (P 1) U)
    (hnames : Wac.names (P 1).imports = Wac.names (Algebra.exportIface (P 0)))
    (hn₀ : (Wac.names (P 0).imports).Nodup)
    (hne : (Wac.names (Algebra.exportIface (P 0))).Nodup)
    (hn₁ : (Wac.names (Algebra.exportIface (P 1))).Nodup) :
    Realizes C (Algebra.select (List.range (P 1).exports.length)
      ((Algebra.plugGraph fun k => Wac.sigOf (P k)).toComp P)) (T.comp U) :=
  (Realizes.seq h₀ h₁).of_equiv (Algebra.plug_equiv_seq_of_names C P hnames hn₀ hne hn₁).symm

/-! ## No faithful `StreamSem` -/

/-- **Every `StreamSem` identifies two inequivalent transformers.** Its `den` maps the
transformers `map (· = A)` on `Set (Strategy sigU sigU)`, which are pairwise inequivalent, into
`Strategy sigU sigU`; by Cantor's theorem the map is not injective. -/
theorem _root_.Silmaril.Wasm.Component.Algebra.StreamSem.not_faithful (S : Algebra.StreamSem C) :
    ∃ (α β : Type) (T U : Tr Unit α β), ¬ T.Equiv U ∧ S.den T = S.den U := by
  classical
  let X := Strategy sigU sigU
  let t : Set X → Tr Unit (Set X) Bool := fun A => Tr.map fun B => decide (B = A)
  have hinj : ¬ Function.Injective fun A => S.den (t A) := Function.cantor_injective _
  simp only [Function.Injective, not_forall] at hinj
  obtain ⟨A, B, hAB, hne⟩ := hinj
  refine ⟨Set X, Bool, t A, t B, fun hE => hne ?_, hAB⟩
  have h1 := (hE [A]).1
  simp [t, Tr.runP_map] at h1
  exact h1

/-! ## The moves are rendezvous of the stream built-ins -/

section Builtins

open Silmaril.Wasm.Component.Async

/-- **An item answer is a one-item rendezvous**: a pending `stream.read r 1` met by
`stream.write w [v]` receives exactly the items of `item v`, with `COMPLETED`, count 1. -/
theorem read_one_write {st : Store} {r w s : Nat} {v : Val}
    (hw : st.tbl w = some (.streamW s)) (hr : st.tbl r = some (.streamR s))
    (hp : (st.chans s).pend = .idle) (hd : (st.chans s).wDropped = false) :
    ∃ st₁ st₂, step st (.streamRead r 1) = some (st₁, .nat blocked) ∧
      step st₁ (.streamWrite w [v]) = some (st₂, .nat (packCopy .completed 1)) ∧
      st₂.ev r = some ⟨.streamRead, r, packCopy .completed 1, [v]⟩ ∧
      some (Payload.vals [v]) = item v := by
  obtain ⟨st₁, st₂, h₁, h₂, -, h₄⟩ := read_write (n := 1) (xs := [v]) hw hr hp hd
  exact ⟨st₁, st₂, h₁, h₂, h₄, rfl⟩

/-- **An end answer is a drop of the writable end**: a pending `stream.read` followed by
`stream.drop-writable` receives `DROPPED` and no items. -/
theorem read_dropW {st : Store} {r w s n : Nat}
    (hw : st.tbl w = some (.streamW s)) (hr : st.tbl r = some (.streamR s))
    (hp : (st.chans s).pend = .idle) (hd : (st.chans s).wDropped = false) :
    ∃ st₁ st₂, step st (.streamRead r n) = some (st₁, .nat blocked) ∧
      step st₁ (.streamDropW w) = some (st₂, .unit) ∧
      st₂.ev r = some ⟨.streamRead, r, packCopy .dropped 0, []⟩ := by
  have hrw : r ≠ w := by
    rintro rfl
    rw [hw] at hr
    cases hr
  simp [step, streamRead, streamDropW, hw, hr, hp, hd, Store.setChan, Store.post, Store.remove,
    upd, hrw]

end Builtins

end Silmaril.Wasm.Component.Algebra.StreamGame
