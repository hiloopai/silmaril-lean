module

public import Silmaril.Wasm.Component.Algebra.Pipe.Defs
public import Silmaril.Wasm.Component.Algebra.Plug.Thms
public import Silmaril.Wasm.Component.Streams.Laws.Thms

/-!
# Stream pipelines in the component algebra

Lemmas for the streams and WAC tracks: pipelines of components (`pipe`) and their laws, and,
for a compositional semantics of stream transformers (`StreamSem`, a hypothesis), the transfer
of the transformer laws of `Silmaril.Wasm.Component.Streams.Laws` to components through
`denU_seq`.

Without a stream semantics:

* `pipe_congr`: replacing every stage of a pipeline by an equivalent one gives an equivalent
  pipeline; `pipe_fuse`: two consecutive stages may be replaced by one stage equivalent to their
  plug (by `seq_assoc`); `ident_equiv`.

With a stream semantics `S` (every statement is conditional on `S`, of which no non-trivial
instance is constructed here; `StreamSem.trivial` only shows the conditions are consistent):

* `Realizes.seq`: **plugging realises composition**, `Realizes S c T → Realizes S d U →
  Realizes S (seq c d) (T.comp U)` (from `denU_seq` and `S.den_comp`);
* `realizes_pipe`: a pipeline realises the composite (`chain`) of its stages;
* `Realizes.equiv`: realisations of equivalent transformers are equivalent components;
  `Realizes.congr`, `Realizes.of_equiv`;
* **fusion and commutation**: `seq_fuse`, `seq_commute`, and the instances `seq_map_map`
  (map fusion), `seq_filter_filter`, `seq_map_filter` (filter after map is map after a filter),
  `seq_map_take` (take after map);
* `plug_realizes`: `wac plug` of two stream components realises the composite transformer
  (by `plug_equiv_seq_of_names`).
-/

public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Streams Silmaril.Wasm.Wac

variable {M : Type} [CoreModule M]

/-! ## Pipelines without a stream semantics -/

/-- Identity components of interfaces of the same size are equivalent. -/
theorem ident_equiv (C : CoreSem M) {I J : Iface} (h : I.length = J.length) :
    CompEquiv C (ident I : Comp M) (ident J) := by
  refine ⟨⟨h, ?_⟩, ?_⟩
  · simp only [ident, Comp.exports_mk, length_reexport, ifaceExports, List.length_map, h]
  · rw [denU_ident, denU_ident, h]

omit [CoreModule M] in
theorem length_exportIface (c : Comp M) : (exportIface c).length = c.exports.length :=
  List.length_map _

theorem forall₂_compEquiv_refl (C : CoreSem M) :
    ∀ cs : List (Comp M), List.Forall₂ (CompEquiv C) cs cs
  | [] => .nil
  | c :: cs => .cons (CompEquiv.refl C c) (forall₂_compEquiv_refl C cs)

/-- **Pipelines are congruent**: replacing every stage by an equivalent one gives an equivalent
pipeline. -/
theorem pipe_congr (C : CoreSem M) :
    ∀ {I J : Iface} {cs ds : List (Comp M)}, List.Forall₂ (CompEquiv C) cs ds →
      I.length = J.length → CompEquiv C (pipe I cs) (pipe J ds)
  | _, _, [], [], .nil, h => ident_equiv C h
  | _, _, c :: cs, d :: ds, .cons hcd hs, _ => by
    have hl : (exportIface c).length = (exportIface d).length := by
      rw [length_exportIface, length_exportIface, hcd.1.2]
    exact seq_congr hcd (pipe_congr C hs hl)

/-- **Fusion inside a pipeline**: two consecutive stages may be replaced by one stage
equivalent to their plug. -/
theorem pipe_fuse (C : CoreSem M) {c d e : Comp M} (hcde : CompEquiv C (seq c d) e) :
    ∀ (I : Iface) (cs ds : List (Comp M)),
      CompEquiv C (pipe I (cs ++ c :: d :: ds)) (pipe I (cs ++ e :: ds))
  | I, [], ds => by
    have hl : (exportIface d).length = (exportIface e).length := by
      rw [length_exportIface, length_exportIface, ← hcde.1.2, (sizes_seq c d).2]
    show CompEquiv C (seq c (seq d (pipe (exportIface d) ds))) (seq e (pipe (exportIface e) ds))
    exact (seq_assoc C c d _).symm.trans
      (seq_congr hcde (pipe_congr C (forall₂_compEquiv_refl C ds) hl))
  | I, b :: cs, ds =>
    seq_congr (CompEquiv.refl C b) (pipe_fuse C hcde (exportIface b) cs ds)

/-! ## Realisations of transformers -/

section Realizes

variable {C : CoreSem M} (S : StreamSem C)

/-- **Plugging realises composition** (through `denU_seq`). -/
theorem Realizes.seq {σ τ α β γ : Type} {c d : Comp M} {T : Tr σ α β} {U : Tr τ β γ}
    (hc : Realizes S c T) (hd : Realizes S d U) : Realizes S (Algebra.seq c d) (T.comp U) :=
  ⟨hc.1, (sizes_seq c d).2.trans hd.2.1, by rw [denU_seq, hc.2.2, hd.2.2, S.den_comp]⟩

/-- A realisation of `T` realises every transformer equivalent to `T`. -/
theorem Realizes.congr {σ τ α β : Type} {c : Comp M} {T : Tr σ α β} {U : Tr τ α β}
    (hc : Realizes S c T) (h : T.Equiv U) : Realizes S c U :=
  ⟨hc.1, hc.2.1, hc.2.2.trans (S.den_congr h)⟩

/-- Components equivalent to a realisation are realisations. -/
theorem Realizes.of_equiv {σ α β : Type} {c d : Comp M} {T : Tr σ α β} (hc : Realizes S c T)
    (h : CompEquiv C c d) : Realizes S d T :=
  ⟨h.1.1 ▸ hc.1, h.1.2 ▸ hc.2.1, h.2 ▸ hc.2.2⟩

/-- **Realisations of equivalent transformers are equivalent components.** -/
theorem Realizes.equiv {σ τ α β : Type} {c d : Comp M} {T : Tr σ α β} {U : Tr τ α β}
    (hc : Realizes S c T) (hd : Realizes S d U) (h : T.Equiv U) : CompEquiv C c d :=
  ⟨⟨hc.1.trans hd.1.symm, hc.2.1.trans hd.2.1.symm⟩, by rw [hc.2.2, hd.2.2, S.den_congr h]⟩

/-- The identity component of the stream interface realises the identity transformer. -/
theorem realizes_ident {α : Type} {I : Iface} (hI : I.length = S.width) :
    Realizes S (ident I : Comp M) (Tr.id : Tr Unit α α) :=
  ⟨hI, by simp only [ident, Comp.exports_mk, length_reexport, ifaceExports, List.length_map, hI],
    by rw [denU_ident, hI, S.den_id]⟩

/-- **A pipeline realises the composite of its stages.** -/
theorem realizes_pipe {α : Type} :
    ∀ {I : Iface} {cs : List (Comp M)} {ts : List (Σ σ : Type, Tr σ α α)},
      I.length = S.width → List.Forall₂ (fun c t => Realizes S c t.2) cs ts →
        Realizes S (pipe I cs) (chain ts).2
  | _, [], [], hI, .nil => realizes_ident S hI
  | _, c :: _, _ :: _, _, .cons hc hs =>
    Realizes.seq S hc (realizes_pipe ((length_exportIface c).trans hc.2.1) hs)

/-- **Fusion through `denU_seq`**: if `T` then `U` is equivalent to `V`, plugging a realisation
of `T` into one of `U` is equivalent to a realisation of `V`. -/
theorem seq_fuse {σ τ ρ α β γ : Type} {c d e : Comp M} {T : Tr σ α β} {U : Tr τ β γ}
    {V : Tr ρ α γ} (hc : Realizes S c T) (hd : Realizes S d U) (he : Realizes S e V)
    (h : (T.comp U).Equiv V) : CompEquiv C (Algebra.seq c d) e :=
  (Realizes.seq S hc hd).equiv S he h

/-- **Commutation of stages**: two plugs whose transformers compose to equivalent ones are
equivalent. -/
theorem seq_commute {σ τ σ' τ' α β β' γ : Type} {c d c' d' : Comp M} {T : Tr σ α β}
    {U : Tr τ β γ} {T' : Tr σ' α β'} {U' : Tr τ' β' γ} (hc : Realizes S c T)
    (hd : Realizes S d U) (hc' : Realizes S c' T') (hd' : Realizes S d' U')
    (h : (T.comp U).Equiv (T'.comp U')) :
    CompEquiv C (Algebra.seq c d) (Algebra.seq c' d') :=
  (Realizes.seq S hc hd).equiv S (Realizes.seq S hc' hd') h

/-- **Map fusion**: `map f` plugged into `map g` is `map (g ∘ f)`. -/
theorem seq_map_map {α β γ : Type} {f : α → β} {g : β → γ} {c d e : Comp M}
    (hc : Realizes S c (Tr.map f)) (hd : Realizes S d (Tr.map g))
    (he : Realizes S e (Tr.map (g ∘ f))) : CompEquiv C (Algebra.seq c d) e :=
  seq_fuse S hc hd he (Tr.map_map f g)

/-- **Filter fusion**: `filter p` plugged into `filter q` is `filter (p ∧ q)`. -/
theorem seq_filter_filter {α : Type} {p q : α → Bool} {c d e : Comp M}
    (hc : Realizes S c (Tr.filter p)) (hd : Realizes S d (Tr.filter q))
    (he : Realizes S e (Tr.filter fun x => p x && q x)) : CompEquiv C (Algebra.seq c d) e :=
  seq_fuse S hc hd he (Tr.filter_filter p q)

/-- **Filter after map** commutes to map after a filter on the original items. -/
theorem seq_map_filter {α β : Type} {f : α → β} {p : β → Bool} {c d c' d' : Comp M}
    (hc : Realizes S c (Tr.map f)) (hd : Realizes S d (Tr.filter p))
    (hc' : Realizes S c' (Tr.filter (p ∘ f))) (hd' : Realizes S d' (Tr.map f)) :
    CompEquiv C (Algebra.seq c d) (Algebra.seq c' d') :=
  seq_commute S hc hd hc' hd' (Tr.map_filter f p)

/-- **Take after map** commutes to map after take. -/
theorem seq_map_take {α β : Type} {f : α → β} {n : Nat} {c d c' d' : Comp M}
    (hc : Realizes S c (Tr.map f)) (hd : Realizes S d (Tr.take (α := β) n))
    (hc' : Realizes S c' (Tr.take (α := α) n)) (hd' : Realizes S d' (Tr.map f)) :
    CompEquiv C (Algebra.seq c d) (Algebra.seq c' d') :=
  seq_commute S hc hd hc' hd' (Tr.map_take f n)

/-- **`wac plug` of two stream components realises the composite transformer**, when the
socket imports the plug's exports by name and in order. -/
theorem plug_realizes {σ τ α β γ : Type} (P : Nat → Comp M) {T : Tr σ α β} {U : Tr τ β γ}
    (h₀ : Realizes S (P 0) T) (h₁ : Realizes S (P 1) U)
    (hnames : names (P 1).imports = names (exportIface (P 0)))
    (hn₀ : (names (P 0).imports).Nodup) (hne : (names (exportIface (P 0))).Nodup)
    (hn₁ : (names (exportIface (P 1))).Nodup) :
    Realizes S (select (List.range (P 1).exports.length)
      ((plugGraph fun k => sigOf (P k)).toComp P)) (T.comp U) :=
  (Realizes.seq S h₀ h₁).of_equiv S (plug_equiv_seq_of_names C P hnames hn₀ hne hn₁).symm

end Realizes

/-- The degenerate semantics on an empty interface: every transformer traps. It shows only
that the conditions of `StreamSem` are consistent. -/
def StreamSem.trivial (C : CoreSem M) : StreamSem C where
  width := 0
  den _ := Strategy.ofHandler (maskH 0)
  den_comp _ _ := by rw [← Strategy.ofHandler_comp, maskH_comp_maskH]
  den_congr _ := rfl
  den_id := rfl

end Silmaril.Wasm.Component.Algebra
