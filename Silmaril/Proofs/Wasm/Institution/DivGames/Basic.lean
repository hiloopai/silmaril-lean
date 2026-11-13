module

public import Silmaril.Wasm.Institution.DivGames.Defs
public import Silmaril.Wasm.Institution.Games.Thms
public import Silmaril.Games.Inst.Thms
public import Silmaril.Games.DivLTS.Thms

@[expose] public section

/-!
# Wasm observations of divergence- and instantiation-observing games: proofs

* `div_wasmRed_iff`: the strategy of `wasmRed P host w` may diverge right
  after the invocation of `x` on `vs` iff `.diverges` is a Core behaviour of
  that invocation.
* `behOf_wasmRed`: with `mem_wasmRed_iff` for finite behaviours, all
  single-invocation behaviours are read off the strategy.
* `instReady_wasmInst`, `instFails_wasmInst`, `instDiverges_wasmInst`: the
  instantiation outcomes of `wasmInst` are those of silmaril's instantiation
  run; `instObs_wasmInst`: they are `moduleObs` on the empty script.
-/

namespace Silmaril.Wasm.Institution.DivGames

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Games Silmaril.Wasm.Institution.Games

variable {H : Type} (P : Profile) (host : HostSemantics H)

/-! ## Single invocations -/

theorem wasmRed_inf_some {w : Inst H} {q} {d : Config H} :
    Silmaril.InfiniteTrace (@Silmaril.Games.Reduction.step _ _ (wasmRed P host w) q) (some d) ↔
      Diverges P host d := by
  constructor
  · intro h
    refine Silmaril.InfiniteTrace.of_map some (fun _ => True) ?_ trivial h
    rintro a b - ⟨e, e', he, rfl, hs⟩
    cases he
    exact ⟨e', hs, trivial, rfl⟩
  · exact Silmaril.InfiniteTrace.map some (fun a b h => ⟨a, b, rfl, rfl, h⟩)

theorem wasmRed_inf_none {w : Inst H} {q} :
    ¬ Silmaril.InfiniteTrace (@Silmaril.Games.Reduction.step _ _ (wasmRed P host w) q) none := by
  intro h
  obtain ⟨b, ⟨e, e', he, -⟩, -⟩ := h.unfold
  cases he

theorem div_wasmRed_iff (w : Inst H) (x : String) (vs : List Val) :
    [.inr (.ask ⟨(x, vs), trivial⟩)] ∈ (DStrategy.ofReduction (wasmRed P host w)).div ↔
      .diverges ∈ (instEntry P host).beh w x vs := by
  refine DStrategy.div_ask_ofReduction_iff.trans ?_
  change Silmaril.InfiniteTrace _ ((Binaryen.exportFunc? w.2 x).map fun a => invoke w.1 a vs) ↔ _
  constructor
  · intro h
    cases ha : Binaryen.exportFunc? w.2 x with
    | none => rw [ha] at h; exact (wasmRed_inf_none P host h).elim
    | some a => rw [ha] at h; exact ⟨a, ha, .inr ⟨rfl, (wasmRed_inf_some P host).1 h⟩⟩
  · rintro ⟨a, ha, hmem⟩
    rw [ha]
    rcases hmem with ⟨c', r, -, -, hr⟩ | ⟨-, hd⟩
    · cases r <;> cases hr
    · exact (wasmRed_inf_some P host).2 hd

theorem behOf_wasmRed (w : Inst H) (x : String) (vs : List Val) :
    behOf (DStrategy.ofReduction (wasmRed P host w)) ⟨(x, vs), trivial⟩ =
      (instEntry P host).beh w x vs := by
  ext b
  by_cases hb : b = .diverges
  · subst hb
    simp only [behOf, Set.mem_ofPred_eq, ne_eq, not_true_eq_false, false_and, true_and, false_or]
    exact div_wasmRed_iff P host w x vs
  · simp only [behOf, Set.mem_ofPred_eq, hb, ne_eq, not_false_eq_true, true_and, false_and,
      or_false]
    exact mem_wasmRed_iff P host w x vs hb

theorem behOf_mono {E : Silmaril.Games.Sig.{0}} {X : Set String} {δ δ' : DStrategy E (exportSig X)}
    (h : δ ≤ δ') (q : (exportSig X).Op) : behOf δ q ⊆ behOf δ' q := by
  rintro b (⟨hb, hm⟩ | ⟨hb, hd⟩)
  · exact .inl ⟨hb, h.1 hm⟩
  · exact .inr ⟨hb, h.2.1 hd⟩

/-! ## Instantiation -/

variable {s : Store H} {xas : List ExternAddr} {m : Module}

theorem rtg_none {x : (wasmInst P host s xas m).IConf}
    (h : Relation.ReflTransGen (wasmInst P host s xas m).istep none x) :
    x = none ∨ ∃ d d', Instantiate P host s m xas d ∧ Steps P host d d' ∧
      x = some (d', d.frame.module) := by
  induction h with
  | refl => exact .inl rfl
  | tail _ hst ih =>
    rcases ih with rfl | ⟨d, d', hi, hs, rfl⟩
    · rcases hst with ⟨-, d, hi, rfl⟩ | ⟨e, e', mi, he, -, -⟩
      · exact .inr ⟨d, d, hi, .refl, rfl⟩
      · cases he
    · rcases hst with ⟨he, -⟩ | ⟨e, e', mi, he, rfl, hst⟩
      · cases he
      · cases he
        exact .inr ⟨d, e', hi, hs.tail hst, rfl⟩

theorem rtg_of {d d' : Config H} (hi : Instantiate P host s m xas d) (hs : Steps P host d d') :
    Relation.ReflTransGen (wasmInst P host s xas m).istep none (some (d', d.frame.module)) := by
  refine Relation.ReflTransGen.head (b := some (d, d.frame.module)) (.inl ⟨rfl, d, hi, rfl⟩) ?_
  induction hs with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (.inr ⟨_, _, _, rfl, rfl, hst⟩)

theorem instReady_wasmInst :
    (DStrategy.ofInst (wasmInst P host s xas m)).InstReady ↔
      ∃ d d', Instantiate P host s m xas d ∧ Steps P host d d' ∧ d'.code = [] := by
  rw [DStrategy.ofInst_instReady_iff]
  constructor
  · rintro ⟨c, st, hc, d₁, mi, rfl, hcode, -⟩
    rcases rtg_none P host hc with h | ⟨d, d', hi, hs, h⟩
    · cases h
    · cases h
      exact ⟨d, d₁, hi, hs, hcode⟩
  · rintro ⟨d, d', hi, hs, hcode⟩
    exact ⟨_, _, rtg_of P host hi hs, d', _, rfl, hcode, rfl⟩

theorem instFails_wasmInst {b : Behaviour Val} :
    (DStrategy.ofInst (wasmInst P host s xas m)).InstFails b ↔
      ∃ d d', ∃ r : Result, Instantiate P host s m xas d ∧ Steps P host d d' ∧
        d'.code = r.toAdmin ∧ r ≠ .values [] ∧ b = r.toBehaviour := by
  rw [DStrategy.ofInst_instFails_iff]
  constructor
  · rintro ⟨c, hc, d₁, mi, r, rfl, hcode, hr, rfl⟩
    rcases rtg_none P host hc with h | ⟨d, d', hi, hs, h⟩
    · cases h
    · cases h
      exact ⟨d, d₁, r, hi, hs, hcode, hr, rfl⟩
  · rintro ⟨d, d', r, hi, hs, hcode, hr, rfl⟩
    exact ⟨_, rtg_of P host hi hs, d', _, r, rfl, hcode, hr, rfl⟩

theorem inf_some {d : Config H} {mi : ModuleInst} :
    Silmaril.InfiniteTrace (wasmInst P host s xas m).istep (some (d, mi)) ↔ Diverges P host d := by
  constructor
  · intro h
    refine Silmaril.InfiniteTrace.of_map (fun d => (some (d, mi) : (wasmInst P host s xas m).IConf))
      (fun _ => True) ?_ trivial h
    rintro a b - (⟨he, -⟩ | ⟨e, e', mi', he, rfl, hs⟩)
    · cases he
    · cases he
      exact ⟨e', hs, trivial, rfl⟩
  · exact Silmaril.InfiniteTrace.map (fun d => (some (d, mi) : (wasmInst P host s xas m).IConf))
      (fun a b h => .inr ⟨a, b, mi, rfl, rfl, h⟩)

theorem instDiverges_wasmInst :
    (DStrategy.ofInst (wasmInst P host s xas m)).InstDiverges ↔
      ∃ d, Instantiate P host s m xas d ∧ Diverges P host d := by
  rw [DStrategy.ofInst_instDiverges_iff]
  constructor
  · intro h
    obtain ⟨b, hst, hinf⟩ := h.unfold
    rcases hst with ⟨-, d, hi, rfl⟩ | ⟨e, e', mi, he, -, -⟩
    · exact ⟨d, hi, (inf_some P host).1 hinf⟩
    · cases he
  · rintro ⟨d, hi, hd⟩
    exact Silmaril.InfiniteTrace.fold (b := some (d, d.frame.module)) (.inl ⟨rfl, d, hi, rfl⟩)
      ((inf_some P host).2 hd)

theorem session_nil {mi : ModuleInst} {st : Store H} {bs : List (Behaviour Val)}
    (h : Binaryen.Session P host mi st [] bs) : bs = [] := by
  cases h
  rfl

/-- **Instantiation observations.** The instantiation outcomes read off the
strategy of `wasmInst` are silmaril's module observations of the empty
script. -/
theorem instObs_wasmInst :
    instObs (DStrategy.ofInst (wasmInst P host s xas m)) = Binaryen.moduleObs P host s xas m [] := by
  ext bs
  simp only [instObs, Set.mem_ofPred_eq, instReady_wasmInst, instFails_wasmInst,
    instDiverges_wasmInst, Binaryen.moduleObs]
  constructor
  · rintro (⟨rfl, d, d', hi, hs, hcode⟩ | ⟨b, rfl, d, d', r, hi, hs, hcode, hr, rfl⟩ |
      ⟨rfl, d, hi, hd⟩)
    · exact ⟨d, hi, .inl ⟨d', [], hs, hcode, .nil, rfl⟩⟩
    · exact ⟨d, hi, .inr (.inl ⟨d', r, hs, hcode, hr, rfl⟩)⟩
    · exact ⟨d, hi, .inr (.inr ⟨hd, rfl⟩)⟩
  · rintro ⟨d, hi, ⟨d', bs', hs, hcode, hses, rfl⟩ | ⟨d', r, hs, hcode, hr, rfl⟩ | ⟨hd, rfl⟩⟩
    · rw [session_nil P host hses]
      exact .inl ⟨rfl, d, d', hi, hs, hcode⟩
    · exact .inr (.inl ⟨_, rfl, d, d', r, hi, hs, hcode, hr, rfl⟩)
    · exact .inr (.inr ⟨rfl, d, hi, hd⟩)

end Silmaril.Wasm.Institution.DivGames
