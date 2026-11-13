module

public import Silmaril.Proofs.Wasm.Det.CompRef.Basic
public import Silmaril.Wasm.Det.CompIR.Thms
public import Silmaril.Wasm.Component.Reference.Sound.Thms

/-!
# Determinism of simple components over the reference machine

For a simple component (`Silmaril.Wasm.Component.Reference.Simple`), the IR component
`c.toComp` has one core instance, so its strategy is deterministic and strict when the module's
semantics `modSem P` is (`den_detMod_single`, `modSem_det`). Soundness of the IR with respect to
the reference machine (`Simple.sound`) maps every returned reference outcome of an export call
to a play of the IR strategy; two such plays after the same question have the same answer, so
the reference outcomes coincide (`simple_returns_eq`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.CompRef

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Det.Game
  Silmaril.Wasm.Det.CompIR Silmaril.Wasm.Det.CompRef
open Silmaril.Wasm.Numerics (Profile)

/-- The IR strategy of a simple component is deterministic and strict. -/
theorem simple_detMod {P : Profile} (c : Simple) (hD : ModDet P c.mod) :
    DetMod (noneTraps _) (c.toComp.den (modSem P)) ∧
      Strict (noneTraps _) (noneTraps _) (c.toComp.den (modSem P)) :=
  den_detMod_single (modSem P) (modSem_det hD) _ _ _

/-- The IR strategy of a simple component is stateless and strict. -/
theorem simple_statelessMod {P : Profile} (c : Simple) (hD : ModStateless P c.mod) :
    StatelessMod (noneTraps _) (c.toComp.den (modSem P)) ∧
      Strict (noneTraps _) (noneTraps _) (c.toComp.den (modSem P)) :=
  den_statelessMod_single (modSem P) (modSem_stateless hD) _ _ _

/-- **Returned reference outcomes of an export call of a deterministic simple component
coincide.** -/
theorem simple_returns_eq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple)
    (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) (hD : ModDet P c.mod)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {rs₁ rs₂ : List Silmaril.Wasm.Component.Value.Val}
    (h₁ : Outcome.returns (some rs₁) ∈ exportBehaviours prof (refHost P) () c.toRef []
      c.exports[j].name (vs.map toRefVal))
    (h₂ : Outcome.returns (some rs₂) ∈ exportBehaviours prof (refHost P) () c.toRef []
      c.exports[j].name (vs.map toRefVal)) : rs₁ = rs₂ := by
  obtain ⟨ws₁, rfl, hp₁⟩ := Simple.sound P prof c hc hf hi ha j vs hvs _ h₁
  obtain ⟨ws₂, rfl, hp₂⟩ := Simple.sound P prof c hc hf hi ha j vs hvs _ h₂
  let a : Move (sigN 0) (sigN c.toComp.exports.length) :=
    .inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs))
  have hfree : TrapFree (noneTraps _) [a] := by
    intro m hm
    rw [List.mem_singleton] at hm
    subst hm
    exact id
  rcases (simple_detMod c hD).1 [a] _ _ hp₁ hp₂ trivial trivial hfree with h | h | h
  · cases h
    rfl
  · cases h
  · cases h

/-! ## Sequences of calls -/

section SeqLength

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

theorem seqCalls_length {prof : ProfileKind} {h : Host E σ} {m m' : Machine.Config E σ} {k : Nat}
    {cs : List (FuncId × List Value.Val)} {rss : List (List Value.Val)}
    (hs : SeqCalls prof h m k cs rss m') : rss.length = cs.length := by
  induction hs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨y, -, ys', hys, rfl⟩ := h
    simp [mapM_length hys]

/-- The results of a returning sequence have one entry per call. -/
theorem seqBehaviours_length {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {c : Syntax.Component E.Module} {calls : List (String × List Value.Val)} {name : String}
    {vals rs : List Value.Val} {p : List (List Value.Val) × Outcome}
    (hp : p ∈ seqBehaviours prof h σ0 c calls name vals) (hr : p.2 = .returns (some rs)) :
    p.1.length = calls.length := by
  rcases hp with ⟨_, _, _, fs, _, _, -, hfs, hseq, -, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [seqCalls_length hseq, List.length_zip, mapM_length hfs, List.length_map, Nat.min_self]
  · cases hr
  · cases hr

end SeqLength

theorem seqMoves_snoc (c : Simple) (j : Fin c.exports.length) (vs ws : List Silmaril.Wasm.Component.Val) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)), wss.length = calls.length →
      seqMoves c (calls ++ [(j, vs)]) (wss ++ [ws]) = seqMoves c calls wss ++
        [.inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)),
          .inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) (some (.vals ws)))]
  | [], [], _ => rfl
  | (_, _) :: calls, _ :: wss, hl => by
    simp only [List.cons_append, seqMoves]
    rw [seqMoves_snoc c j vs ws calls wss (by simpa using hl)]
  | [], _ :: _, hl => by cases hl
  | _ :: _, [], hl => by cases hl

theorem seqMoves_idle (c : Simple) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)), Path .idle (seqMoves c calls wss) .idle
  | (_, _) :: calls, _ :: wss => .cons (.ask _) (.cons (.ret _ _) (seqMoves_idle c calls wss))
  | [], _ => .nil _
  | _ :: _, [] => .nil _

/-- The IR play of a returning sequence of reference calls: the earlier calls end idle, then
the question of the last call and its answer. -/
theorem seq_play (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (ht : TypedCalls c calls) (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome}
    {rs : List Silmaril.Wasm.Component.Value.Val}
    (h : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal))
    (hr : p.2 = .returns (some rs)) :
    ∃ wss ws, rs = ws.map toRefVal ∧ seqMoves c calls wss ∈ c.toComp.den (modSem P) ∧
      seqMoves c calls wss ++ [.inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs))] ++
        [.inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) (some (.vals ws)))] ∈
          c.toComp.den (modSem P) := by
  have hl := seqBehaviours_length h hr
  obtain ⟨wss, hw, hm, ho⟩ := Simple.sound_seq P prof c hc hf hi ha calls j vs ht hvs p h
  rw [hr] at ho
  obtain ⟨ws, rfl, hp⟩ := ho
  have e : wss.length = calls.length := by
    rw [hw, List.length_map, List.length_map] at hl
    exact hl
  rw [seqMoves_snoc c j vs ws calls wss e] at hp
  have hsplit : ∀ (X : List (Move (sigN 0) (sigN c.toComp.exports.length))) (y z : Move (sigN 0)
      (sigN c.toComp.exports.length)), X ++ [y, z] = X ++ [y] ++ [z] := fun X y z => by simp
  rw [hsplit] at hp
  exact ⟨wss, ws, rfl, hm, hp⟩

/-- **Returned reference outcomes of an export call of a stateless simple component do not
depend on the earlier calls.** -/
theorem simple_seq_returns_eq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (hD : ModStateless P c.mod)
    (calls₁ calls₂ : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (ht₁ : TypedCalls c calls₁) (ht₂ : TypedCalls c calls₂)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {p₁ p₂ : List (List Silmaril.Wasm.Component.Value.Val) × Outcome}
    {rs₁ rs₂ : List Silmaril.Wasm.Component.Value.Val}
    (h₁ : p₁ ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls₁.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal))
    (h₂ : p₂ ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls₂.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal))
    (hr₁ : p₁.2 = .returns (some rs₁)) (hr₂ : p₂.2 = .returns (some rs₂)) : rs₁ = rs₂ := by
  obtain ⟨wss₁, ws₁, rfl, hm₁, hp₁⟩ := seq_play P prof c hc hf hi ha calls₁ ht₁ j vs hvs h₁ hr₁
  obtain ⟨wss₂, ws₂, rfl, hm₂, hp₂⟩ := seq_play P prof c hc hf hi ha calls₂ ht₂ j vs hvs h₂ hr₂
  have hfree : TrapFree (noneTraps _)
      [(.inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)) :
        Move (sigN 0) (sigN c.toComp.exports.length))] := fun m hm => by
    rw [List.mem_singleton] at hm
    subst hm
    exact id
  rcases (simple_statelessMod c hD).1 _ _ hm₁ hm₂ (seqMoves_idle c _ _) (seqMoves_idle c _ _)
      _ _ _ hp₁ hp₂ trivial trivial hfree with h | h | h
  · cases h
    rfl
  · cases h
  · cases h

end Silmaril.Proofs.Wasm.Det.CompRef
