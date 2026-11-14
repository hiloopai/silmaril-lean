module

public import Silmaril.Proofs.Wasm.Logic.Iris.Base
public import Silmaril.Proofs.Wasm.Logic.Iris.Head
public import Silmaril.Proofs.Wasm.Logic.Iris.Cells

/-!
# The Iris logic of Wasm Core 3.0: locals and globals

`wp_localGet`, `wp_localSet` (through the frame cell) and `wp_globalGet`,
`wp_globalSet` (through the frame cell, for the module instance, and the cell of
the global).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head)
open _root_.Iris _root_.Iris.BI _root_.Iris.Std _root_.Iris.ProgramLogic

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Owned cells as separating conjunctions -/

section Own

variable {GF : BundledGFunctors} [WasmGS GF]

theorem ownCells_one (l : ILoc) (c : ICell) : ownCells (GF := GF) [(l, c)] = pts l c :=
  sep_emp.to_eq

theorem ownCells_two (l : ILoc) (c : ICell) (l' : ILoc) (c' : ICell) :
    ownCells (GF := GF) [(l, c), (l', c')] = iprop(pts l c ∗ pts l' c') := by
  simp only [ownCells, sep_emp.to_eq]

theorem ownCells_nil : ownCells (GF := GF) [] = iprop(emp) := rfl

theorem ownCells_cons (l : ILoc) (c : ICell) (ps : List (ILoc × ICell)) :
    ownCells (GF := GF) ((l, c) :: ps) = iprop(pts l c ∗ ownCells ps) := rfl

end Own

/-! ## Facts from owned cells -/

theorem frame_of_cells {s : Store H} {f f' : Frame} {ps : List (ILoc × ICell)}
    (h : Cells ((.frame, .frame f) :: ps) s f') : f' = f := by
  have h₁ : cellOf s f' .frame = some (.frame f) := h _ (List.mem_cons_self ..)
  simpa [cellOf] using h₁

theorem global_of_cells {s : Store H} {f f' : Frame} {a : Nat} {v : Val}
    (h : Cells [(.frame, .frame f), (.global a, .val v)] s f') :
    ∃ g, s.globals[a]? = some g ∧ g.value = v := by
  have h₁ : cellOf s f' (.global a) = some (.val v) := h (.global a, .val v) (by simp)
  rcases hg : s.globals[a]? with _ | g
  · simp [cellOf, hg] at h₁
  · exact ⟨g, rfl, by simpa [cellOf, hg] using h₁⟩

theorem global?_eq {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (hx : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g) :
    s.global? f x = some (a, g) := by
  simp [Store.global?, hx, hg]

/-! ## Locals -/

theorem localGet_progress {vs : List Val} {x : LocalIdx} {v : Val} {f : Frame}
    (hv : f.local? x = some (some v)) (s : Store H) (f' : Frame)
    (hc : Cells [(.frame, .frame f)] s f') :
    ∃ (vs' args : List Val) (c₀ : Config H), vs = vs' ++ args ∧
      Head P s f' args (.plain (.localGet x)) c₀ := by
  have hf : f' = f := frame_of_cells hc
  exact ⟨vs, [], _, by simp, .variable (.localGet (hf ▸ hv))⟩

theorem localGet_inv {vs : List Val} {x : LocalIdx} {v : Val} {f : Frame} {rest : List Admin}
    (hv : f.local? x = some (some v)) (s : Store H) (f' : Frame) (vs' args : List Val)
    (c₀ : Config H) (hc : Cells [(.frame, .frame f)] s f') (hW : vs = vs' ++ args)
    (hh : Head P s f' args (.plain (.localGet x)) c₀) :
    c₀.store = s ∧ c₀.frame = f' ∧ vals vs' ++ c₀.code ++ rest = vals (vs ++ [v]) ++ rest := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨rfl, v', hv', rfl⟩ := Hoare.head_localGet hh
  have hvv : v' = v := by rw [hf, hv] at hv'; simpa using hv'.symm
  subst hvv
  simp [hW, vals]

theorem localSet_progress {vs : List Val} {x : LocalIdx} {w : Val} {f : Frame}
    (hx : x.toNat < f.locals.length) (s : Store H) (f' : Frame)
    (hc : Cells [(.frame, .frame f)] s f') :
    ∃ (vs' args : List Val) (c₀ : Config H), vs ++ [w] = vs' ++ args ∧
      Head P s f' args (.plain (.localSet x)) c₀ := by
  have hf : f' = f := frame_of_cells hc
  exact ⟨vs, [w], _, rfl, .variable (.localSet (hf ▸ hx))⟩

theorem localSet_inv {vs : List Val} {x : LocalIdx} {w : Val} {f : Frame} {rest : List Admin}
    (s : Store H) (f' : Frame) (vs' args : List Val) (c₀ : Config H)
    (hc : Cells [(.frame, .frame f)] s f') (hW : vs ++ [w] = vs' ++ args)
    (hh : Head P s f' args (.plain (.localSet x)) c₀) :
    vals vs' ++ c₀.code ++ rest = vals vs ++ rest ∧
      Change s f' c₀.store c₀.frame [(.frame, .frame f)] [(.frame, .frame (f.setLocal x w))] [] := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨v, rfl, -, rfl⟩ := Hoare.head_localSet hh
  obtain ⟨rfl, rfl⟩ := Hoare.split_one hW
  subst hf
  refine ⟨by simp, rfl, by simp, by simp, ?_, ?_⟩
  · intro p hp
    simp only [List.append_nil, List.mem_singleton] at hp
    subst hp
    rfl
  · intro l c hl hlc
    have hne : l ≠ .frame := by simpa using hl
    rw [cellOf_frame_ne hne]
    exact hlc

theorem globalGet_progress {vs : List Val} {x : GlobalIdx} {a : Nat} {v : Val} {f : Frame}
    (hx : f.module.globals[x.toNat]? = some a) (s : Store H) (f' : Frame)
    (hc : Cells [(.frame, .frame f), (.global a, .val v)] s f') :
    ∃ (vs' args : List Val) (c₀ : Config H), vs = vs' ++ args ∧
      Head P s f' args (.plain (.globalGet x)) c₀ := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨g, hg, -⟩ := global_of_cells hc
  exact ⟨vs, [], _, by simp, .variable (.globalGet (global?_eq (hf ▸ hx) hg))⟩

theorem globalGet_inv {vs : List Val} {x : GlobalIdx} {a : Nat} {v : Val} {f : Frame}
    {rest : List Admin} (hx : f.module.globals[x.toNat]? = some a) (s : Store H) (f' : Frame)
    (vs' args : List Val) (c₀ : Config H)
    (hc : Cells [(.frame, .frame f), (.global a, .val v)] s f') (hW : vs = vs' ++ args)
    (hh : Head P s f' args (.plain (.globalGet x)) c₀) :
    c₀.store = s ∧ c₀.frame = f' ∧ vals vs' ++ c₀.code ++ rest = vals (vs ++ [v]) ++ rest := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨g, hg, hgv⟩ := global_of_cells hc
  obtain ⟨rfl, a', g', hg', rfl⟩ := head_globalGet hh
  have hgg : g' = g := by
    rw [hf, global?_eq hx hg] at hg'
    cases hg'
    rfl
  subst hgg hgv
  simp [hW, vals]

theorem globalSet_progress {vs : List Val} {x : GlobalIdx} {a : Nat} {v w : Val} {f : Frame}
    (hx : f.module.globals[x.toNat]? = some a) (s : Store H) (f' : Frame)
    (hc : Cells [(.frame, .frame f), (.global a, .val v)] s f') :
    ∃ (vs' args : List Val) (c₀ : Config H), vs ++ [w] = vs' ++ args ∧
      Head P s f' args (.plain (.globalSet x)) c₀ := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨g, hg, -⟩ := global_of_cells hc
  exact ⟨vs, [w], _, rfl, .variable (.globalSet (global?_eq (hf ▸ hx) hg))⟩

theorem globalSet_change {s : Store H} {f : Frame} {a : Nat} {v w : Val}
    (hlt : a < s.globals.length) :
    Change s f (s.setGlobal a w) f [(.frame, .frame f), (.global a, .val v)]
      [(.frame, .frame f), (.global a, .val w)] [] := by
  refine ⟨rfl, by simp, by simp, ?_, ?_⟩
  · intro p hp
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rfl
    · exact cellOf_setGlobal_self hlt
  · intro l c hl hlc
    have hne : l ≠ .global a := fun he => hl (by simp [he])
    rw [cellOf_setGlobal_ne hne]
    exact hlc

theorem globalSet_inv {vs : List Val} {x : GlobalIdx} {a : Nat} {v w : Val} {f : Frame}
    {rest : List Admin} (hx : f.module.globals[x.toNat]? = some a) (s : Store H) (f' : Frame)
    (vs' args : List Val) (c₀ : Config H)
    (hc : Cells [(.frame, .frame f), (.global a, .val v)] s f') (hW : vs ++ [w] = vs' ++ args)
    (hh : Head P s f' args (.plain (.globalSet x)) c₀) :
    vals vs' ++ c₀.code ++ rest = vals vs ++ rest ∧
      Change s f' c₀.store c₀.frame [(.frame, .frame f), (.global a, .val v)]
        [(.frame, .frame f), (.global a, .val w)] [] := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨g, hg, -⟩ := global_of_cells hc
  obtain ⟨v', a', g', hargs, hg', hc₀⟩ := head_globalSet hh
  have hvs : vs' = vs ∧ v' = w := Hoare.split_one (hargs ▸ hW)
  have haa : (a', g') = (a, g) := Option.some.inj (hg'.symm.trans (hf ▸ global?_eq hx hg))
  have hlt : a < s.globals.length := (List.getElem?_eq_some_iff.mp hg).1
  refine ⟨by rw [hc₀, hvs.1]; simp, ?_⟩
  rw [hc₀, (Prod.mk.inj haa).1, hvs.2, hf]
  exact globalSet_change hlt

section Rules

variable {GF : BundledGFunctors} [WasmGS GF]

local bi (IProp GF)

/-- **`local.get`.** -/
theorem wp_localGet {E : CoPset} {vs : List Val} {x : LocalIdx} {v : Val} {rest : List Admin}
    {f : Frame} {Φ : Res H → IProp GF} (hv : f.local? x = some (some v)) :
    ownFrame f ∗ ▷ (ownFrame f -∗ WP (IExpr.run (vals (vs ++ [v]) ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals vs ++ .plain (.localGet x) :: rest) : IExpr P host) @ E {{ Φ }} := by
  simpa only [ownCells_one] using
    wp_head_read (P := P) (host := host) (E := E) (Φ := Φ) [(.frame, .frame f)] ⟨rfl, by simp, rfl⟩
      (localGet_progress hv) (localGet_inv hv)

/-- **`local.set`.** -/
theorem wp_localSet {E : CoPset} {vs : List Val} {x : LocalIdx} {w : Val} {rest : List Admin}
    {f : Frame} {Φ : Res H → IProp GF} (hx : x.toNat < f.locals.length) :
    ownFrame f ∗ ▷ (ownFrame (f.setLocal x w) -∗
      WP (IExpr.run (vals vs ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (vs ++ [w]) ++ .plain (.localSet x) :: rest) : IExpr P host) @ E
      {{ Φ }} := by
  iintro ⟨Hf, H⟩
  iapply wp_head_change [(.frame, .frame f)] [(.frame, .frame (f.setLocal x w))] (fun _ => [])
    (fun _ => vals vs ++ rest) ⟨rfl, by simp, rfl⟩ (localSet_progress hx) localSet_inv
  simp only [ownCells_one, ownCells_nil]
  iframe Hf
  iintro !> %_ Hf -
  iapply H $$ Hf

/-- **`global.get`.** -/
theorem wp_globalGet {E : CoPset} {vs : List Val} {x : GlobalIdx} {a : Nat} {v : Val}
    {rest : List Admin} {f : Frame} {Φ : Res H → IProp GF}
    (hx : f.module.globals[x.toNat]? = some a) :
    ownFrame f ∗ ownGlobal a v ∗ ▷ (ownFrame f ∗ ownGlobal a v -∗
      WP (IExpr.run (vals (vs ++ [v]) ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals vs ++ .plain (.globalGet x) :: rest) : IExpr P host) @ E {{ Φ }} := by
  simpa only [ownCells_two, sep_assoc.to_eq] using
    wp_head_read (P := P) (host := host) (E := E) (Φ := Φ) [(.frame, .frame f), (.global a, .val v)]
      ⟨rfl, by simp, rfl⟩ (globalGet_progress hx) (globalGet_inv hx)

/-- **`global.set`.** -/
theorem wp_globalSet {E : CoPset} {vs : List Val} {x : GlobalIdx} {a : Nat} {v w : Val}
    {rest : List Admin} {f : Frame} {Φ : Res H → IProp GF}
    (hx : f.module.globals[x.toNat]? = some a) :
    ownFrame f ∗ ownGlobal a v ∗ ▷ (ownFrame f ∗ ownGlobal a w -∗
      WP (IExpr.run (vals vs ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (vs ++ [w]) ++ .plain (.globalSet x) :: rest) : IExpr P host) @ E
      {{ Φ }} := by
  iintro ⟨Hf, Hg, H⟩
  iapply wp_head_change [(.frame, .frame f), (.global a, .val v)]
    [(.frame, .frame f), (.global a, .val w)] (fun _ => []) (fun _ => vals vs ++ rest)
    ⟨rfl, by simp, rfl⟩ (globalSet_progress hx) (globalSet_inv hx)
  simp only [ownCells_two, ownCells_nil]
  iframe Hf Hg
  iintro !> %_ Hc -
  iapply H $$ Hc

end Rules

end Silmaril.Wasm.Logic.IrisWasm
