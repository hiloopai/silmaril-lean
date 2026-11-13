module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegNoFailList
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Setup

/-!
# Segment initialisation under global embeddings

`initSegmentsT?` reads the store only through tables, memories, element and data segments,
and (in offsets) globals and allocation: replacing the globals and functions of a store
(`repl G F`) while renaming the frame's global addresses, with the same global reads
(`HG`), maps its outcome exactly (`initSegmentsT?_repl`). Hence, for the residue configuration
of single allocation and the spec configuration related by the embedding of
`prepare_residue_emb`, the outcomes agree, and `residue_segments_not_fail`: for a validated
module, the direct initialisation that `instantiateOnce?` runs never fails.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- Map the stores of a segment result. -/
def segMap {α β : Type} (ga : α → β) (g : Store Nat → Store Nat) :
    SegResult Nat α → SegResult Nat β
  | .ok a => .ok (ga a)
  | .trap s => .trap (g s)
  | .fail => .fail

variable {ρ : Nat → Nat} (G : List GlobalInst) (F : List (FuncInst Nat))

/-- The global reads of `repl G F u` through the renamed frame are those of `u`. -/
def HG (ρ : Nat → Nat) (G : List GlobalInst) (F : List (FuncInst Nat)) (u : Store Nat)
    (f : Frame) : Prop :=
  ∀ x, ((repl G F u).global? (frame ρ f) x).map (·.2) = (u.global? f x).map (·.2)

theorem HG.of_globals {u u' : Store Nat} {f : Frame} (h : HG ρ G F u f)
    (hg : u'.globals = u.globals) : HG ρ G F u' f := by
  intro x
  have e₁ : (repl G F u').global? (frame ρ f) x = (repl G F u).global? (frame ρ f) x := rfl
  have e₂ : u'.global? f x = u.global? f x := by simp only [Store.global?, hg]
  rw [e₁, e₂]
  exact h x

theorem cfold_repl {f : Frame} (e : Expr) :
    ∀ (u : Store Nat) (vs : List Val), HG ρ G F u f →
      cfold (frame ρ f) (repl G F u) vs e = (cfold f u vs e).map (fun p => (repl G F p.1, p.2)) := by
  induction e with
  | nil => intro u vs _; rfl
  | cons i e ih =>
    intro u vs hu
    rw [cfold_cons, cfold_cons, constInstr?_repl G F hu]
    cases h : constInstr? u f vs i with
    | none => rfl
    | some p =>
      have hg : p.1.globals = u.globals := (constInstr?_shape (s' := p.1) (vs' := p.2) h).1
      simp only [Option.map_some, Option.bind_some]
      exact ih p.1 p.2 (hu.of_globals G F hg)

theorem evalConst?_repl {u : Store Nat} {f : Frame} {e : Expr} (hu : HG ρ G F u f) :
    evalConst? (repl G F u) (frame ρ f) e = (evalConst? u f e).map (fun p => (repl G F p.1, p.2)) := by
  have h : constExpr? (repl G F u) (frame ρ f) e =
      (constExpr? u f e).map (fun p => (repl G F p.1, p.2)) := cfold_repl G F (f := f) e u [] hu
  unfold evalConst?
  rw [h]
  cases constExpr? u f e with
  | none => rfl
  | some p =>
    obtain ⟨s', ws⟩ := p
    rcases ws with _ | ⟨v, _ | _⟩ <;> rfl

theorem pred_lt {nb : BitVec 32} {n : Nat} (hn : nb.toNat = n) (hnz : nb ≠ 0) :
    (nb - 1).toNat < n := by
  have h : nb.toNat ≠ 0 := fun h => hnz (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [bv_pred hnz]
  omega

theorem tableInitLoop_repl {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType} (n : Nat) :
    ∀ (u : Store Nat) (i : BitVec a.intType.width) (j nb : BitVec 32), nb.toNat = n →
      tableInitLoop (repl G F u) (frame ρ f) x y a i j nb =
        (tableInitLoop u f x y a i j nb).map (repl G F) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u i j nb hn
    have ht : (repl G F u).table? (frame ρ f) x = u.table? f x := rfl
    have he : (repl G F u).elem? (frame ρ f) y = u.elem? f y := rfl
    rw [tableInitLoop, tableInitLoop, ht, he]
    rcases u.table? f x with _ | ⟨ta, ti⟩ <;> rcases u.elem? f y with _ | ⟨ea, ei⟩
    all_goals try rfl
    by_cases hb : i.toNat + nb.toNat ≤ ti.refs.length ∧ j.toNat + nb.toNat ≤ ei.refs.length
    · simp only [hb, and_self, ite_true]
      by_cases hz : nb = 0
      · simp only [hz, dite_true, Option.map_some]
      · simp only [hz, dite_false]
        cases ei.refs[j.toNat]? with
        | none => rfl
        | some r =>
          exact ih _ (pred_lt hn hz) (u.setTable ta { ti with refs := ti.refs.set i.toNat r })
            (i + 1) (j + 1) (nb - 1) rfl
    · simp only [hb, ite_false, Option.map_none]

theorem memoryInitLoop_repl {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType} (n : Nat) :
    ∀ (u : Store Nat) (i : BitVec a.intType.width) (j nb : BitVec 32), nb.toNat = n →
      memoryInitLoop (repl G F u) (frame ρ f) x y a i j nb =
        (memoryInitLoop u f x y a i j nb).map (repl G F) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    show ∀ (u : Store Nat) (i : BitVec a.intType.width) (j nb : BitVec 32), nb.toNat = n →
      memoryInitLoop (repl G F u) (frame ρ f) x y a i j nb =
        (memoryInitLoop u f x y a i j nb).map (repl G F)
    intro u i j nb hn
    have hm : (repl G F u).mem? (frame ρ f) x = u.mem? f x := rfl
    have hd : (repl G F u).data? (frame ρ f) y = u.data? f y := rfl
    rw [memoryInitLoop, memoryInitLoop, hm, hd]
    rcases u.mem? f x with _ | ⟨ma, mi⟩ <;> rcases u.data? f y with _ | ⟨da, di⟩
    all_goals try rfl
    by_cases hb : i.toNat + nb.toNat ≤ mi.bytes.size ∧ j.toNat + nb.toNat ≤ di.bytes.size
    swap
    · simp only [hb, ite_false, Option.map_none]
    simp only [hb, and_self, ite_true]
    by_cases hz : nb = 0
    · simp only [hz, dite_true, Option.map_some]
    have ih' : ∀ (u' : Store Nat) (i' : BitVec a.intType.width) (j' : BitVec 32),
        memoryInitLoop (repl G F u') (frame ρ f) x y a i' j' (nb - 1) =
          (memoryInitLoop u' f x y a i' j' (nb - 1)).map (repl G F) :=
      fun u' i' j' => ih _ (pred_lt hn hz) u' i' j' (nb - 1) rfl
    simp only [hz, dite_false]
    rcases di.bytes.data[j.toNat]? with _ | byte
    · rfl
    dsimp only
    rcases Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr i.toNat memarg0)
      (count := PackSize.i8.width / 8) ((BitVec.ofNat 32 byte.toNat).setWidth _) with _ | b
    · rfl
    exact ih' (u.setMem ma { mi with bytes := b }) (i + 1) (j + 1)

/-! ## Globals are kept -/

theorem tableInitLoop_globals {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType} (n : Nat) :
    ∀ (u u' : Store Nat) (i : BitVec a.intType.width) (j nb : BitVec 32), nb.toNat = n →
      tableInitLoop u f x y a i j nb = some u' → u'.globals = u.globals := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u u' i j nb hn h
    rw [tableInitLoop] at h
    split at h
    · split at h
      · split at h
        · cases h; rfl
        · rename_i hz
          split at h
          · have hr := ih _ (pred_lt hn hz) _ _ _ _ _ rfl h
            exact hr
          · cases h
      · cases h
    · cases h

theorem memoryInitLoop_globals {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType} (n : Nat) :
    ∀ (u u' : Store Nat) (i : BitVec a.intType.width) (j nb : BitVec 32), nb.toNat = n →
      memoryInitLoop u f x y a i j nb = some u' → u'.globals = u.globals := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u u' i j nb hn h
    rw [memoryInitLoop] at h
    split at h
    · split at h
      · split at h
        · cases h; rfl
        · rename_i hz
          split at h
          · split at h
            · have hr := ih _ (pred_lt hn hz) _ _ _ _ _ rfl h
              exact hr
            · cases h
          · cases h
      · cases h
    · cases h

theorem elemSeg_globals {u u' : Store Nat} {f : Frame} {k : Nat} {e : Elem}
    (h : initElemSeg? evalConst? u f k e = some u') : u'.globals = u.globals := by
  unfold initElemSeg? at h
  split at h
  · cases h; rfl
  · simp only [elemDrop?, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    rfl
  · split at h
    · cases h
    · rename_i s₁ v hev
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i s₂ hl
          simp only [elemDrop?, Option.map_eq_some_iff] at h
          obtain ⟨_, -, rfl⟩ := h
          exact (tableInitLoop_globals _ _ _ _ _ _ rfl hl).trans (evalConst?_shape hev).1

theorem dataSeg_globals {u u' : Store Nat} {f : Frame} {k : Nat} {d : Data}
    (h : initDataSeg? evalConst? u f k d = some u') : u'.globals = u.globals := by
  unfold initDataSeg? at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · rename_i s₁ v hev
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i s₂ hl
          simp only [dataDrop?, Option.map_eq_some_iff] at h
          obtain ⟨_, -, rfl⟩ := h
          exact (memoryInitLoop_globals _ _ _ _ _ _ rfl hl).trans (evalConst?_shape hev).1

/-! ## Segments -/

theorem elemDrop?_repl {u : Store Nat} {f : Frame} {y : ElemIdx} :
    elemDrop? (repl G F u) (frame ρ f) y = (elemDrop? u f y).map (repl G F) := by
  have he : (repl G F u).elem? (frame ρ f) y = u.elem? f y := rfl
  simp only [elemDrop?, he]
  cases u.elem? f y <;> rfl

theorem dataDrop?_repl {u : Store Nat} {f : Frame} {y : DataIdx} :
    dataDrop? (repl G F u) (frame ρ f) y = (dataDrop? u f y).map (repl G F) := by
  have hd : (repl G F u).data? (frame ρ f) y = u.data? f y := rfl
  simp only [dataDrop?, hd]
  cases u.data? f y <;> rfl

theorem initElemSeg?_repl {u : Store Nat} {f : Frame} {k : Nat} {e : Elem} (hu : HG ρ G F u f) :
    initElemSeg? evalConst? (repl G F u) (frame ρ f) k e =
      (initElemSeg? evalConst? u f k e).map (repl G F) := by
  unfold initElemSeg?
  split
  · rfl
  · exact elemDrop?_repl G F
  rw [evalConst?_repl G F hu]
  rcases evalConst? u f _ with _ | ⟨s₁, v⟩
  · rfl
  simp only [Option.map_some]
  rcases v.addr? with _ | ⟨a, i⟩
  · rfl
  dsimp only
  rw [tableInitLoop_repl G F _ s₁ i 0 _ rfl]
  rcases tableInitLoop s₁ f _ _ a i 0 _ with _ | s₂
  · rfl
  exact elemDrop?_repl G F

theorem initDataSeg?_repl {u : Store Nat} {f : Frame} {k : Nat} {d : Data} (hu : HG ρ G F u f) :
    initDataSeg? evalConst? (repl G F u) (frame ρ f) k d =
      (initDataSeg? evalConst? u f k d).map (repl G F) := by
  unfold initDataSeg?
  split
  · rfl
  · rw [evalConst?_repl G F hu]
    cases evalConst? u f _ with
    | none => rfl
    | some p =>
      obtain ⟨s₁, v⟩ := p
      show (match v.addr? with | none => none | some ⟨a, i⟩ => _) =
        Option.map _ (match v.addr? with | none => none | some ⟨a, i⟩ => _)
      cases v.addr? with
      | none => rfl
      | some ai =>
        obtain ⟨a, i⟩ := ai
        dsimp only
        rw [memoryInitLoop_repl G F _ s₁ i 0 _ rfl]
        cases memoryInitLoop s₁ f _ _ a i 0 _ with
        | none => rfl
        | some s₂ => exact dataDrop?_repl G F

theorem elemSegTrap?_repl {u : Store Nat} {f : Frame} {k : Nat} {e : Elem} (hu : HG ρ G F u f) :
    elemSegTrap? evalConst? (repl G F u) (frame ρ f) k e =
      (elemSegTrap? evalConst? u f k e).map (repl G F) := by
  unfold elemSegTrap?
  split
  · rw [evalConst?_repl G F hu]
    cases evalConst? u f _ with
    | none => rfl
    | some p =>
      obtain ⟨s₁, v⟩ := p
      simp only [Option.map_some]
      cases v.addr? with
      | none => rfl
      | some ai =>
        obtain ⟨a, i⟩ := ai
        dsimp only
        split <;> split <;> first | rfl | (rename_i h₁ h₂; exact absurd h₁ h₂) |
          (rename_i h₁ h₂; exact absurd h₂ h₁)
  · rfl

theorem dataSegTrap?_repl {u : Store Nat} {f : Frame} {k : Nat} {d : Data} (hu : HG ρ G F u f) :
    dataSegTrap? evalConst? (repl G F u) (frame ρ f) k d =
      (dataSegTrap? evalConst? u f k d).map (repl G F) := by
  unfold dataSegTrap?
  split
  · rw [evalConst?_repl G F hu]
    cases evalConst? u f _ with
    | none => rfl
    | some p =>
      obtain ⟨s₁, v⟩ := p
      simp only [Option.map_some]
      cases v.addr? with
      | none => rfl
      | some ai =>
        obtain ⟨a, i⟩ := ai
        dsimp only
        split <;> split <;> first | rfl | (rename_i h₁ h₂; exact absurd h₁ h₂) |
          (rename_i h₁ h₂; exact absurd h₂ h₁)
  · rfl

theorem initElemSegT?_repl {u : Store Nat} {f : Frame} {k : Nat} {e : Elem} (hu : HG ρ G F u f) :
    initElemSegT? evalConst? (repl G F u) (frame ρ f) k e =
      segMap (repl G F) (repl G F) (initElemSegT? evalConst? u f k e) := by
  unfold initElemSegT?
  rw [initElemSeg?_repl G F hu, elemSegTrap?_repl G F hu]
  cases initElemSeg? evalConst? u f k e with
  | some s₁ => rfl
  | none => cases elemSegTrap? evalConst? u f k e <;> rfl

theorem initDataSegT?_repl {u : Store Nat} {f : Frame} {k : Nat} {d : Data} (hu : HG ρ G F u f) :
    initDataSegT? evalConst? (repl G F u) (frame ρ f) k d =
      segMap (repl G F) (repl G F) (initDataSegT? evalConst? u f k d) := by
  unfold initDataSegT?
  rw [initDataSeg?_repl G F hu, dataSegTrap?_repl G F hu]
  cases initDataSeg? evalConst? u f k d with
  | some s₁ => rfl
  | none => cases dataSegTrap? evalConst? u f k d <;> rfl

theorem initElemListT?_repl {f : Frame} : ∀ (l : List (Nat × Elem)) (u : Store Nat),
    HG ρ G F u f → initElemListT? evalConst? (repl G F u) (frame ρ f) l =
      segMap (repl G F) (repl G F) (initElemListT? evalConst? u f l)
  | [], _, _ => rfl
  | (k, e) :: l, u, hu => by
    rw [initElemListT?, initElemListT?, initElemSegT?_repl G F hu]
    cases h : initElemSegT? evalConst? u f k e with
    | ok s₁ =>
      have hg : s₁.globals = u.globals := elemSeg_globals (initElemSegT?_ok_iff.1 h)
      exact initElemListT?_repl l s₁ (hu.of_globals G F hg)
    | trap s₁ => rfl
    | fail => rfl

theorem initDataListT?_repl {f : Frame} : ∀ (l : List (Nat × Data)) (u : Store Nat),
    HG ρ G F u f → initDataListT? evalConst? (repl G F u) (frame ρ f) l =
      segMap (repl G F) (repl G F) (initDataListT? evalConst? u f l)
  | [], _, _ => rfl
  | (k, d) :: l, u, hu => by
    rw [initDataListT?, initDataListT?, initDataSegT?_repl G F hu]
    cases h : initDataSegT? evalConst? u f k d with
    | ok s₁ =>
      have hg : s₁.globals = u.globals := dataSeg_globals (initDataSegT?_ok_iff.1 h)
      exact initDataListT?_repl l s₁ (hu.of_globals G F hg)
    | trap s₁ => rfl
    | fail => rfl

theorem elemList_globals {f : Frame} : ∀ (l : List (Nat × Elem)) (u u' : Store Nat),
    initElemListT? evalConst? u f l = .ok u' → u'.globals = u.globals
  | [], _, _, h => by cases h; rfl
  | (k, e) :: l, u, u', h => by
    rw [initElemListT?] at h
    split at h
    · rename_i s₁ h₁
      exact (elemList_globals l s₁ u' h).trans (elemSeg_globals (initElemSegT?_ok_iff.1 h₁))
    · cases h
    · cases h

/-- **Segment initialisation commutes with replacing globals and functions.** -/
theorem initSegmentsT?_repl {u : Store Nat} {f : Frame} {m : Module} (hu : HG ρ G F u f) :
    initSegmentsT? evalConst? (repl G F u) (frame ρ f) m =
      segMap (fun p => (repl G F p.1, frame ρ p.2)) (repl G F)
        (initSegmentsT? evalConst? u f m) := by
  unfold initSegmentsT?
  rw [initElemListT?_repl G F _ u hu]
  cases h : initElemListT? evalConst? u f ((List.range m.elems.length).zip m.elems) with
  | ok s₁ =>
    have hg : s₁.globals = u.globals := elemList_globals _ u s₁ h
    simp only [segMap]
    rw [initDataListT?_repl G F _ s₁ (hu.of_globals G F hg)]
    cases initDataListT? evalConst? s₁ f ((List.range m.data.length).zip m.data) <;> rfl
  | trap s₁ => rfl
  | fail => rfl

/-! ## The residue configuration of single allocation -/

theorem xas_map_id (xas : List ExternAddr) : xas.map (external id) = xas := by
  have h : external id = (id : ExternAddr → ExternAddr) := funext fun x => by cases x <;> rfl
  rw [h, List.map_id]

theorem segMap_ne_fail {α β : Type} {ga : α → β} {g : Store Nat → Store Nat}
    {r : SegResult Nat α} (h : segMap ga g r ≠ .fail) : r ≠ .fail := by
  intro hr
  rw [hr] at h
  exact h rfl

/-- **The direct segment initialisation that single allocation runs never fails** for a
validated module instantiated into a host-free well-typed store against typed addresses: with
the residue preparation `hg`/`hp` of `instantiateOnce?`, `initSegmentsT?` succeeds or traps. -/
theorem residue_segments_not_fail {s : Store Nat} {m : Module} {xas : List ExternAddr}
    {xtI xtE : List CExternType} (hm : ModuleOk m ⟨xtI, xtE⟩) (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f) (hxas : List.Forall₂ (ExternAddrOk s) xas xtI)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st)) :
    initSegmentsT? evalConst? c₁.store c₁.frame m.globalResidue ≠ .fail := by
  obtain ⟨c, ι, hc, -, hframe, -, he, -, -⟩ :=
    prepare_residue_emb (Emb.refl s) Function.injective_id (modDom_of_storeOk hs hw)
      (imports_globals_lt hxas) hg hp
  have hc' : prepare? evalConst? s m xas = some (c, st) := by
    rw [← xas_map_id xas]
    exact hc
  have hspec : initSegmentsT? evalConst? c.store c.frame m ≠ .fail :=
    prepare_segments_not_fail hm hs hxas hc'
  have hu : HG ι c.store.globals c.store.funcs c₁.store c₁.frame := global?_repl he c₁.frame
  have heq : initSegmentsT? evalConst? c.store c.frame m =
      segMap (fun p => (repl c.store.globals c.store.funcs p.1, frame ι p.2))
        (repl c.store.globals c.store.funcs)
        (initSegmentsT? evalConst? c₁.store c₁.frame m.globalResidue) := by
    rw [hframe, ← repl_self he]
    exact initSegmentsT?_repl _ _ hu
  rw [heq] at hspec
  exact segMap_ne_fail hspec

end Silmaril.Proofs.Wasm.Game.SpecGlobals
