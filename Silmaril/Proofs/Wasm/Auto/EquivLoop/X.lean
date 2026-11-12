module

public import Silmaril.Proofs.Wasm.Auto.EquivLoop.Inv

/-!
# Loops with memory and globals

The invariant `XInv lt gt mem` (a typed context of the extended checker has this store and frame)
instantiates the loop congruence under an invariant:

* `bodyEquivI_of_segEquivX`: `SegEquivX lt [] gt mem` (decided by `checkX`) is a body equivalence
  under `XInv`;
* `XCtx.rebase`, `rebase_ok`: after a symbolic run `A` that keeps the types of the locals and
  globals, the concrete state `(storeOf A, frameOf A)` is again the store and frame of a typed
  context (inputs: the values of `A`'s slots; initial memory: the bytes of `A`'s memory term);
* `keepsBr0I_of_check`: a `do … while` body `c ++ [br_if l]` accepted by `brIfBodyOkX` keeps
  `XInv` at its back edges;
* **`loopEquivX`**: two `do … while` loops whose bodies are `checkX`-equivalent, with memory and
  globals, are equivalent in both readings.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EquivLoop

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EquivLoop
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv (NoFuncTop wp_exit_post wp_step_inv)
open Silmaril.Wasm.Auto.Equiv (Env)
open Silmaril.Wasm.Auto.Equiv

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem code_init' (c : XCtx H) (lt gt : List IntType) (a : List Instr) (rest : List Admin) :
    c.code lt [] gt [] a rest = expression a ++ rest := by
  simp [XCtx.code, XCtx.stackOf, initX]

/-- **`SegEquivX` is a body equivalence under `XInv`.** -/
theorem bodyEquivI_of_segEquivX {lt gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : SegEquivX lt [] gt mem a b) : BodyEquivI (XInv lt gt mem) a b := by
  rintro m P H host s f Q ⟨c, hc, rfl, rfl⟩
  have h₁ := h m P host c [] [] Q hc
  simpa only [code_init', List.append_nil] using h₁

/-! ## Rebasing a context on the state after a symbolic run -/

theorem denX_envOfSlots {ρ : Env} {B0 B' : ByteArray} {l : List (IntType × XT)} {n : Nat}
    {p : IntType × XT} (h : l[n]? = some p) :
    denX (envOfSlots ρ B0 l) B' (p.1, .var n) = denX ρ B0 p := by
  simp [denX, evX, envOfSlots, h]

theorem setGlobals_idem : ∀ (s : Store H) (ga : List Nat) (vs : List Val), ga.Nodup →
    setGlobals (setGlobals s ga vs) ga vs = setGlobals s ga vs
  | s, a :: as, v :: vs, hnd => by
    have ha : a ∉ as := (List.nodup_cons.mp hnd).1
    show setGlobals ((setGlobals (s.setGlobal a v) as vs).setGlobal a v) as vs =
      setGlobals (s.setGlobal a v) as vs
    rw [setGlobals_setGlobal_not_mem _ _ _ _ _ ha, setGlobal_setGlobal]
    exact setGlobals_idem _ as vs (List.nodup_cons.mp hnd).2
  | _, [], _, _ => rfl
  | _, _ :: _, [], _ => rfl

theorem setGlobals_setMem : ∀ (s : Store H) (ga : List Nat) (vs : List Val) (a : Nat)
    (mi : MemInst), setGlobals (s.setMem a mi) ga vs = (setGlobals s ga vs).setMem a mi
  | s, b :: bs, w :: ws, a, mi => by
    show setGlobals ((s.setMem a mi).setGlobal b w) bs ws = (setGlobals (s.setGlobal b w) bs ws).setMem a mi
    rw [← setGlobals_setMem]
    rfl
  | _, [], _, _, _ => rfl
  | _, _ :: _, [], _, _ => rfl

theorem map_denX_init_locals {ρ : Env} {B0 B' : ByteArray} {lt : List IntType} {L G : List (IntType × XT)}
    (hl : L.map Prod.fst = lt) :
    (lt.mapIdx fun i t => (t, XT.var i)).map (denX (envOfSlots ρ B0 (L ++ G)) B') = L.map (denX ρ B0) := by
  have hlen : L.length = lt.length := by simpa using congrArg List.length hl
  apply List.ext_getElem
  · simp [hlen]
  · intro i h₁ h₂
    have hi : i < L.length := by simpa using h₂
    have hp : (L ++ G)[i]? = some L[i] := by simp [List.getElem?_append_left hi, hi]
    have ht : lt[i]'(by simpa [hlen] using hi) = L[i].1 := by
      subst hl
      simp
    simp only [List.getElem_map, List.getElem_mapIdx]
    rw [ht]
    exact denX_envOfSlots hp

theorem map_denX_init_globs {ρ : Env} {B0 B' : ByteArray} {lt gt : List IntType}
    {L G : List (IntType × XT)} (hl : L.length = lt.length) (hg : G.map Prod.fst = gt) :
    (initX lt [] gt).globs.map (denX (envOfSlots ρ B0 (L ++ G)) B') = G.map (denX ρ B0) := by
  have hlen : G.length = gt.length := by simpa using congrArg List.length hg
  simp only [initX, List.length_nil, Nat.add_zero]
  apply List.ext_getElem
  · simp [hlen]
  · intro k h₁ h₂
    have hk : k < G.length := by simpa using h₂
    have hp : (L ++ G)[lt.length + k]? = some G[k] := by
      rw [← hl, List.getElem?_append_right (by omega)]
      simp [hk]
    have ht : gt[k]'(by simpa [hlen] using hk) = G[k].1 := by
      subst hg
      simp
    simp only [List.getElem_map, List.getElem_mapIdx]
    rw [ht]
    exact denX_envOfSlots hp

/-- **Rebasing**: the state after a symbolic run that keeps the types is a typed context. -/
theorem rebase_ok {lt gt : List IntType} {mem : Bool} {c : XCtx H} (hc : c.Ok lt [] gt mem)
    {A : XState} (hl : A.locals.map Prod.fst = lt) (hg : A.globs.map Prod.fst = gt) :
    (c.rebase mem A).Ok lt [] gt mem := by
  have hll : A.locals.length = lt.length := by simpa using congrArg List.length hl
  have hglobs : (initX lt [] gt).globs.map (denX (envOfSlots c.ρ c.mi.bytes (A.locals ++ A.globs))
      (evM c.ρ c.mi.bytes A.mem)) = A.globs.map (denX c.ρ c.mi.bytes) := map_denX_init_globs hll hg
  have hlocs : (initX lt [] gt).locals.map (fun p => some (denX (envOfSlots c.ρ c.mi.bytes
      (A.locals ++ A.globs)) (evM c.ρ c.mi.bytes A.mem) p)) =
      A.locals.map (fun p => some (denX c.ρ c.mi.bytes p)) := by
    have h₀ := congrArg (List.map some) (map_denX_init_locals (ρ := c.ρ) (B0 := c.mi.bytes)
      (B' := evM c.ρ c.mi.bytes A.mem) (G := A.globs) hl)
    simpa [initX, List.map_map, Function.comp_def] using h₀
  obtain ⟨-, -, hga, hnd, hadr, hm⟩ := hc
  refine ⟨?_, ?_, hga, hnd, ?_, ?_⟩
  · show (XCtx.rebase c mem A).storeOf mem (initX lt [] gt) = c.storeOf mem A
    simp only [XCtx.storeOf, XCtx.rebase, hglobs]
    cases mem
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact setGlobals_idem _ _ _ hnd
    · simp only [↓reduceIte]
      rw [setGlobals_setMem, setGlobals_idem _ _ _ hnd]
      simp [Store.setMem, initX, evM, List.set_set]
  · simp only [XCtx.frameOf, XCtx.rebase, hlocs]
  · intro k hk
    obtain ⟨h₁, h₂⟩ := hadr k hk
    refine ⟨h₁, ?_⟩
    show c.ga[k] < (c.storeOf mem A).globals.length
    unfold XCtx.storeOf
    cases mem <;> simp [globals_length_setGlobals, Store.setMem, h₂]
  · intro hmem
    subst hmem
    exact mem?_storeOf ⟨hnd, hadr, hm⟩ A rfl

/-! ## Back edges of `do … while` bodies -/

/-- `br_if` keeps the store and the frame. -/
theorem hwp_brIf_state {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32}
    {l : LabelIdx} {Q : Post H} (hw : HWP P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) Q) :
    HWP P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)])
      (fun s' F o => Q s' F o ∧ s' = s ∧ F = f) := by
  have e₂ : ∀ x : Admin, vals (us ++ [.i32 c]) ++ [x] = vals us ++ [constI32 c, x] := fun x => by
    simp only [vals, List.map_append, List.map_cons, List.map_nil, constI32, List.append_assoc,
      List.cons_append, List.nil_append]
  by_cases hc0 : c = 0
  · subst hc0
    have hst : Step P host ⟨s, f, vals (us ++ [.i32 0]) ++ [.plain (.brIf l)]⟩ ⟨s, f, vals us⟩ := by
      rw [e₂]
      simpa using Sim.Step.vals_left (Step.brIfFalse (P := P) (host := host) (s := s) (f := f) (l := l)) us
    have hq := wp_exit_post (m := .part) (wp_step_inv (m := .part) hw hst) (o := .normal us) rfl
    exact HWP.brIf (fun h => (h rfl).elim)
      (fun _ => by simpa using HWP.of_vals (Q := fun s' F o => Q s' F o ∧ s' = s ∧ F = f) ⟨hq, rfl, rfl⟩)
  · have hst : Step P host ⟨s, f, vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]⟩
        ⟨s, f, vals us ++ [.plain (.br l)]⟩ := by
      rw [e₂]
      simpa using Sim.Step.vals_left (Step.brIfTrue (P := P) (host := host) (s := s) (f := f) (l := l) hc0) us
    have hex : Exits (.br l.toNat us) (vals us ++ [.plain (.br l)]) := ⟨l, [], rfl, rfl⟩
    have hq := wp_exit_post (m := .part) (wp_step_inv (m := .part) hw hst) hex
    exact HWP.brIf (fun _ => HWP.of_exits hex ⟨hq, rfl, rfl⟩) (fun h => (hc0 h).elim)

/-- **`do … while` bodies keep `XInv` at their back edges.** -/
theorem keepsBr0I_of_check {lt gt : List IntType} {mem : Bool} {c : List Instr} (l : LabelIdx)
    (hok : brIfBodyOkX lt gt mem c = true) : KeepsBr0I (XInv lt gt mem) (c ++ [.brIf l]) := by
  cases hA : xsexec mem (initX lt [] gt) c with
  | none => simp [brIfBodyOkX, hA] at hok
  | some A =>
    show KeepsBr0I (XInv lt gt mem) (c ++ [.brIf l])
    have hok' : (A.locals.map Prod.fst = lt ∧ A.globs.map Prod.fst = gt) ∧
        (A.stack.map Prod.fst).head? = some .i32 := by
      simpa [brIfBodyOkX, hA] using hok
    obtain ⟨⟨hl, hg⟩, hs⟩ := hok'
    rintro P H host s f Q ⟨c₀, hc, rfl, rfl⟩ hw
    have e : expression (c ++ [.brIf l]) = c₀.code lt [] gt [] c [.plain (.brIf l)] := by
      rw [code_init']
      simp [expression]
    have hw' : XOut .part P host c₀ mem A [] [.plain (.brIf l)] Q :=
      (wp_init_iff (m := .part) hc hA [] [.plain (.brIf l)] Q).mp (e ▸ hw)
    rw [e]
    refine (wp_init_iff (m := .part) hc hA [] [.plain (.brIf l)] _).mpr ?_
    unfold XOut at hw' ⊢
    cases hT : firstFail c₀.ρ c₀.mi.bytes A.guards with
    | some T =>
      have hq : Q (c₀.storeOf mem T) (c₀.frameOf T) .trap := by rw [hT] at hw'; exact hw'
      exact ⟨hq, fun vs h => Outcome.noConfusion h⟩
    | none =>
      show Wp .part P host (c₀.storeOf mem A) (c₀.frameOf A)
        (vals ([] ++ (c₀.stackOf A).reverse) ++ [.plain (.brIf l)]) (InvBr0 (XInv lt gt mem) Q)
      have hw₀ : Wp .part P host (c₀.storeOf mem A) (c₀.frameOf A)
          (vals ([] ++ (c₀.stackOf A).reverse) ++ [.plain (.brIf l)]) Q := by
        rw [hT] at hw'
        exact hw'
      obtain ⟨p, st, hst⟩ : ∃ p st, A.stack = p :: st := by
        cases hx : A.stack with
        | nil => simp [hx] at hs
        | cons p st => exact ⟨p, st, rfl⟩
      have hp : p.1 = .i32 := by simpa [hst] using hs
      obtain ⟨t, e₀⟩ := p
      have ht : t = .i32 := hp
      subst ht
      have hstack : vals ([] ++ (c₀.stackOf A).reverse) ++ [Admin.plain (.brIf l)] =
          vals ((st.map (denX c₀.ρ c₀.mi.bytes)).reverse ++ [.i32 (evX c₀.ρ c₀.mi.bytes .i32 e₀)]) ++
            [.plain (.brIf l)] := by
        simp [XCtx.stackOf, hst, denX, Val.i32]
      have hw₁ : Wp .part P host (c₀.storeOf mem A) (c₀.frameOf A)
          (vals ((st.map (denX c₀.ρ c₀.mi.bytes)).reverse ++
            [.i32 (evX c₀.ρ c₀.mi.bytes .i32 e₀)]) ++ [.plain (.brIf l)]) Q := hstack ▸ hw₀
      rw [hstack]
      refine HWP.mono (fun s' F o ho => ⟨ho.1, fun vs _ => ?_⟩) (hwp_brIf_state hw₁)
      obtain ⟨-, rfl, rfl⟩ := ho
      exact ⟨c₀.rebase mem A, rebase_ok hc hl hg, rfl, rfl⟩

/-- **Loops with memory and globals**: two `do … while` loops whose straight-line bodies are
`checkX`-equivalent (memory `0` and the globals `gt` included) and whose first body passes
`brIfBodyOkX` are equivalent, in both readings, in every typed context. -/
theorem loopEquivX {lt gt : List IntType} {mem : Bool} {c d : List Instr} {bt : BlockType}
    (l : LabelIdx) (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : checkX lt [] gt mem c d = true) (hok : brIfBodyOkX lt gt mem c = true) :
    LoopEquivI (XInv lt gt mem) bt (c ++ [.brIf l]) (d ++ [.brIf l]) := by
  have hb : BodyEquivI (XInv lt gt mem) (c ++ [.brIf l]) (d ++ [.brIf l]) := by
    rintro m P H host s f Q ⟨c₀, hc, rfl, rfl⟩
    have h₁ := segEquivX_of_checkX h m P host c₀ [] [.plain (.brIf l)] Q hc
    rw [code_init', code_init'] at h₁
    simpa [expression] using h₁
  exact LoopEquivI.of_body hbt hb (keepsBr0I_of_check l hok)

end Silmaril.Proofs.Wasm.Auto.EquivLoop