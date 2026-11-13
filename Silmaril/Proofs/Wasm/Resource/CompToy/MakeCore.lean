module

public import Silmaril.Proofs.Wasm.Resource.CompToy.Core
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# The toy resource component: the core function `make` in the program logic

`make` (core function `2`) under the most general environment of an import context in which
`res.new` (core function `0`, the canon built-in `resource.new`) is called on the counter's old
value `c` and answers some index in a set `J`, keeping the core store:

* `toyBind`: `resource.new` stands for address `0`, `resource.drop` for `1`;
* `newSpec c J`, `Γnew c J`: that import specification and context;
* `makeSpec c J`: from the toy's core store with counter `c`, `make` traps, or returns some
  `i32 j` with `J j` in the core store with counter `c + 1`;
* **`makeSpec_valid`** (`c < 2^32`): `make` meets `makeSpec c J` under `specHost toyBind (Γnew
  c J)` (body: `global.get`, `i32.eq`, `if … unreachable`, increment, `global.set`, and the
  stub rule `Open.FSpecAt.stub` for the call).

The import specification is not assumed of the machine: the core phase relates each machine
callout to it (`Silmaril.Proofs.Wasm.Resource.CompToy.Core.CalloutsAns`), discharged from the
built-in's dispatch program in `Silmaril.Proofs.Wasm.Resource.CompToy.Make`. New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Open
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable (P : Silmaril.Wasm.Numerics.Profile)

/-! ## The import context -/

/-- The canon built-in `resource.new` of the toy, as core host code. -/
abbrev newH : CanonHost (E3 P) := .builtin (.resourceNew ⟨0⟩ .i32) ⟨0⟩

/-- The canon built-in `resource.drop` of the toy, as core host code. -/
abbrev dropH : CanonHost (E3 P) := .builtin (.resourceDrop ⟨0⟩) ⟨0⟩

open Classical in
/-- The import binding: `resource.new` stands for core address `0`, `resource.drop` for `1`,
any other host code for address `5` (which no context specifies). -/
def toyBind (h : CanonHost (E3 P)) : ℕ := if h = newH P then 0 else if h = dropH P then 1 else 5

theorem toyBind_new : toyBind P (newH P) = 0 := by simp [toyBind]

theorem toyBind_drop : toyBind P (dropH P) = 1 := by
  have h : dropH P ≠ newH P := by simp
  simp [toyBind, h]

/-- `resource.new` called on `i32 c`, answering `i32 j` for some `j` with `J j` and keeping the
core store. -/
def newSpec (c : ℕ) (J : ℕ → Prop) : FSpec (CanonHost (E3 P)) where
  pre _ args := args = [.i32 (BitVec.ofNat 32 c)]
  post s _ s' o := s' = s ∧ ∃ j, J j ∧ o = .normal [.i32 (BitVec.ofNat 32 j)]

/-- The import context of `make`: only `resource.new` (address `0`). -/
def Γnew (c : ℕ) (J : ℕ → Prop) : Ctx (CanonHost (E3 P)) :=
  fun a => if a = 0 then some (newSpec P c J) else none

/-- The host relation of `make`'s core phase. -/
abbrev Hnew (c : ℕ) (J : ℕ → Prop) : HostSemantics (CanonHost (E3 P)) :=
  specHost (toyBind P) (Γnew P c J)

/-- **The specification of `make`** (core function `2`): from the core store with counter `c`
and no arguments, it traps, or returns `i32 j` for some `j` with `J j` in the core store with
counter `c + 1`. -/
def makeSpec (c : ℕ) (J : ℕ → Prop) : FSpec (CanonHost (E3 P)) where
  pre s args := s = toyCs P c ∧ args = []
  post _ _ s' o := o = .trap ∨
    (c + 1 < 2 ^ 32 ∧ s' = toyCs P (c + 1) ∧ ∃ j, J j ∧ o = .normal [.i32 (BitVec.ofNat 32 j)])

/-! ## Facts about the toy's core store (kernel evaluation) -/

theorem toyCore_make_code : ((toyInst P).store.core.funcs[2]?).map FuncInst.code =
    some (.wasm ⟨⟨2⟩, [], makeBody⟩) := by kernel_rfl

theorem toyCore_make_type : ((toyInst P).store.core.funcs[2]?).map
    (fun fi => decide (Expand fi.type
      (Silmaril.Wasm.Game.FnType.toComp ⟨[], [.num (.int .i32)]⟩))) = some true := by kernel_rfl

theorem toyCore_make_module : ((toyInst P).store.core.funcs[2]?).map
    (fun fi => (fi.module.funcs[0]?, fi.module.globals[0]?)) = some (some 0, some 0) := by
  kernel_rfl

theorem toyCore_new_code : ((toyInst P).store.core.funcs[0]?).map FuncInst.code =
    some (.host (newH P)) := by kernel_rfl

theorem toyCore_new_type : ((toyInst P).store.core.funcs[0]?).map
    (fun fi => decide (Expand fi.type
      (Silmaril.Wasm.Game.FnType.toComp ⟨[.num (.int .i32)], [.num (.int .i32)]⟩))) = some true := by
  kernel_rfl

theorem toyCore_globals : ((toyInst P).store.core.globals[0]?).map (fun g => g.value) =
    some (.i32 0) := by kernel_rfl

variable {P}

/-- The counter global of the toy's core store. -/
theorem toyCs_global (c : ℕ) : ∃ g : GlobalInst, (toyCs P c).globals[0]? = some g ∧
    g.value = .i32 (BitVec.ofNat 32 c) := by
  have h := toyCore_globals P
  cases hg : (toyInst P).store.core.globals[0]? with
  | none => simp [hg] at h
  | some g =>
    refine ⟨{ g with value := .i32 (BitVec.ofNat 32 c) }, ?_, rfl⟩
    show (List.modify (toyInst P).store.core.globals 0 _)[0]? = _
    rw [List.getElem?_modify]
    simp [hg]

/-- Setting the counter global of the toy's core store with counter `c` to `c + 1`. -/
theorem toyCs_setGlobal (c : ℕ) :
    (toyCs P c).setGlobal 0 (.i32 (BitVec.ofNat 32 c + 1)) = toyCs P (c + 1) := by
  unfold Store.setGlobal toyCs setCtr
  dsimp only
  rw [List.modify_modify_eq]
  congr 3
  funext g
  simp [BitVec.ofNat_add]

/-! ## The body -/

section Body

variable {H : Type} {host : HostSemantics H} {s : Store H} {F : Frame} {Q : Post H}
  {rest : List Admin}

theorem hwp_block_trap' (hq : Q s F .trap) :
    HWP P host s F (vals [] ++ .plain (.block .empty [.unreachable]) :: rest) Q :=
  HWP.block (us := []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl
    (Wp.unreachable (m := .part) (us := []) (rest := []) hq)

theorem hwp_block_empty' (h : HWP P host s F rest Q) :
    HWP P host s F (vals [] ++ .plain (.block .empty []) :: rest) Q :=
  HWP.block (us := []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl (HWP.of_vals (vs := []) h)

theorem ofNat_eq_allOnes {c : ℕ} (hc : c < 2 ^ 32) (h : BitVec.ofNat 32 c = -1) : c = 2 ^ 32 - 1 := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc] at h'
  rw [h']
  rfl

/-- The increment and the call after the test. -/
theorem make_incr {g : GlobalInst} {c : ℕ} (hgl : s.global? F ⟨0⟩ = some (0, g))
    (hv : g.value = .i32 (BitVec.ofNat 32 c))
    (hcall : HWP P host (s.setGlobal 0 (.i32 (BitVec.ofNat 32 c + 1))) F
      (vals [.i32 (BitVec.ofNat 32 c)] ++ [.plain (.call ⟨0⟩)]) Q) :
    HWP P host s F (vals [] ++ .plain (.globalGet ⟨0⟩) :: .plain (.globalGet ⟨0⟩) ::
      .plain (.intConst .i32 1) :: .plain (.intBinOp .i32 .add) :: .plain (.globalSet ⟨0⟩) ::
      [.plain (.call ⟨0⟩)]) Q := by
  have hset : HWP P host s F (vals ([.i32 (BitVec.ofNat 32 c)] ++ [.i32 (BitVec.ofNat 32 c + 1)]) ++
      .plain (.globalSet ⟨0⟩) :: [.plain (.call ⟨0⟩)]) Q :=
    Wp.globalSet (m := .part) (us := [.i32 (BitVec.ofNat 32 c)]) hgl hcall
  have hadd : HWP P host s F (vals ([.i32 (BitVec.ofNat 32 c)] ++
      [.num ⟨.int .i32, BitVec.ofNat 32 c⟩, .num ⟨.int .i32, 1⟩]) ++
      .plain (.intBinOp .i32 .add) :: .plain (.globalSet ⟨0⟩) :: [.plain (.call ⟨0⟩)]) Q :=
    HWP.intBinOp (fun z hz => by cases hz; exact hset) (fun e he => by cases he)
  have h₂ : HWP P host s F (vals ([.i32 (BitVec.ofNat 32 c)] ++ [g.value]) ++
      .plain (.intConst .i32 1) :: .plain (.intBinOp .i32 .add) :: .plain (.globalSet ⟨0⟩) ::
      [.plain (.call ⟨0⟩)]) Q := by
    rw [hv]
    exact hadd
  have h₁ : HWP P host s F (vals ([] ++ [g.value]) ++ .plain (.globalGet ⟨0⟩) ::
      .plain (.intConst .i32 1) :: .plain (.intBinOp .i32 .add) :: .plain (.globalSet ⟨0⟩) ::
      [.plain (.call ⟨0⟩)]) Q := by
    rw [hv]
    exact Wp.globalGet (m := .part) (us := [.i32 (BitVec.ofNat 32 c)]) hgl (hv ▸ h₂)
  exact Wp.globalGet (m := .part) (us := []) hgl h₁

/-- **The body of `make`**: it traps, or increments the counter and calls `res.new` on the old
value. -/
theorem make_body {g : GlobalInst} {c : ℕ} (hgl : s.global? F ⟨0⟩ = some (0, g))
    (hv : g.value = .i32 (BitVec.ofNat 32 c)) (hc : c < 2 ^ 32) (htrap : Q s F .trap)
    (hcall : c ≠ 2 ^ 32 - 1 → HWP P host (s.setGlobal 0 (.i32 (BitVec.ofNat 32 c + 1))) F
      (vals [.i32 (BitVec.ofNat 32 c)] ++ [.plain (.call ⟨0⟩)]) Q) :
    HWP P host s F (expression makeBody) Q := by
  have hif : HWP P host s F (vals ([] ++ [.i32 (Silmaril.Wasm.Numerics.intRelOp .i32 .eq
      (BitVec.ofNat 32 c) (-1))]) ++ .plain (.if_ .empty [.unreachable] []) ::
      .plain (.globalGet ⟨0⟩) :: .plain (.globalGet ⟨0⟩) :: .plain (.intConst .i32 1) ::
      .plain (.intBinOp .i32 .add) :: .plain (.globalSet ⟨0⟩) :: [.plain (.call ⟨0⟩)]) Q := by
    refine HWP.if_ (us := []) (fun _ => hwp_block_trap' htrap) (fun h0 => ?_)
    have hne : c ≠ 2 ^ 32 - 1 := by
      intro he
      subst he
      exact absurd h0 (by decide)
    exact hwp_block_empty' (make_incr hgl hv (hcall hne))
  have hrel : HWP P host s F (vals ([] ++ [.num ⟨.int .i32, BitVec.ofNat 32 c⟩,
      .num ⟨.int .i32, -1⟩]) ++ .plain (.intRelOp .i32 .eq) ::
      .plain (.if_ .empty [.unreachable] []) ::
      .plain (.globalGet ⟨0⟩) :: .plain (.globalGet ⟨0⟩) :: .plain (.intConst .i32 1) ::
      .plain (.intBinOp .i32 .add) :: .plain (.globalSet ⟨0⟩) :: [.plain (.call ⟨0⟩)]) Q :=
    Wp.intRelOp (m := .part) hif
  have hget : HWP P host s F (vals ([] ++ [g.value]) ++ .plain (.intConst .i32 (-1)) ::
      .plain (.intRelOp .i32 .eq) :: .plain (.if_ .empty [.unreachable] []) ::
      .plain (.globalGet ⟨0⟩) :: .plain (.globalGet ⟨0⟩) :: .plain (.intConst .i32 1) ::
      .plain (.intBinOp .i32 .add) :: .plain (.globalSet ⟨0⟩) :: [.plain (.call ⟨0⟩)]) Q := by
    rw [hv]
    exact hrel
  exact Wp.globalGet (m := .part) (us := []) hgl hget

end Body

/-! ## `make` meets its specification -/

/-- The call of `res.new` at the end of `make`. -/
theorem make_call {c : ℕ} {J : ℕ → Prop} {F f : Frame} {fi₀ : FuncInst (CanonHost (E3 P))}
    {vs₀ : List Execution.Core.Val} {k nr : ℕ} (hnr : nr = 1) (hc : c + 1 < 2 ^ 32)
    (hx : F.module.funcs[0]? = some 0) (hf₀ : (toyInst P).store.core.funcs[0]? = some fi₀)
    (hcode : fi₀.code = .host (newH P))
    (he : Expand fi₀.type (Silmaril.Wasm.Game.FnType.toComp ⟨[.num (.int .i32)], [.num (.int .i32)]⟩)) :
    HWP P (Hnew P c J) (toyCs P (c + 1)) F (vals [.i32 (BitVec.ofNat 32 c)] ++ [.plain (.call ⟨0⟩)])
      (bodyPostK P (Hnew P c J) nr f vs₀
        (callPost f vs₀ ((makeSpec P c J).post (toyCs P c) [])) k)
  | 0 => trivial
  | n + 1 => by
    have hS : Γnew P c J (toyBind P (newH P)) = some (newSpec P c J) := by
      rw [toyBind_new]
      rfl
    have hpre : (stubSpec 0 (newH P) (newSpec P c J)).pre (toyCs P (c + 1))
        [.i32 (BitVec.ofNat 32 c)] :=
      ⟨⟨fi₀, _, _, hf₀, hcode, he, rfl⟩, rfl⟩
    refine Safe.callIdx (vs₀ := []) hx hf₀ (FSpecAt.stub hS n) hpre fun s' o hc => ?_
    rcases hc with ⟨-, ⟨res, rfl, hs', j, hj, hres⟩ | ⟨rfl, -, j, -, he'⟩ | ⟨a, rfl, -, j, -, he'⟩⟩
    · cases hres
      subst hs'
      exact Safe.of_exits (o := .normal [.i32 (BitVec.ofNat 32 j)]) rfl
        ⟨by simp [hnr], rfl, .inl ⟨_, rfl, .inr ⟨hc, rfl, j, hj, rfl⟩⟩⟩
    · cases he'
    · cases he'

/-- **`make` meets its specification** under the import context of `resource.new`, for a
counter `c < 2^32`. -/
theorem makeSpec_valid {c : ℕ} (hc : c < 2 ^ 32) (J : ℕ → Prop) :
    FSpecValid P (Hnew P c J) 2 (makeSpec P c J)
  | 0 => fun _ _ _ _ _ _ _ => trivial
  | n + 1 => by
    have hcode := toyCore_make_code P
    have ht := toyCore_make_type P
    have hmod := toyCore_make_module P
    have hc₀ := toyCore_new_code P
    have ht₀ := toyCore_new_type P
    cases hf : (toyInst P).store.core.funcs[2]? with
    | none => simp [hf] at hcode
    | some fi =>
    cases hf₀ : (toyInst P).store.core.funcs[0]? with
    | none => simp [hf₀] at hc₀
    | some fi₀ =>
      simp only [hf, hf₀, Option.map_some, Option.some.injEq, decide_eq_true_eq,
        Prod.mk.injEq] at hcode ht hmod hc₀ ht₀
      refine FSpecAt.of_body (fi := fi) (fun s args h => by rw [h.1]; exact hf) hcode ht
        (fun s args h => by rw [h.2]; rfl) ?_
      rintro s args ⟨rfl, rfl⟩ f vs₀
      obtain ⟨g, hg, hv⟩ := toyCs_global (P := P) c
      have hgl : (toyCs P c).global? (Frame.forCall fi.module [] []) ⟨0⟩ = some (0, g) := by
        simp [Store.global?, Frame.forCall, hmod.2, hg, Idx.toNat]
      refine make_body hgl hv hc ⟨rfl, .inr (.inl ⟨rfl, .inl rfl⟩)⟩ (fun hne => ?_) n
      rw [toyCs_setGlobal]
      exact make_call (F := Frame.forCall fi.module [] []) (by rfl) (by omega) hmod.1 hf₀ hc₀ ht₀

end Silmaril.Wasm.Resource.CompToy
