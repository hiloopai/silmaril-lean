module

public import Silmaril.Proofs.Wasm.Spec.Attest.Shape
public import Silmaril.Wasm.Logic.GameLink.Thms
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# The gate calls `attest` only after both of its exports were called

Every profile, every run (no determinism), through the every-run program logic of
`Silmaril.Wasm.Logic` and its game link `GameLink.strategy_sound`:

* `hwp_gate_trap`: from a store where the other flag is `0`, every run of a gate function
  sets its own flag and traps (`HWP`, every-run partial correctness);
* `gateSat k`: with export `k` forbidden to the environment (`forbid k`) and the import never
  allowed (`noCall`), the gate meets its specification with the store invariant "flag `k` is
  `0`" (`flagZero k`): the other export only sets its own flag and traps;
* `gate_noCall`: hence (`strategy_sound`) a play of the gate in which export `k` is never asked
  never asks the import;
* **`gate_safe`**: a play of the gate that calls `attest` asks both `attestL` and `attestR`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Spec.Attest

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify Silmaril.Wasm.Spec.Attest
  Silmaril.Wasm.Spec.Attest.Core Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
open Silmaril.Wasm.Logic.Strategy (ISpec agStrat AG MoveGood resultOutcome)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-! ### The body, every run -/

/-- **Every run of a gate function whose other flag is `0` sets its flag and traps.** -/
theorem hwp_gate_trap {host : HostSemantics Nat} {s : Store Nat} {F : Frame} {m o : Fin (2 ^ 32)}
    {am ao : Nat} {gm go : GlobalInst} {Q : Post Nat} (hset : s.global? F ⟨m⟩ = some (am, gm))
    (hget : (s.setGlobal am (.i32 1)).global? F ⟨o⟩ = some (ao, go)) (hv : go.value = .i32 0)
    (hQ : Q (s.setGlobal am (.i32 1)) F .trap) :
    HWP P host s F (expression (gateBody m o)) Q := by
  show HWP P host s F (vals ([] ++ [.i32 1]) ++ .plain (.globalSet ⟨m⟩) ::
    [.plain (.globalGet ⟨o⟩), .plain (.if_ .empty [.call ⟨0⟩] []), .plain .unreachable]) Q
  refine Wp.globalSet (m := .part) hset ?_
  refine Wp.globalGet (m := .part) (us := []) hget ?_
  show HWP P host (s.setGlobal am (.i32 1)) F (vals ([] ++ [go.value]) ++
    .plain (.if_ .empty [.call ⟨0⟩] []) :: [.plain .unreachable]) Q
  rw [hv]
  refine HWP.if_ (fun h => absurd rfl h) (fun _ => ?_)
  refine HWP.block (us := []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
  refine HWP.of_vals (vs := []) ?_
  show HWP P host (s.setGlobal am (.i32 1)) F (vals ([] ++ []) ++ [.plain .unreachable]) Q
  exact Wp.unreachable (m := .part) (us := []) hQ

/-! ### The specification -/

/-- The import is never allowed. -/
def noCall : ISpec Att := ⟨fun _ => False, fun _ _ => True⟩

/-- Export `k` is not called by the environment. -/
def forbid (k : Fin 2) : ISpec gateI.F := ⟨fun e => e.1 ≠ k, fun _ _ => True⟩

/-- The store invariant: the functions are the gate's, and flag `k` is `0`. -/
def flagZero (k : Nat) (s : Store Nat) : Prop :=
  s.funcs = gS.funcs ∧ s.globals.length = 2 ∧ ∃ g, s.globals[k]? = some g ∧ g.value = .i32 0

/-- Setting another flag keeps the invariant. -/
theorem flagZero_set {k b : Nat} {s : Store Nat} (hk : k ≠ b) (h : flagZero k s) (v : Val) :
    flagZero k (s.setGlobal b v) := by
  obtain ⟨hf, hl, g, hg, hv⟩ := h
  refine ⟨hf, by simpa [Store.setGlobal] using hl, g, ?_, hv⟩
  simpa [Store.setGlobal, List.getElem?_modify, Ne.symm hk] using hg

/-- The arguments of a call of a gate export are empty. -/
theorem gate_args {j : Fin gateI.exports.length} {args : List Val}
    (ht : List.Forall₂ ScalarType.HasVal (gateI.exports.get j).params args) : args = [] := by
  have hp : (gateI.exports.get j).params = [] := by
    rcases j with ⟨_ | _ | j, hj⟩
    · rfl
    · rfl
    · exact absurd hj (by simp [gateI])
  rw [hp] at ht
  exact List.forall₂_nil_left_iff.1 ht

theorem list01 (i : Fin 2) : ([0, 1] : List Nat)[i.val]? = some i.val := by
  rcases i with ⟨_ | _ | _, h⟩ <;> first | rfl | omega

/-- Reading a flag of the gate's frame. -/
theorem global?_flag {s : Store Nat} {mi : ModuleInst} {x : Fin (2 ^ 32)} {i : Fin 2}
    {g : GlobalInst} (hglob : mi.globals = [0, 1]) (hx : x.val = i.val)
    (hg : s.globals[i.val]? = some g) :
    s.global? (Frame.forCall mi [] []) ⟨x⟩ = some (i.val, g) := by
  have h01 : (Frame.forCall mi [] []).module.globals[(⟨x⟩ : GlobalIdx).toNat]? = some i.val := by
    show mi.globals[x.val]? = _
    rw [hglob, hx]
    exact list01 i
  unfold Store.global?
  simp [h01, hg]

/-- A gate function, from the invariant on the flag it reads: a full specification proof. -/
theorem fspec_gate {k b : Fin 2} {mine other : Fin (2 ^ 32)} {fi : FuncInst Nat} {t : TypeIdx}
    (hkb : k ≠ b) (hfi : gS.funcs[gateI.addr b]? = some fi)
    (hc : fi.code = .wasm ⟨t, [], gateBody mine other⟩) (he : Expand fi.type voidTy)
    (hm : mine.val = b.val) (ho : other.val = k.val) (hglob : fi.module.globals = [0, 1]) :
    FSpecValid P (gameHost gateI noCall) (gateI.addr b)
      (exportSpec gateI (flagZero k) (forbid k) b)
  | 0 => fun _ _ _ _ _ _ _ => trivial
  | n + 1 => by
    refine FSpecAt.of_body (fun s _ h => h.1.1 ▸ hfi) hc he
      (fun _ _ ⟨_, ht, _⟩ => by rw [gate_args ht]; rfl) ?_
    rintro s args ⟨hinv, ht, -⟩ f vs₀
    obtain rfl := gate_args ht
    obtain ⟨hfun, hlen, g, hg, hv⟩ := hinv
    have hgm : s.globals[b.val]? = some (s.globals[b.val]'(by rw [hlen]; exact b.2)) :=
      List.getElem?_eq_getElem _
    have hset := global?_flag (s := s) (x := mine) hglob hm hgm
    have hinv' : flagZero k (s.setGlobal b.val (.i32 1)) :=
      flagZero_set (Fin.val_ne_of_ne hkb) ⟨hfun, hlen, g, hg, hv⟩ _
    obtain ⟨-, -, g', hg', hv'⟩ := hinv'
    have hget := global?_flag (s := s.setGlobal b.val (.i32 1)) (x := other) hglob ho hg'
    have hpost : (exportSpec gateI (flagZero k) (forbid k) b).post s [] (s.setGlobal b.val (.i32 1))
        .trap := ⟨flagZero_set (Fin.val_ne_of_ne hkb) ⟨hfun, hlen, g, hg, hv⟩ _, fun _ _ _ => trivial⟩
    exact hwp_gate_trap (P := P) hset hget hv' (show callPost f vs₀ _ _ f .trap from
      ⟨rfl, .inr (.inl ⟨rfl, hpost⟩)⟩) n

/-- A forbidden export: its specification holds vacuously. -/
theorem fspec_forbidden (k : Fin 2) :
    FSpecValid P (gameHost gateI noCall) (gateI.addr k) (exportSpec gateI (flagZero k) (forbid k) k) :=
  fun _ _ _ ⟨_, _, hne⟩ => absurd rfl hne

/-! ### The game link -/

theorem gS_globals_len : gS.globals.length = 2 := by
  obtain ⟨_, _, _, g₀, g₁, h⟩ := gateShape
  rw [h.globals]
  rfl

/-- The instantiated gate has both flags `0`. -/
theorem flagZero_init (k : Fin 2) : flagZero k.val gS := by
  obtain ⟨_, _, _, g₀, g₁, h⟩ := gateShape
  refine ⟨rfl, gS_globals_len, ?_⟩
  rcases k with ⟨_ | _ | _, hk⟩
  · exact ⟨g₀, by rw [h.globals]; rfl, h.val₀⟩
  · exact ⟨g₁, by rw [h.globals]; rfl, h.val₁⟩
  · omega

/-- **The gate meets its specification** with export `k` forbidden and flag `k` zero. -/
theorem gateSat (k : Fin 2) : GameSat P gateI (flagZero k.val) noCall (forbid k) := by
  obtain ⟨fi₀, fi₁, fi₂, g₀, g₁, h⟩ := gateShape
  obtain ⟨t₁, hc₁⟩ := h.code₁
  obtain ⟨t₂, hc₂⟩ := h.code₂
  have hf₁ : gS.funcs[gateI.addr (gateOp 0).1]? = some fi₁ := by
    rw [gateI_addr0, h.funcs]; rfl
  have hf₂ : gS.funcs[gateI.addr (gateOp 1).1]? = some fi₂ := by
    rw [gateI_addr1, h.funcs]; rfl
  intro j
  rcases k with ⟨_ | _ | _, hk⟩ <;> rcases j with ⟨_ | _ | _, hj⟩
  · exact fspec_forbidden _
  · exact fspec_gate (k := 0) (b := 1) (mine := 1) (other := 0) (by decide) hf₂ hc₂ h.ty₂ rfl rfl
      h.glob₂
  · exact absurd hj (by simp [gateI])
  · exact fspec_gate (k := 1) (b := 0) (mine := 0) (other := 1) (by decide) hf₁ hc₁ h.ty₁ rfl rfl
      h.glob₁
  · exact fspec_forbidden _
  · exact absurd hj (by simp [gateI])
  · omega
  · omega
  · omega

/-- Under an assume/guarantee strategy, if every Opponent move is allowed then so is every
Proponent move. -/
theorem ag_good {E F : Sig.{0}} {I : ISpec E} {S : ISpec F} :
    ∀ {p : List (Move E F)}, AG I S p → (∀ m ∈ p, Move.IsO m → MoveGood I S m) →
      ∀ m ∈ p, Move.IsP m → MoveGood I S m
  | [], _, _, _, hm, _ => absurd hm List.not_mem_nil
  | o :: p, ⟨hO, hP⟩, hgood, m, hm, hmP => by
    have hrest : ∀ m ∈ p, Move.IsO m → MoveGood I S m := fun m hm => hgood m (List.mem_cons_of_mem _ hm)
    rcases o with (_ | _) | (_ | _)
    · obtain ⟨hg, hag⟩ := hP trivial
      rcases List.mem_cons.1 hm with rfl | hm'
      · exact hg
      · exact ag_good hag hrest m hm' hmP
    · have hag := hO trivial (hgood _ (List.mem_cons_self ..) trivial)
      rcases List.mem_cons.1 hm with rfl | hm'
      · exact hmP.elim
      · exact ag_good hag hrest m hm' hmP
    · have hag := hO trivial (hgood _ (List.mem_cons_self ..) trivial)
      rcases List.mem_cons.1 hm with rfl | hm'
      · exact hmP.elim
      · exact ag_good hag hrest m hm' hmP
    · obtain ⟨hg, hag⟩ := hP trivial
      rcases List.mem_cons.1 hm with rfl | hm'
      · exact hg
      · exact ag_good hag hrest m hm' hmP

/-- **A play in which export `k` is never asked never asks `attest`.** -/
theorem gate_noCall (k : Fin 2) {p : List (Move Att GateSig)} (hp : p ∈ gateI.strategy P gS)
    (hk : ∀ e, (.inr (.ask e) : Move Att GateSig) ∈ p → e.1 ≠ k) (m : Att.Op) :
    (.inl (.ask m) : Move Att GateSig) ∉ p := by
  have hle := strategy_sound (gateSat (P := P) k) (flagZero_init k)
  obtain ⟨-, hag⟩ := hle hp
  intro hm
  have hO : ∀ o ∈ p, Move.IsO o → MoveGood noCall (forbid k) o := by
    intro o ho hIs
    rcases o with (_ | ⟨e, v⟩) | (e | _)
    · exact hIs.elim
    · trivial
    · exact hk e ho
    · exact hIs.elim
  exact ag_good hag hO _ hm trivial

/-- A gate question with index `k` is `gateOp k`. -/
theorem gateOp_eq {e : GateSig.Op} {k : Fin 2} (h : e.1 = k) : e = gateOp k := by
  obtain ⟨i, vs, hvs⟩ := e
  cases h
  have hp : ([unitFn, unitFn].get i).params = [] := by rw [get_unitFn 0 i]; rfl
  rw [hp] at hvs
  cases hvs
  rfl

/-- The question of `attest`. -/
def attOp : Att.Op := ⟨0, ⟨[], .nil⟩⟩

/-- **Gate safety**: a play of the gate that calls `attest` asks `attestL` and `attestR`. -/
theorem gate_safe (P : Profile) : ∀ s ∈ gateI.strategy P gateI.store,
    (∃ m : Att.Op, (.inl (.ask m) : Move Att GateSig) ∈ s) →
      (∃ a, (.inr (.ask (ιL.op a)) : Move Att GateSig) ∈ s) ∧
        (∃ a, (.inr (.ask (ιR.op a)) : Move Att GateSig) ∈ s) := by
  rintro s hs ⟨m, hm⟩
  constructor
  · by_contra hno
    refine gate_noCall (P := P) 0 hs (fun e he h0 => hno ⟨attOp, ?_⟩) m hm
    have hge : e = gateOp 0 := gateOp_eq h0
    rw [hge] at he
    exact he
  · by_contra hno
    refine gate_noCall (P := P) 1 hs (fun e he h1 => hno ⟨attOp, ?_⟩) m hm
    have hge : e = gateOp 1 := gateOp_eq h1
    rw [hge] at he
    exact he

end Silmaril.Proofs.Wasm.Spec.Attest
