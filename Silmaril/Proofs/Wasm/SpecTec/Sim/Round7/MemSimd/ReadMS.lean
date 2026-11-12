module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.DispatchD
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadPackBwd

/-!
# Round 7, memory SIMD: the vector loads as obligations of the generic dispatch at `configVD`

`BackwardUpToD.read` asks, for every `Step_read` rule `i`, that a firing at the `configVD` image
of a configuration be the image of a Core step. This file discharges it for the ten memory SIMD
loads (`msReadRules`, rules 42–51), for every configuration. Pass 5 needed the store to hold no
memory SIMD code (`StoreMS`), because the per-rule leaves were stated at `stateV`; pass 6 states
them at `stateVF F s f` (any function list `F`, `StateF.lean`), of which `stateVD` is an instance,
so the hypothesis is gone (`readMSD`, `backward_upToD_restD`):

* `decode_vloadD`, `decode_vloadLaneD`: a vector load rule fires only at the image of
  `CONST at i; v128.load…` or `CONST at i; VCONST c; v128.loadN_lane …`. The left-hand side
  names the constructors; `adminToVD_case` and the head lemmas name the Core instructions, and
  `at : addrtype` makes the constant an address (`Round4Read.decode_aconst_typed`);
* `vload_kind`: rules 42–49 tell the four load shapes apart by their `vloadop` option, so rule
  `k` fires at `vecLoad op` only for `k = oobRule op` or `k = oobRule op + 1`;
* `readMSD`: **the ten obligations**, from round 7's backend leaves (`bwdB_vloadOob`,
  `bwdB_vloadFull`, `bwdB_vecLoadPack`, `bwdB_vecLoadSplat`, `bwdB_vecLoadZero`,
  `bwdB_vloadLaneOob`, `bwdB_vecLoadLane`) through `Round6.Reading.firesB_read_iff`;
* `backwardUpToD_of_restD`, `backward_upToD_restD`: **the generic dispatch at `configVD` with the
  memory SIMD loads plugged in**: from the remaining obligations `BackwardUpToDRest` and
  `typingFactsD_simEnv`, a declarative SpecTec step from the `configVD` image is a Core step.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H} {F : Value}

/-! ## Heads -/

theorem head_vecLoad {a : Admin} (h : Typing.adminHead a = "VLOAD") :
    ∃ op x arg, a = .plain (.vecLoad op x arg) := by
  revert h
  admin_head_inv

theorem head_vecLoadLane {a : Admin} (h : Typing.adminHead a = "VLOAD_LANE") :
    ∃ p x arg j, a = .plain (.vecLoadLane p x arg j) := by
  revert h
  admin_head_inv

theorem head_vconst {a : Admin} (h : Typing.adminHead a = "VCONST") :
    ∃ c, a = .plain (.vecConst c) := by
  revert h
  admin_head_inv

/-- A two-element image is the image of a two-element sequence. -/
theorem adminsToVD_eq_pair {is : List Admin} {v₁ v₂ : Value} (h : adminsToVD is = [v₁, v₂]) :
    ∃ a₁ a₂, is = [a₁, a₂] ∧ adminToVD a₁ = v₁ ∧ adminToVD a₂ = v₂ := by
  match is, h with
  | [a₁, a₂], h => exact ⟨a₁, a₂, rfl, (List.cons.inj h).1, (List.cons.inj (List.cons.inj h).2).1⟩
  | [], h => simp [adminsToVD] at h
  | [_], h => simp [adminsToVD] at h
  | _ :: _ :: _ :: _, h => simp [adminsToVD] at h

/-- A three-element image is the image of a three-element sequence. -/
theorem adminsToVD_eq_triple {is : List Admin} {v₁ v₂ v₃ : Value}
    (h : adminsToVD is = [v₁, v₂, v₃]) :
    ∃ a₁ a₂ a₃, is = [a₁, a₂, a₃] ∧ adminToVD a₁ = v₁ ∧ adminToVD a₂ = v₂ ∧
      adminToVD a₃ = v₃ := by
  match is, h with
  | [a₁, a₂, a₃], h =>
      simp only [adminsToVD, List.cons.injEq, and_true] at h
      exact ⟨a₁, a₂, a₃, rfl, h.1, h.2.1, h.2.2⟩
  | [], h => simp [adminsToVD] at h
  | [_], h => simp [adminsToVD] at h
  | [_, _], h => simp [adminsToVD] at h
  | _ :: _ :: _ :: _ :: _, h => simp [adminsToVD] at h

/-- An address constant at `adminToVD`, decoded from the typing of its type. -/
theorem decode_aconstD {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {a : Admin} {AT I : Value}
    (h : adminToVD a = .case "CONST" (.tuple [AT, I]))
    (hAT : HasTyp (simEnv B) ρ (.varT "addrtype" []) AT) :
    ∃ (t : AddrType) (b : BitVec t.intType.width), a = aconst t b := by
  have hV : adminToV a = .case "CONST" (.tuple [AT, I]) := by
    rcases Typing.head_const (adminToVD_case h).symm with ⟨t, b, rfl⟩ | ⟨t, b, rfl⟩
    · exact h
    · exact h
  obtain ⟨t, b, rfl, -, -⟩ := Round4Read.decode_aconst_typed hρ hV hAT
  exact ⟨t, b, rfl⟩

/-! ## The left-hand sides, decoded -/

/-- **A vector load rule fires only at the image of `CONST at i; v128.load…`.** -/
theorem decode_vloadD {B : Builtins} {k : Nat} {nm : IL.Id} {qs : List Param} {eo rh : Exp}
    {prems : List Prem} {Z : Value} {code : List Admin} {w : Value}
    (h : Equiv.Validation.HasRuleAt (simEnv B) "Step_read" "%~>%" k (.ruleD nm qs "%~>%"
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "CONST" (.tupE [.subE (.varE "at")
        (.varT "addrtype" []) (.varT "numtype" []), .varE "i"]), .caseE "VLOAD" (.tupE
        [.caseE "V128" (.tupE []), eo, .varE "x", .varE "ao"])]]), rh]) prems))
    (hat : Param.expP "at" (.varT "addrtype" []) ∈ qs)
    (hf : Fires (simEnv B) "Step_read" k (.tuple [cfgV Z (adminsToVD code), w])) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (op : VecLoadOp) (x : MemIdx) (arg : MemArg),
      code = [aconst a i, .plain (.vecLoad op x arg)] := by
  obtain ⟨σ, hq, he, -⟩ := State.Fires.rule_eq h hf
  obtain ⟨-, hc⟩ := RefsGC.cfgz_inv (RefsGC.lhs_of_concl he)
  obtain ⟨v₁, l₁, h₁, hl₁, hL⟩ := evalExps_cons_iff.1 (RefsGC.elems_of_list hc)
  obtain ⟨v₂, l₂, h₂, hl₂, rfl⟩ := evalExps_cons_iff.1 hl₁
  obtain rfl := evalExps_nil_iff.1 hl₂
  obtain ⟨a₁, a₂, rfl, ha₁, ha₂⟩ := adminsToVD_eq_pair hL
  obtain ⟨u₂, -, hv₂⟩ := evalExp_caseE_iff.1 h₂
  obtain ⟨op, x, arg, rfl⟩ := head_vecLoad (adminToVD_case (ha₂.trans hv₂)).symm
  obtain ⟨u₁, hu₁, hv₁⟩ := evalExp_caseE_iff.1 h₁
  obtain ⟨AT, I, rfl, hAT, -⟩ := Vec.inv_tup2 hu₁
  obtain ⟨AT', fat, hT⟩ := hq "at" _ hat
  have hA : AT' = AT :=
    Option.some.inj (fat.symm.trans (evalExp_varE_iff.1 (evalExp_subE_iff.1 hAT)))
  obtain ⟨t, b, rfl⟩ := decode_aconstD ⟨rfl, rfl, rfl⟩ (ha₁.trans hv₁) (hA ▸ hT)
  exact ⟨t, b, op, x, arg, rfl⟩

/-- **A vector lane load rule fires only at the image of `CONST at i; VCONST c;
v128.loadN_lane …`.** -/
theorem decode_vloadLaneD {B : Builtins} {k : Nat} {nm : IL.Id} {qs : List Param} {rh : Exp}
    {prems : List Prem} {Z : Value} {code : List Admin} {w : Value}
    (h : Equiv.Validation.HasRuleAt (simEnv B) "Step_read" "%~>%" k (.ruleD nm qs "%~>%"
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "CONST" (.tupE [.subE (.varE "at")
        (.varT "addrtype" []) (.varT "numtype" []), .varE "i"]), .caseE "VCONST" (.tupE
        [.caseE "V128" (.tupE []), .varE "c_1"]), .caseE "VLOAD_LANE" (.tupE [.caseE "V128"
        (.tupE []), .caseE "%" (.tupE [.varE "N"]), .varE "x", .varE "ao", .varE "j"])]]), rh])
      prems))
    (hat : Param.expP "at" (.varT "addrtype" []) ∈ qs)
    (hf : Fires (simEnv B) "Step_read" k (.tuple [cfgV Z (adminsToVD code), w])) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (c : BitVec 128) (p : PackSize) (x : MemIdx)
      (arg : MemArg) (j : LaneIdx),
      code = [aconst a i, .plain (.vecConst c), .plain (.vecLoadLane p x arg j)] := by
  obtain ⟨σ, hq, he, -⟩ := State.Fires.rule_eq h hf
  obtain ⟨-, hc⟩ := RefsGC.cfgz_inv (RefsGC.lhs_of_concl he)
  obtain ⟨v₁, l₁, h₁, hl₁, hL⟩ := evalExps_cons_iff.1 (RefsGC.elems_of_list hc)
  obtain ⟨v₂, l₂, h₂, hl₂, rfl⟩ := evalExps_cons_iff.1 hl₁
  obtain ⟨v₃, l₃, h₃, hl₃, rfl⟩ := evalExps_cons_iff.1 hl₂
  obtain rfl := evalExps_nil_iff.1 hl₃
  obtain ⟨a₁, a₂, a₃, rfl, ha₁, ha₂, ha₃⟩ := adminsToVD_eq_triple hL
  obtain ⟨u₃, -, hv₃⟩ := evalExp_caseE_iff.1 h₃
  obtain ⟨p, x, arg, j, rfl⟩ := head_vecLoadLane (adminToVD_case (ha₃.trans hv₃)).symm
  obtain ⟨u₂, -, hv₂⟩ := evalExp_caseE_iff.1 h₂
  obtain ⟨c, rfl⟩ := head_vconst (adminToVD_case (ha₂.trans hv₂)).symm
  obtain ⟨u₁, hu₁, hv₁⟩ := evalExp_caseE_iff.1 h₁
  obtain ⟨AT, I, rfl, hAT, -⟩ := Vec.inv_tup2 hu₁
  obtain ⟨AT', fat, hT⟩ := hq "at" _ hat
  have hA : AT' = AT :=
    Option.some.inj (fat.symm.trans (evalExp_varE_iff.1 (evalExp_subE_iff.1 hAT)))
  obtain ⟨t, b, rfl⟩ := decode_aconstD ⟨rfl, rfl, rfl⟩ (ha₁.trans hv₁) (hA ▸ hT)
  exact ⟨t, b, c, p, x, arg, j, rfl⟩

/-! ## Which load rule fires at which shape -/

theorem opt_none_of {env : Env} {ρ : VarEnv} {o : Option Value}
    (h : EvalExp env ρ (.optE none) (.opt o)) : o = none := by
  simpa using evalExp_optE_none_iff.1 h

theorem opt_case_of {env : Env} {ρ : VarEnv} {C : MixopS} {e : Exp} {o : Option Value}
    (h : EvalExp env ρ (.optE (some (.caseE C e))) (.opt o)) : ∃ u, o = some (.case C u) := by
  obtain ⟨u, hu, he⟩ := evalExp_optE_some_iff.1 h
  obtain ⟨u', -, rfl⟩ := evalExp_caseE_iff.1 hu
  exact ⟨u', by simpa using he⟩

section Kind

variable {B : Builtins} {s : Store H} {f : Frame} {A : Value} {I : Nat} {op : VecLoadOp} {n : Nat}
  {arg : MemArg} {w : Value}

/-- Rules 42 and 43 fire only at `v128.load`. -/
theorem vload_kind_full {k : Nat} (hk : k = 42 ∨ k = 43)
    (hf : Fires (simEnv B) "Step_read" k (.tuple [cfgV (stateVF F s f)
      [aconstV A I, vloadV (Round6.MemSimd.vecLoadOpV op) n arg], w])) : op = .full := by
  have ho : Round6.MemSimd.vecLoadOpV op = none := by
    rcases hk with rfl | rfl
    · obtain ⟨σ, -, -, -, -, -, ho, -, -⟩ :=
        fires_vload_inv (State.hasReadRules_simEnv B).vloadNumOob hf
      exact opt_none_of ho
    · obtain ⟨σ, -, -, -, -, -, ho, -, -⟩ :=
        fires_vload_inv (State.hasReadRules_simEnv B).vloadNumVal hf
      exact opt_none_of ho
  cases op <;> simp_all [Round6.MemSimd.vecLoadOpV]

/-- Rules 44 and 45 fire only at the widening loads. -/
theorem vload_kind_pack {k : Nat} (hk : k = 44 ∨ k = 45)
    (hf : Fires (simEnv B) "Step_read" k (.tuple [cfgV (stateVF F s f)
      [aconstV A I, vloadV (Round6.MemSimd.vecLoadOpV op) n arg], w])) :
    ∃ sx, op = .extend8x8 sx ∨ op = .extend16x4 sx ∨ op = .extend32x2 sx := by
  have ho : ∃ u, Round6.MemSimd.vecLoadOpV op = some (.case "SHAPE%X%_%" u) := by
    rcases hk with rfl | rfl
    · obtain ⟨σ, -, -, -, -, -, ho, -, -⟩ :=
        fires_vload_inv (State.hasReadRules_simEnv B).vloadPackOob hf
      exact opt_case_of ho
    · obtain ⟨σ, -, -, -, -, -, ho, -, -⟩ :=
        fires_vload_inv (State.hasReadRules_simEnv B).vloadPackVal hf
      exact opt_case_of ho
  cases op <;> simp_all [Round6.MemSimd.vecLoadOpV]

/-- Rules 46 and 47 fire only at the splat loads. -/
theorem vload_kind_splat {k : Nat} (hk : k = 46 ∨ k = 47)
    (hf : Fires (simEnv B) "Step_read" k (.tuple [cfgV (stateVF F s f)
      [aconstV A I, vloadV (Round6.MemSimd.vecLoadOpV op) n arg], w])) :
    ∃ p, op = .splat p := by
  have ho : ∃ u, Round6.MemSimd.vecLoadOpV op = some (.case "SPLAT" u) := by
    rcases hk with rfl | rfl
    · obtain ⟨σ, -, -, -, -, -, ho, -, -⟩ :=
        fires_vload_inv (State.hasReadRules_simEnv B).vloadSplatOob hf
      exact opt_case_of ho
    · obtain ⟨σ, -, -, -, -, -, ho, -, -⟩ :=
        fires_vload_inv (State.hasReadRules_simEnv B).vloadSplatVal hf
      exact opt_case_of ho
  cases op <;> simp_all [Round6.MemSimd.vecLoadOpV]

/-- Rules 48 and 49 fire only at the zero-extending loads. -/
theorem vload_kind_zero {k : Nat} (hk : k = 48 ∨ k = 49)
    (hf : Fires (simEnv B) "Step_read" k (.tuple [cfgV (stateVF F s f)
      [aconstV A I, vloadV (Round6.MemSimd.vecLoadOpV op) n arg], w])) :
    op = .zero32 ∨ op = .zero64 := by
  have ho : ∃ u, Round6.MemSimd.vecLoadOpV op = some (.case "ZERO" u) := by
    rcases hk with rfl | rfl
    · obtain ⟨σ, -, -, -, -, -, ho, -, -⟩ :=
        fires_vload_inv (State.hasReadRules_simEnv B).vloadZeroOob hf
      exact opt_case_of ho
    · obtain ⟨σ, -, -, -, -, -, ho, -, -⟩ :=
        fires_vload_inv (State.hasReadRules_simEnv B).vloadZeroVal hf
      exact opt_case_of ho
  cases op <;> simp_all [Round6.MemSimd.vecLoadOpV]

end Kind

/-! ## The ten obligations -/

/-- The conclusion of a load obligation, from a successor code `js` that is its own image. -/
theorem readOblig_of {c : Config H} {w : Value} {js : List Admin}
    (hw : w = .list (adminsToVD js)) (hs : Step P host c ⟨c.store, c.frame, js⟩) :
    ∃ is' js', Bwd.CodeEq is' js' ∧ w = .list (adminsToVD js') ∧
      Step P host c ⟨c.store, c.frame, is'⟩ :=
  ⟨js, js, Bwd.CodeEq.refl _, hw, hs⟩

/-- `bwdB_vloadOob` at a rule index given as a numeral. -/
theorem bwdB_vloadOobAt {k : Nat} {op : VecLoadOp} (hk : oobRule op = k) {s : Store H}
    {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width}
    {w : Value}
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w])) :
    ∃ js, w = .list (adminsToVD js) ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩ ⟨s, f, js⟩ := by
  subst hk
  obtain ⟨hw, hs⟩ := bwdB_vloadOob hf
  exact ⟨[.trap], hw, hs⟩

section Load

variable {s : Store H} {f : Frame} {a : AddrType} {i : BitVec a.intType.width} {op : VecLoadOp}
  {x : MemIdx} {arg : MemArg} {w : Value}

/-- Rules 42 and 43 at a decoded load. -/
theorem readMS_full {k : Nat} (hk : k = 42 ∨ k = 43)
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f) [aconstV (Encode.toValue a) i.toNat,
        vloadV (Round6.MemSimd.vecLoadOpV op) x.toNat arg], w]))
    (hB : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w])) :
    ∃ js, w = .list (adminsToVD js) ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩ ⟨s, f, js⟩ := by
  obtain rfl := vload_kind_full hk hf
  rcases hk with rfl | rfl
  · exact bwdB_vloadOobAt rfl hB
  · obtain ⟨v, hw, hs⟩ := bwdB_vloadFull hB
    exact ⟨[.plain (.vecConst v)], hw, hs⟩

/-- Rules 44 and 45 at a decoded load. -/
theorem readMS_pack {k : Nat} (hk : k = 44 ∨ k = 45)
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f) [aconstV (Encode.toValue a) i.toNat,
        vloadV (Round6.MemSimd.vecLoadOpV op) x.toNat arg], w]))
    (hB : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w])) :
    ∃ js, w = .list (adminsToVD js) ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩ ⟨s, f, js⟩ := by
  have hop := vload_kind_pack hk hf
  rcases hk with rfl | rfl
  · obtain ⟨sx, rfl | rfl | rfl⟩ := hop <;> exact bwdB_vloadOobAt rfl hB
  · obtain ⟨v, hw, hs⟩ := bwdB_vecLoadPack hop hB
    exact ⟨[.plain (.vecConst v)], hw, hs⟩

/-- Rules 46 and 47 at a decoded load. -/
theorem readMS_splat {k : Nat} (hk : k = 46 ∨ k = 47)
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f) [aconstV (Encode.toValue a) i.toNat,
        vloadV (Round6.MemSimd.vecLoadOpV op) x.toNat arg], w]))
    (hB : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w])) :
    ∃ js, w = .list (adminsToVD js) ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩ ⟨s, f, js⟩ := by
  obtain ⟨p, rfl⟩ := vload_kind_splat hk hf
  rcases hk with rfl | rfl
  · exact bwdB_vloadOobAt rfl hB
  · obtain ⟨v, hw, hs⟩ := bwdB_vecLoadSplat hB
    exact ⟨[.plain (.vecConst v)], hw, hs⟩

/-- Rules 48 and 49 at a decoded load. -/
theorem readMS_zero {k : Nat} (hk : k = 48 ∨ k = 49)
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f) [aconstV (Encode.toValue a) i.toNat,
        vloadV (Round6.MemSimd.vecLoadOpV op) x.toNat arg], w]))
    (hB : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w])) :
    ∃ js, w = .list (adminsToVD js) ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩ ⟨s, f, js⟩ := by
  have hop := vload_kind_zero hk hf
  rcases hk with rfl | rfl
  · rcases hop with rfl | rfl <;> exact bwdB_vloadOobAt rfl hB
  · rcases hop with rfl | rfl
    · obtain ⟨v, hw, hs⟩ := bwdB_vecLoadZero (N := 32) (.inl rfl) hB
      exact ⟨[.plain (.vecConst v)], hw, hs⟩
    · obtain ⟨v, hw, hs⟩ := bwdB_vecLoadZero (N := 64) (.inr rfl) hB
      exact ⟨[.plain (.vecConst v)], hw, hs⟩

/-- **The memory SIMD loads in bounds and out of bounds, at a decoded `v128.load…`.** -/
theorem readMS_vload {k : Nat} (hk : 42 ≤ k ∧ k ≤ 49)
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w])) :
    ∃ js, w = .list (adminsToVD js) ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩ ⟨s, f, js⟩ := by
  have ha : RefsGC.LhsIn loadTags (cfgV (stateVF F s f)
      [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)]) := by
    rw [State.adminToV_aconst, instrToVM_vecLoad]; exact lhsIn_vload _ _ _ _ _ _
  have hB := (Round6.Reading.firesB_read_iff _ loadTags_noCast ha).2 hf
  have hf' : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f) [aconstV (Encode.toValue a) i.toNat,
        vloadV (Round6.MemSimd.vecLoadOpV op) x.toNat arg], w]) := by
    rwa [State.adminToV_aconst, instrToVM_vecLoad] at hf
  have hcases : (k = 42 ∨ k = 43) ∨ (k = 44 ∨ k = 45) ∨ (k = 46 ∨ k = 47) ∨
      (k = 48 ∨ k = 49) := by omega
  rcases hcases with h | h | h | h
  · exact readMS_full h hf' hB
  · exact readMS_pack h hf' hB
  · exact readMS_splat h hf' hB
  · exact readMS_zero h hf' hB

end Load

/-- **The lane loads in bounds and out of bounds, at a decoded `v128.loadN_lane`.** -/
theorem readMS_vloadLane {k : Nat} (hk : k = 50 ∨ k = 51) {s : Store H} {f : Frame}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec 128} {p : PackSize} {x : MemIdx}
    {arg : MemArg} {j : LaneIdx} {w : Value}
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" k
      (.tuple [cfgV (stateVF F s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecLoadLane p x arg j)], w])) :
    ∃ js, w = .list (adminsToVD js) ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecLoadLane p x arg j)]⟩
        ⟨s, f, js⟩ := by
  have ha : RefsGC.LhsIn loadTags (cfgV (stateVF F s f) [adminToV (aconst a i), valV (.vec c),
      Round6.MemSimd.instrToVM (.vecLoadLane p x arg j)]) := by
    rw [State.adminToV_aconst, instrToVM_vecLoadLane]; exact lhsIn_vloadLane _ _ _ _ _ _ _ _
  have hB := (Round6.Reading.firesB_read_iff _ loadTags_noCast ha).2 hf
  rcases hk with rfl | rfl
  · obtain ⟨hw, hs⟩ := bwdB_vloadLaneOob hB
    exact ⟨[.trap], hw, hs⟩
  · obtain ⟨v, hw, hs⟩ := bwdB_vecLoadLane hB
    exact ⟨[.plain (.vecConst v)], hw, hs⟩

/-- Rules 42–49 fire only at the image of `CONST at i; v128.load…`. -/
theorem decode_vloadD_any {i : Nat} (hk : 42 ≤ i ∧ i ≤ 49) {Z : Value} {code : List Admin}
    {w : Value}
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" i
      (.tuple [cfgV Z (adminsToVD code), w])) :
    ∃ (a : AddrType) (b : BitVec a.intType.width) (op : VecLoadOp) (x : MemIdx) (arg : MemArg),
      code = [aconst a b, .plain (.vecLoad op x arg)] := by
  have h8 : i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact decode_vloadD (State.hasReadRules_simEnv _).vloadNumOob (by simp) hf
  · exact decode_vloadD (State.hasReadRules_simEnv _).vloadNumVal (by simp) hf
  · exact decode_vloadD (State.hasReadRules_simEnv _).vloadPackOob (by simp) hf
  · exact decode_vloadD (State.hasReadRules_simEnv _).vloadPackVal (by simp) hf
  · exact decode_vloadD (State.hasReadRules_simEnv _).vloadSplatOob (by simp) hf
  · exact decode_vloadD (State.hasReadRules_simEnv _).vloadSplatVal (by simp) hf
  · exact decode_vloadD (State.hasReadRules_simEnv _).vloadZeroOob (by simp) hf
  · exact decode_vloadD (State.hasReadRules_simEnv _).vloadZeroVal (by simp) hf

/-- Rules 50 and 51 fire only at the image of `CONST at i; VCONST c; v128.loadN_lane …`. -/
theorem decode_vloadLaneD_any {i : Nat} (hk : i = 50 ∨ i = 51) {Z : Value} {code : List Admin}
    {w : Value}
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" i
      (.tuple [cfgV Z (adminsToVD code), w])) :
    ∃ (a : AddrType) (b : BitVec a.intType.width) (cv : BitVec 128) (p : PackSize) (x : MemIdx)
      (arg : MemArg) (j : LaneIdx),
      code = [aconst a b, .plain (.vecConst cv), .plain (.vecLoadLane p x arg j)] := by
  rcases hk with rfl | rfl
  · exact decode_vloadLaneD (State.hasReadRules_simEnv _).vloadLaneOob (by simp) hf
  · exact decode_vloadLaneD (State.hasReadRules_simEnv _).vloadLaneVal (by simp) hf

/-- **The memory SIMD `Step_read` obligations of the dispatch at `configVD`**, at
`withVBytes (Prims.builtins …)`, for **every** configuration (pass 6): if one of rules 42–51
fires at the `configVD` image, the result is the image of a Core successor. The leaves are stated
at `stateVF`, so memory SIMD code in the store's function bodies is allowed. -/
theorem readMSD {i : Nat} (hi : i ∈ msReadRules) (c : Config H) (w : Value)
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" i
      (.tuple [configVD hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  obtain ⟨s, f, code⟩ := c
  have hcases : (42 ≤ i ∧ i ≤ 49) ∨ i = 50 ∨ i = 51 := by
    simp only [msReadRules, List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  -- `configVD` is `cfgV` at `stateVF`, with the `funcInstVD` images as function list.
  change Fires _ "Step_read" i (.tuple [cfgV (stateVF (.list (s.funcs.map (funcInstVD hn))) s f)
    (adminsToVD code), w]) at hf
  rcases hcases with hk | hk
  · obtain ⟨a, b, op, x, arg, rfl⟩ := decode_vloadD_any hk hf
    obtain ⟨js, hw, hst⟩ := readMS_vload hk hf
    exact readOblig_of hw hst
  · obtain ⟨a, b, cv, p, x, arg, j, rfl⟩ := decode_vloadLaneD_any hk hf
    obtain ⟨js, hw, hst⟩ := readMS_vloadLane hk hf
    exact readOblig_of hw hst

/-! ## The dispatch with the memory SIMD loads plugged in -/

/-- **The per-rule obligations at `configVD` from the remaining ones**, under any predicate: the
memory SIMD loads are `readMSD`. -/
theorem backwardUpToD_of_restD {V : Config H → Prop}
    (Rk : BackwardUpToDRest V (simEnv (withVBytes (Prims.builtins P hn host))) hn P host) :
    BackwardUpToD V (simEnv (withVBytes (Prims.builtins P hn host))) hn P host where
  pure := Rk.pure
  read i c w hv hc hf := by
    by_cases hi : i ∈ msReadRules
    · exact readMSD hi c w hf
    · exact Rk.read i hi c w hv hc hf
  step := Rk.step

/-- **Round 6's backward recursion at `configVD`, with the memory SIMD loads discharged**, under
any context-closed predicate (pass 6): a declarative SpecTec step from the `configVD` image of a
typed configuration is the image of a configuration equivalent to a Core successor, given the
obligations of the rules other than 42–51 (the typing facts are `typingFactsD_simEnv`). Memory
SIMD code may occur in the store. -/
theorem backward_upToD_restD {V : Config H → Prop} (CV : Round6.Target.CtxClosedVals V)
    (Rk : BackwardUpToDRest V (simEnv (withVBytes (Prims.builtins P hn host))) hn P host)
    (c : Config H) (w : Value) (hv : V c)
    (hc : TypedD (simEnv (withVBytes (Prims.builtins P hn host))) hn c)
    (hs : SStep (simEnv (withVBytes (Prims.builtins P hn host))) (configVD hn c) w) :
    BwdUpToD hn P host c w :=
  backward_upToD CV (backwardUpToD_of_restD Rk) (structDecodeD_simEnv _)
    (typingFactsD_simEnv _ hn) (hasStepRules_simEnv _)
    (Bwd.findRel_of_ruleAt (simEnv_execRules _).unreachable)
    (Bwd.findRel_of_ruleAt (simEnv_readRules _).call) c w hv hc hs

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
