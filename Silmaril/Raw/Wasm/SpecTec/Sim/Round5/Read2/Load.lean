module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Common

/-!
# Round 5, pass 3, track read: the value loads (39, 41), backward

`load-num-val` (39) and `load-pack-val` (41) carry the premise
`$nbytes_(nt, c) = $mem(z, x).BYTES[i + ao.OFFSET : $size(nt)/8]` (resp. `$ibytes_(n, c) = …`).
Read back:

* the slice evaluates only in bounds (`Value.slice?`), so Core's `Memory.load` succeeds;
* `B` answers `$nbytes_`/`$ibytes_` by `FwdMem.nbytesCall`/`ibytesCall`, so the loaded `c` is a
  numeral of type `nt` (resp. a `%`-wrapped natural) whose little-endian encoding is the slice;
* the encoding is injective below `256 ^ k` (`leBytesV_inj`), so `c` is Core's loaded word;
* `$extend__` is `B`'s `extendBits` (41).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv)
open Round4Read (decode_aconst_typed decode_loadNum decode_loadPack)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## The little-endian encoding, inverted -/

theorem decL_encL : ∀ (k n : Nat), n < 256 ^ k → FwdMem.decL (FwdMem.encL k n) = n
  | 0, n, h => by simp at h; subst h; rfl
  | k + 1, n, h => by
    have ih := decL_encL k (n / 256) (by rw [Nat.pow_succ] at h; omega)
    simp only [FwdMem.encL, FwdMem.decL, List.foldr_cons] at ih ⊢
    rw [ih, UInt8.toNat_ofNat']
    omega

theorem pctV_inj {a b : Nat} (h : pctV a = pctV b) : a = b := by
  simpa [pctV] using h

theorem leBytesV_eq_map (k n : Nat) :
    FwdMem.leBytesV k n = (FwdMem.encL k n).map fun c => pctV c.toNat := by
  rw [FwdMem.leBytesV, FwdMem.bytesV_eq, FwdMem.encodeLE_toList]

/-- **The `k`-byte little-endian encoding is injective below `256 ^ k`.** -/
theorem leBytesV_inj {k n m : Nat} (hn : n < 256 ^ k) (hm : m < 256 ^ k)
    (h : FwdMem.leBytesV k n = FwdMem.leBytesV k m) : n = m := by
  rw [leBytesV_eq_map, leBytesV_eq_map] at h
  have e : FwdMem.encL k n = FwdMem.encL k m :=
    List.map_injective_iff.2 (fun a b hab => UInt8.toNat_inj.1 (pctV_inj hab)) h
  rw [← decL_encL k n hn, ← decL_encL k m hm, e]

/-- A load within bounds succeeds. -/
theorem load_some {mem : ByteArray} {i k : Nat} (h : i + k ≤ mem.size) :
    ∃ c, Silmaril.Wasm.Execution.Memory.load mem i k = some c := by
  simp [Silmaril.Wasm.Execution.Memory.load, Silmaril.Wasm.Execution.Memory.readBytes, h]

/-- **A slice of the memory's image, read back as a load**: a `k`-byte slice that evaluates and is
the encoding of `n < 2 ^ (8 * k)` is what Core's `Memory.load` reads, as a word with value `n`. -/
theorem load_of_slice {mem : ByteArray} {i k n : Nat} {v : Value} (hn : n < 2 ^ (8 * k))
    (hs : Value.slice? (.list (FwdMem.bytesV mem)) i k = some v)
    (hv : v = .list (FwdMem.leBytesV k n)) :
    ∃ c : BitVec (8 * k), Silmaril.Wasm.Execution.Memory.load mem i k = some c ∧ c.toNat = n := by
  simp only [Value.slice?, FwdMem.bytesV_length] at hs
  split at hs
  · rename_i hle
    obtain ⟨c, hc⟩ := load_some hle
    refine ⟨c, hc, ?_⟩
    have hb := (FwdMem.load_bytesV hc).2
    have hp : (2 : Nat) ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]
    subst hv
    have e : FwdMem.leBytesV k c.toNat = FwdMem.leBytesV k n := by
      rw [hb]
      exact (Value.list.inj (Option.some.inj hs))
    exact leBytesV_inj (hp ▸ c.isLt) (hp ▸ hn) e
  · cases hs

/-! ## The byte builtins, inverted -/

theorem decNum_eq_some {t : NumType} {v : Value} {b : BitVec t.width}
    (h : Floats.decNum t v = some b) : numV ⟨t, b⟩ = v := by
  unfold Floats.decNum at h
  split at h
  · rename_i hex
    obtain rfl := Option.some.inj h
    exact Classical.choose_spec hex
  · cases h

theorem call_nbytes (nt c : Value) :
    (BI P hn host).call "nbytes_" [.val nt, .val c] = FwdMem.nbytesCall nt c := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

theorem call_ibytes (N c : Value) :
    (BI P hn host).call "ibytes_" [.val N, .val c] = FwdMem.ibytesCall N c := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- **`$nbytes_(nt, c)`, read back**: `c` is a numeral of type `nt`, and the value its encoding. -/
theorem nbytes_inv {t : NumType} {c u : Value}
    (h : Applies (simEnv (BI P hn host)) "nbytes_" [.val (Encode.toValue t), .val c] u) :
    ∃ b : BitVec t.width, c = numV ⟨t, b⟩ ∧ u = .list (FwdMem.leBytesV (t.width / 8) b.toNat) := by
  have hb := Simd.applies_noClause_iff (FwdMem.findDef_nbytes _) h
  rw [show (simEnv (BI P hn host)).builtins = BI P hn host from rfl, call_nbytes,
    Typing.toValue_numType] at hb
  cases hd : Floats.decNum t c with
  | none => simp [FwdMem.nbytesCall, Floats.decNumType_numTypeV, hd] at hb
  | some b =>
    simp [FwdMem.nbytesCall, Floats.decNumType_numTypeV, hd] at hb
    exact ⟨b, (decNum_eq_some hd).symm, hb.symm⟩

/-- **`$ibytes_(N, c)`, read back**. -/
theorem ibytes_inv {N : Nat} {c u : Value}
    (h : Applies (simEnv (BI P hn host)) "ibytes_" [.val (.num (.natN N)), .val c] u) :
    ∃ k, c = pctV k ∧ u = .list (FwdMem.leBytesV (N / 8) k) := by
  have hb := Simd.applies_noClause_iff (FwdMem.findDef_ibytes _) h
  rw [show (simEnv (BI P hn host)).builtins = BI P hn host from rfl, call_ibytes] at hb
  unfold FwdMem.ibytesCall at hb
  split at hb
  all_goals first
    | (cases hb; done)
    | exact ⟨_, rfl, by simp_all⟩


/-! ## The memory slice, read back -/

/-- **The slice `$mem(z, x).BYTES[i + ao.OFFSET : k]`, read back**: the memory resolves, and the
slice is `Value.slice?` of its byte image at Core's effective address. -/
theorem memSlice_inv {ρ : VarEnv} (hρ : ρ.findDef? "mem" = none) {s : Store H} {f : Frame}
    {x : MemIdx} {a : AddrType} {b : BitVec a.intType.width} {arg : MemArg} {ek : Exp} {v : Value}
    (fz : ρ.findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fx : ρ.findVal? "x" = some (idxV x.toNat)) (fi : ρ.findVal? "i" = some (idxV b.toNat))
    (fao : ρ.findVal? "ao" = some (memargV arg))
    (h : EvalExp (simEnv (BI P hn host)) ρ
      (.sliceE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")
        (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
          (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)) ek) v) :
    ∃ ma mi k, s.mem? f x = some (ma, mi) ∧ EvalExp (simEnv (BI P hn host)) ρ ek (.num (.natN k)) ∧
      Value.slice? (.list (FwdMem.bytesV mi.bytes)) (effAddr b.toNat arg) k = some v := by
  obtain ⟨W, ea, k, hW, hea, hk, hsl⟩ := evalExp_sliceE_iff.1 h
  obtain ⟨Mv, hMv, hB⟩ := evalExp_dotE_iff.1 hW
  obtain ⟨ma, mi, hm, rfl⟩ := BwdRead.mem_inv _ (BwdRead.noAcc_builtins P hn host) hρ fz fx hMv
  rw [FwdMem.memInstV_BYTES'] at hB
  obtain rfl := Option.some.inj hB
  have e : Value.num (.natN ea) = .num (.natN (b.toNat + arg.offset.val)) :=
    EvalExp.unique hea (Memory.evalExp_effAddr (evalExp_var fi) (evalExp_var fao))
  simp only [Value.num.injEq, Num.natN.injEq] at e
  subst e
  exact ⟨ma, mi, k, hm, hk, hsl⟩

/-! ## `load-num-val` (39) -/

theorem const_out_int {t : IntType} {b : BitVec t.width} :
    adminToV (.plain (.intConst t b)) =
      .case "CONST" (.tuple [Encode.toValue (NumType.int t), numV ⟨.int t, b⟩]) := rfl

theorem const_out_float {t : FloatType} {b : BitVec t.width} :
    adminToV (.plain (.floatConst t b)) =
      .case "CONST" (.tuple [Encode.toValue (NumType.float t), numV ⟨.float t, b⟩]) := rfl

/-- **`Step_read` 39 (`load-num-val`), backward.** -/
theorem bwd_loadNumVal : ∀ (c : Config H) (w : Value),
    Fires (simEnv (BI P hn host)) "Step_read" 39 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv (BI P hn host)).loadNumVal hf)
  have hρ := Memory.findDef_bindVals_empty σ
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, hAT⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨NT, fnt, -⟩ := hq "nt" (.varT "numtype" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨AO, fao, -⟩ := hq "ao" (.varT "memarg" []) (by simp)
  obtain ⟨C, fc, -⟩ := hq "c" (.varT "num_" [.expA (.varE "nt")]) (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT, I]), .case "LOAD" (.tuple [NT, .opt none, X, AO])]]) ∧
      w = .list [.case "CONST" (.tuple [NT, C])] := by
    concl_inv' he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hcode
  obtain ⟨t, x, arg, ha₂, rfl, rfl, rfl⟩ := decode_loadNum h₂
  obtain ⟨at_, b, rfl, rfl, rfl⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT
  subst hZ
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain rfl := Silmaril.SpecTec.Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  have hA : Applies (simEnv (BI P hn host)) "nbytes_" [.val (Encode.toValue t), .val C] v₁ :=
    (applies_iff_callDef (hρ _) (Equiv.evalArgs_cons (evalExp_var fnt)
      (Equiv.evalArgs_cons (evalExp_var fc) Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 e₁)
  obtain ⟨c, rfl, rfl⟩ := nbytes_inv hA
  obtain ⟨ma, mi, k, hm, hk, hsl⟩ := memSlice_inv (hρ _) fz fx fi fao e₂
  have ek : Value.num (.natN k) = .num (.natN (t.width / 8)) :=
    EvalExp.unique hk (FwdMem.evalExp_widthNum (State.growDefs_simEnv _) (Memory.sizeDefs_simEnv _)
      t (evalExp_var fnt))
  simp only [Value.num.injEq, Num.natN.injEq] at ek
  subst ek
  have hw8 : 8 * (t.width / 8) = t.width := by
    rcases t with t | t <;> cases t <;> rfl
  obtain ⟨c', hl, hc'⟩ := load_of_slice (n := c.toNat) (by rw [hw8]; exact c.isLt) hsl rfl
  have ec : c'.setWidth t.width = c := by
    apply BitVec.eq_of_toNat_eq
    rw [FwdMem.toNat_setWidth_of_le c' hw8.le, hc']
  rcases ha₂ with ⟨it, rfl, rfl⟩ | ⟨ft, rfl, rfl⟩
  · refine ⟨[.plain (.intConst it (c'.setWidth it.width))], ?_, .memory (.loadIntVal hm hl)⟩
    rw [hc.2, ← ec]
    rfl
  · refine ⟨[.plain (.floatConst ft (c'.setWidth ft.width))], ?_, .memory (.loadFloatVal hm hl)⟩
    rw [hc.2, ← ec]
    rfl

/-! ## `load-pack-val` (41) -/

theorem encL_mod : ∀ (k n : Nat), FwdMem.encL k n = FwdMem.encL k (n % 256 ^ k)
  | 0, _ => rfl
  | k + 1, n => by
    simp only [FwdMem.encL]
    congr 1
    · apply UInt8.toNat_inj.1
      rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', Nat.mod_mod_of_dvd]
      exact Dvd.intro_left (256 ^ k) (by rw [Nat.pow_succ]; rfl)
    · rw [encL_mod k (n / 256), encL_mod k (n % 256 ^ (k + 1) / 256), Nat.pow_succ,
        Nat.mul_comm (256 ^ k) 256, Nat.mod_mul_right_div_self, Nat.mod_mod]

/-- The `k`-byte encoding reads its argument modulo `2 ^ (8 * k)`. -/
theorem leBytesV_mod (k n : Nat) : FwdMem.leBytesV k n = FwdMem.leBytesV k (n % 2 ^ (8 * k)) := by
  rw [leBytesV_eq_map, leBytesV_eq_map, Nat.pow_mul, encL_mod k n]

theorem call_extend (N N' k : Nat) (sx : Signedness) :
    (BI P hn host).call "extend__" [.val (.num (.natN N)), .val (.num (.natN N')),
      .val (Equiv.sxV sx), .val (pctV k)] =
      some (Equiv.bvV (match sx with
        | .signed => (BitVec.ofNat N k).signExtend N'
        | .unsigned => (BitVec.ofNat N k).setWidth N')) := by
  refine Prims.floatB_builtins hn host _ _ _ ?_
  simp only [Floats.floatCall, show "extend__" ∈ Floats.floatNames by decide, ite_true]
  show Floats.extendBits N N' (Equiv.sxV sx) (pctV k) = _
  cases sx <;> simp [Floats.extendBits, IntNumeric.asSx?, Equiv.sxV, Equiv.ExecBuiltins.asBits?,
    pctV]

theorem signExtend_congr {a b N : Nat} (h : a = b) (v : BitVec a) (v' : BitVec b)
    (hv : v.toNat = v'.toNat) : v.signExtend N = v'.signExtend N := by
  subst h
  rw [BitVec.eq_of_toNat_eq hv]

theorem setWidth_congr {a b N : Nat} (h : a = b) (v : BitVec a) (v' : BitVec b)
    (hv : v.toNat = v'.toNat) : v.setWidth N = v'.setWidth N := by
  subst h
  rw [BitVec.eq_of_toNat_eq hv]

/-- **`Step_read` 41 (`load-pack-val`), backward.** -/
theorem bwd_loadPackVal : ∀ (c : Config H) (w : Value),
    Fires (simEnv (BI P hn host)) "Step_read" 41 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv (BI P hn host)).loadPackVal hf)
  have hρ := Memory.findDef_bindVals_empty σ
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, hAT⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨NT, fnt, -⟩ := hq "Inn" (.varT "Inn" []) (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨SX, fsx, -⟩ := hq "sx" (.varT "sx" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨AO, fao, -⟩ := hq "ao" (.varT "memarg" []) (by simp)
  obtain ⟨C, fc, -⟩ := hq "c" (.varT "iN" [.expA (.varE "n")]) (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT, I]), .case "LOAD" (.tuple [NT, .opt (some (.case "%_%"
        (.tuple [.case "%" (.tuple [N]), SX]))), X, AO])]]) := by
    concl_inv hl
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hcode
  obtain ⟨t, sz, sx, x, arg, rfl, rfl, rfl, rfl, rfl, rfl⟩ := decode_loadPack h₂
  obtain ⟨at_, b, rfl, rfl, rfl⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT
  subst hZ
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain rfl := Silmaril.SpecTec.Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  have hA : Applies (simEnv (BI P hn host)) "ibytes_" [.val (.num (.natN sz.width)), .val C] v₁ :=
    (applies_iff_callDef (hρ _) (Equiv.evalArgs_cons (evalExp_var fn)
      (Equiv.evalArgs_cons (evalExp_var fc) Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 e₁)
  obtain ⟨k, rfl, rfl⟩ := ibytes_inv hA
  obtain ⟨ma, mi, j, hm, hj, hsl⟩ := memSlice_inv (hρ _) fz fx fi fao e₂
  have ej : Value.num (.natN j) = .num (.natN (sz.width / 8)) :=
    EvalExp.unique hj (Memory.evalExp_div8 (by cases sz <;> simp [PackSize.width])
      (evalExp_var fn))
  simp only [Value.num.injEq, Num.natN.injEq] at ej
  subst ej
  obtain ⟨c', hl', hc'⟩ := load_of_slice (n := k % 2 ^ (8 * (sz.width / 8)))
    (Nat.mod_lt _ (by positivity)) hsl (by rw [← leBytesV_mod])
  have hw8 := FwdMem.width8_pack sz
  have hcv : c'.toNat = (BitVec.ofNat sz.width k).toNat := by
    rw [hc', BitVec.toNat_ofNat, hw8]
  have hext := Vec.evalExp_call (hρ _) (Equiv.evalArgs_cons (evalExp_var fn)
    (Equiv.evalArgs_cons (FwdMem.evalExp_sizeInn hρ fnt) (Equiv.evalArgs_cons (evalExp_var fsx)
      (Equiv.evalArgs_cons (evalExp_var fc) Equiv.evalArgs_nil))))
    (Prims.applies_of_noClause (R4Fwd.findDef_extend _) (call_extend (P := P) (hn := hn)
      (host := host) sz.width t.width k sx))
  have hw := EvalExp.unique (RefsGC.rhs_of_concl he) (RefsGC.evalExp_listE_of
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (RefsGC.evalExp_sub_of (evalExp_var fnt))
      hext)) RefsGC.evalExps_nil'))
  refine ⟨_, ?_, .memory (.loadPackVal hm hl')⟩
  rw [hw]
  cases sx
  · rw [signExtend_congr hw8 c' _ hcv]
    rfl
  · rw [setWidth_congr hw8 c' _ hcv]
    rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2
