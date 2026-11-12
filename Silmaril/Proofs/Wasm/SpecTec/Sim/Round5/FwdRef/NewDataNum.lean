module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef.Concatn

/-!
# Round 5, pass 2, track fwdref: `array.new_data-num`, forward (`Step_read` 76)

```
rule Step_read/array.new_data-num:
  z; (CONST I32 i) (CONST I32 n) (ARRAY.NEW_DATA x y)
    ~>  ($const($cunpack(zt), $cunpacknum_(zt, c)))^n (ARRAY.NEW_FIXED x n)
  -- Expand: $type(z, x) ~~ ARRAY (mut? zt)
  -- if $concatn_(byte, $zbytes_(zt, c)^n, $($zsize(zt)/8)) = $data(z, y).BYTES[i : n * $zsize(zt)/8]
```

Core's `arrayNewDataNum` reads the `n` fields with `readField?` at `i + k * (|zt|/8)`. Each read
is an in-bounds chunk whose little-endian value `c_k` fits `zt` (`R4Fwd.readField_spec`), so the
instance `c* := (litV zt c_k)_k` makes each `$zbytes_(zt, c_k)` that chunk
(`R4Fwd.applies_zbytes`); the chunks all have length `|zt|/8`, so `$concatn_` concatenates them
(`FwdRef.tryClauses_concatn`), and their concatenation is the slice `BYTES[i : n·|zt|/8]`
(`reads_spec`). The rule is not an `otherwise` rule, so nothing else must be refuted.
`newDataNumB_builtins` discharges `Round5.Fwd.NewDataNumB` for the concrete `B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open RefsGC
open R4Fwd (litV fieldOfLit readField_spec applies_zbytes evalExp_constField evalExp_divBy8
  dvd_storageSize evalExp_expandArray)
open Round5.Fwd (AggTypesB)
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## What Core reads -/

/-- **The `n` fields Core reads are `n` adjacent chunks**: each is the encoding of a word `c_k`
that fits `zt`, the fields are `fieldOfLit zt c_k`, and the chunks concatenate to the slice
starting at the first offset. -/
theorem reads_spec {zt : CStorageType} {bytes : ByteArray} {i w : Nat}
    (hw : w = storageSize zt / 8) :
    ∀ (N j : Nat) (vs : List Val),
      (List.range' j N).mapM (fun k => readField? zt bytes (i + k * w)) = some vs →
      ∃ ks : List Nat, vs = ks.map (fieldOfLit zt) ∧ ks.length = N ∧
        (∀ a ∈ ks, a < 2 ^ storageSize zt) ∧
        (ks.map (FwdMem.leBytesV w)).flatten =
          ((FwdMem.bytesV bytes).drop (i + j * w)).take (N * w)
  | 0, j, vs, h => by
    obtain rfl : vs = [] := by simpa using h.symm
    exact ⟨[], rfl, rfl, by simp, by simp⟩
  | N + 1, j, vs, h => by
    rw [List.range'_succ, List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hrest, rfl⟩ := h
    obtain ⟨a, ha, -, hsl, rfl⟩ := readField_spec hv
    obtain ⟨ks, rfl, hlen, hks, hcat⟩ := reads_spec hw N (j + 1) vs' hrest
    refine ⟨a :: ks, rfl, by simp [hlen], ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact hks b hb
    · rw [← hw] at hsl
      rw [List.map_cons, List.flatten_cons, hcat, hsl, show (N + 1) * w = w + N * w by ring,
        List.take_add, List.drop_drop]
      congr 3
      ring

/-! ## Iterations whose bodies evaluate pointwise -/

/-- **A `^n` iteration over an image list**, with a body that evaluates at each image. -/
theorem evalExp_iterNMap_of {env : Env} {ρ : VarEnv} {b : Exp} {x y c : IL.Id} {α : Type}
    {F G : α → Value} {l : List α} (hc : ρ.findVal? c = some (.num (.natN l.length)))
    (hy : ρ.findVal? y = some (.list (l.map F)))
    (hb : ∀ a ∈ l, EvalExp env (ρ.bindVals [(x, F a)]) b (G a)) :
    EvalExp env ρ (.iterE b (.mk (.listN (.varE c) none) [.mk x (.varE y)])) (.list (l.map G)) := by
  classical
  let g : Value → Value := fun w =>
    if hw : ∃ u, EvalExp env (ρ.bindVals [(x, w)]) b u then hw.choose else w
  have hg : ∀ a ∈ l, g (F a) = G a := by
    intro a ha
    have hex : ∃ u, EvalExp env (ρ.bindVals [(x, F a)]) b u := ⟨_, hb a ha⟩
    simp only [g, hex, dite_true]
    exact EvalExp.unique hex.choose_spec (hb a ha)
  have hmap : (l.map F).map g = l.map G := by
    rw [List.map_map]
    exact List.map_congr_left fun a ha => hg a ha
  rw [← hmap]
  refine evalExp_iterNMap (by simpa using hc) hy fun w hw => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hw
  rw [hg a ha]
  exact hb a ha

/-- A typed list, from typed elements. -/
theorem hasTyp_list_of {env : Env} {ρ : VarEnv} {t : Typ} :
    ∀ {vs : List Value}, (∀ v ∈ vs, HasTyp env ρ t v) → HasTyp env ρ (.iterT t .list) (.list vs)
  | [], _ => hasTyp_list_nil
  | v :: rest, h => hasTyp_list_cons_iff.2 ⟨h v (List.mem_cons_self ..),
      hasTyp_list_of (vs := rest) fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

/-! ## The rule -/

set_option maxHeartbeats 800000 in
/-- **`array.new_data-num` (`Step_read` rule 76), forward**, from a bounded frame module. -/
theorem sread_arrayNewDataNumB {P : Profile} (hF : Floats.FloatB P B) (Z : ZBytes.ZB B)
    (R : RTyping (simEnv B)) (A : AggTypesB (simEnv B)) {s : Store H} {f : Frame}
    [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {y : DataIdx} {i n : BitVec 32} {da : Nat}
    {d : DefType} {m : Mutability} {zt : CStorageType} {di : DataInst} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.array (.field m zt)))
    (hdat : s.data? f y = some (da, di)) (h0 : 0 < storageSize zt)
    (hl : i.toNat + n.toNat * storageSize zt / 8 ≤ di.bytes.size)
    (hvs : (List.range n.toNat).mapM (fun k => readField? zt di.bytes
      (i.toNat + k * (storageSize zt / 8))) = some vs)
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewData x y)]⟩)
      (adminsToV (vals vs ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)])) := by
  obtain ⟨ks, rfl, hlen, hks, hcat⟩ := reads_spec (zt := zt) (bytes := di.bytes) (i := i.toNat)
    rfl n.toNat 0 vs (by simpa [List.range_eq_range'] using hvs)
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("n", .num (.natN n.toNat)), ("x", Encode.toValue x), ("y", Encode.toValue y),
    ("zt", tyV zt), ("c*", .list (ks.map (litV zt))), ("mut?", mutV m)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hw8 : n.toNat * storageSize zt / 8 = n.toNat * (storageSize zt / 8) :=
    Nat.mul_div_assoc _ (dvd_storageSize zt h0)
  -- the element size and the slice length
  have hsz : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [.expA (.varE "zt")]) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN (storageSize zt / 8))) :=
    evalExp_divBy8 (dvd_storageSize zt h0) (Vec.evalExp_call (Aggregates.findDef_none hρ _)
      (evalArgs_cons (by eval_tac) evalArgs_nil) (R4Fwd.applies_zsize zt h0))
  have hlenE : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.binE .mulOp (.numT .natT) (.varE "n")
        (.callE "zsize" [.expA (.varE "zt")])) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT))
        .ratT .natT) (.num (.natN (n.toNat * (storageSize zt / 8)))) := by
    rw [← hw8]
    exact evalExp_divBy8 (Dvd.dvd.mul_left (dvd_storageSize zt h0) _) (evalExp_mulNat
      (t := .numT .natT) (by eval_tac) (Vec.evalExp_call (Aggregates.findDef_none hρ "zsize")
        (evalArgs_cons (by eval_tac) evalArgs_nil) (R4Fwd.applies_zsize zt h0)))
  have hdata : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "data" [.expA (.varE "z"), .expA (.varE "y")])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.dataInstToValue di) := by
    obtain ⟨M, Ls, As, a', hS, hM, hA, ha', hr⟩ := Memory.dataAt_of_data? hn hdat
    exact State.evalExp_data (State.stateDefs_simEnv B) (Aggregates.findDef_none hρ _)
      (by eval_tac) (by eval_tac) hS hM hA ha' hr
  -- the chunks
  have hzb : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.iterE (.callE "zbytes_" [.expA (.varE "zt"), .expA (.varE "c")])
        (.mk (.listN (.varE "n") none) [.mk "c" (.varE "c*")]))
      (.list (ks.map fun a => .list (FwdMem.leBytesV (storageSize zt / 8) a))) := by
    refine evalExp_iterNMap_of (F := litV zt) (by rw [hlen]; rfl) rfl fun a ha => ?_
    have hρ' : ValsOnly ((VarEnv.empty.bindVals σ).bindVals [("c", litV zt a)]) := ⟨rfl, rfl, rfl⟩
    exact Vec.evalExp_call (Aggregates.findDef_none hρ' _)
      (evalArgs_cons (evalExp_var rfl) (evalArgs_cons (evalExp_var rfl) evalArgs_nil))
      (applies_zbytes Z h0 (hks a ha))
  have hconcat : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "concatn_" [.typA (.varT "byte" []),
        .expA (.iterE (.callE "zbytes_" [.expA (.varE "zt"), .expA (.varE "c")])
          (.mk (.listN (.varE "n") none) [.mk "c" (.varE "c*")])),
        .expA (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [.expA (.varE "zt")])
          .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)])
      (.list (ks.map (FwdMem.leBytesV (storageSize zt / 8))).flatten) := by
    obtain ⟨cs, ⟨ps, t, hdf⟩, hT⟩ := tryClauses_concatn (concatnDefs_simEnv B) (.varT "byte" [])
      (storageSize zt / 8) (ks.map (FwdMem.leBytesV (storageSize zt / 8))) (by
        intro c hc
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hc
        exact FwdMem.leBytesV_length _ _)
    have hzb' : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.iterE (.callE "zbytes_" [.expA (.varE "zt"), .expA (.varE "c")])
          (.mk (.listN (.varE "n") none) [.mk "c" (.varE "c*")]))
        (.list ((ks.map (FwdMem.leBytesV (storageSize zt / 8))).map Value.list)) := by
      rw [List.map_map]
      exact hzb
    have hargs := evalArgs_typA (env := simEnv B) (ρ := VarEnv.empty.bindVals σ)
      (t := .varT "byte" []) (evalArgs_cons hzb' (evalArgs_cons hsz evalArgs_nil))
    exact evalExp_callE_iff.2 (callDef_of_tryClauses (Aggregates.findDef_none hρ _) hdf hargs hT)
  have hif : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "concatn_" [.typA (.varT "byte" []),
        .expA (.iterE (.callE "zbytes_" [.expA (.varE "zt"), .expA (.varE "c")])
          (.mk (.listN (.varE "n") none) [.mk "c" (.varE "c*")])),
        .expA (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [.expA (.varE "zt")])
          .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)])
        (.sliceE (.dotE (.callE "data" [.expA (.varE "z"), .expA (.varE "y")]) "BYTES")
          (.projE (.uncaseE (.varE "i") "%") 0)
          (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.binE .mulOp (.numT .natT) (.varE "n")
            (.callE "zsize" [.expA (.varE "zt")])) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT
            .ratT)) .ratT .natT))) (.bool true) := by
    refine evalExp_eq_true hconcat (evalExp_sliceE_iff.2 ⟨_, _, _, evalExp_dot hdata
      (Memory.dataInstV_BYTES di), evalExp_unpct (by eval_tac), hlenE, ?_⟩)
    have hcat' : (ks.map (FwdMem.leBytesV (storageSize zt / 8))).flatten =
        ((FwdMem.bytesV di.bytes).drop i.toNat).take (n.toNat * (storageSize zt / 8)) := by
      simpa using hcat
    rw [Silmaril.SpecTec.Equiv.ExecReadAggregate.slice?_list (by simpa [hw8] using hl), hcat']
    rfl
  -- the result
  have hres : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.iterE (.callE "const" [.expA (.callE "cunpack" [.expA (.varE "zt")]),
        .expA (.callE "cunpacknum_" [.expA (.varE "zt"), .expA (.varE "c")])])
        (.mk (.listN (.varE "n") none) [.mk "c" (.varE "c*")]))
      (.list (ks.map fun a => valV (fieldOfLit zt a))) := by
    refine evalExp_iterNMap_of (F := litV zt) (by rw [hlen]; rfl) rfl fun a ha => ?_
    have hρ' : ValsOnly ((VarEnv.empty.bindVals σ).bindVals [("c", litV zt a)]) := ⟨rfl, rfl, rfl⟩
    exact evalExp_constField hF hρ' h0 (hks a ha)
      rfl rfl
  have hrhs : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.catE (.iterE (.callE "const" [.expA (.callE "cunpack" [.expA (.varE "zt")]),
        .expA (.callE "cunpacknum_" [.expA (.varE "zt"), .expA (.varE "c")])])
        (.mk (.listN (.varE "n") none) [.mk "c" (.varE "c*")]))
        (.listE [.caseE "ARRAY.NEW_FIXED" (.tupE [.varE "x", .caseE "%" (.tupE [.varE "n"])])]))
      (.list (adminsToV (vals (ks.map (fieldOfLit zt)) ++
        [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]))) := by
    refine evalExp_catE_iff.2 ⟨_, _, hres, (by eval_tac : EvalExp (simEnv B)
      (VarEnv.empty.bindVals σ)
      (.listE [.caseE "ARRAY.NEW_FIXED" (.tupE [.varE "x", .caseE "%" (.tupE [.varE "n"])])])
      (.list [instrToV (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)])), ?_⟩
    simp [Value.cat?, adminsToV_append, adminsToV_vals, adminsToV, adminToV, List.map_map]
  refine dderives_of_ruleAt (Aggregates.rd B).arrayNewDataNum σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.i32 i _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
      (QuantsOk.cons rfl (hasTyp_list_of fun v hv => by
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
          exact R4Fwd.litTyping_simEnv B zt a _ hρ rfl h0 (hks a ha))
      (QuantsOk.cons rfl (A.mut_ m _ hρ) QuantsOk.nil))))))))
    (evalExp_tup2 (by eval_tac) hrhs)
    (prems_two (.rulePr evalArgs_nil (evalExp_expandArray hρ hd rfl rfl rfl rfl)
      (A.expand _ _ he)) (.ifPr hif))

/-- **`array.new_data-num`, as a forward obligation**, for every `B` with the discharged
families, `ZB` and `AggTypesB`. -/
theorem fwd_arrayNewDataNumB {P : Profile} (hF : Floats.FloatB P B) (Z : ZBytes.ZB B)
    (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B)) (A : AggTypesB (simEnv B))
    {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {y : DataIdx}
    {i n : BitVec 32} {da : Nat} {d : DefType} {ft : CFieldType} {di : DataInst} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (h0 : 0 < storageSize (fieldStorage ft))
    (hl : i.toNat + n.toNat * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size)
    (hvs : (List.range n.toNat).mapM (fun k => readField? (fieldStorage ft) di.bytes
      (i.toNat + k * (storageSize (fieldStorage ft) / 8))) = some vs) :
    FwdP (simEnv B) hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewData x y)]⟩
      ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩ := by
  obtain ⟨m, zt⟩ := ft
  exact RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ =>
    sread_arrayNewDataNumB hF Z R A hd he hdat h0 hl hvs hz

/-- **`Round5.Fwd.NewDataNumB` holds for the concrete `B`.** -/
theorem newDataNumB_builtins {P : Profile} (hn : H → String) (host : HostSemantics H) :
    Round5.Fwd.NewDataNumB (BI P hn host) hn := by
  intro s f x y i n d ft da di vs hM hd he hdat h0 hl hvs
  have : Fact (Round4.ModuleBnd f.module) := ⟨hM⟩
  exact fwd_arrayNewDataNumB (Prims.floatB_builtins hn host) (R4Fwd.zB_builtins hn host)
    (Typing.typingFacts_simEnv _ hn) (Typing.rTyping_simEnv _)
    (Round5.Fwd.aggTypesB_of (Round5.Int.typesB _)) hd he hdat h0 hl hvs

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef
