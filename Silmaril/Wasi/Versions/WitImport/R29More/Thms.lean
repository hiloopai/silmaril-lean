module

public import Silmaril.Wasi.Versions.WitImport.R29Typing.Thms
public import Silmaril.Wasi.Versions.WitImport.RNetTyping.Thms

@[expose] public section

/-!
# The 0.2.12 typing results and refutations, restated for WASI 0.2.9

`Silmaril.Wasi.Versions.WitImport.R29Typing` showed that each 0.2.9 package renames onto the 0.2.12
one (`io29_rn`, `sock29_rn`, `http29_rn`, `rand29_rn`; `wasi:cli` without `exit-with-code`) and
that renaming does not change the resolved typing (`witROk_29`). This module moves the remaining
0.2.12 results of `RIo2`, `RCli2`, `RNet`, `RNetTyping` and `RP3` to the 0.2.9 tables, with the
same witnesses:

* **Typing results** (sound direction or converse): `cliOk_eqR29` (on named-type-free results,
  `P2.cliOk` is the resolved check against the 0.2.9 signature, which exists), `witR_p2Ok29`
  (converse for `cli2C`, on 0.2.9-typed arguments), `tcpOk_witR29`, `httpOk_witR_up29`,
  `ok2R_eq29` (`Random.ok2` is the 0.2.9 typing plus the length checks).
* **Refutations**: `witR_not_ioTh29`, `witR_not_p2Ok29`, `cliOk_not_witR29`,
  `tcpOk_not_witR_code29`, `finish_witR_not_tcpOk29`, `netMore_not_witR29`,
  `netMore_typed_decisive29` (the 0.2 half; the 0.3 half does not mention 0.2.9).

Each is proved by rewriting with the renaming equations, not by evaluating the 0.2.9 tables
again, except `p29_rn_cli2L` (the `cli2L` restriction, decided by the kernel like
`p29_rn_cli2S`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasi.Versions

/-! ## Moving along a renaming -/

/-- **The unrestricted typing of a 0.2.9 package is that of the 0.2.12 package.** -/
theorem witROk_eq29 {P Q : RPkg} (h : rnPkg rn29 P = Q) (e : WEv) :
    witROk P e = witROk Q e := by
  rw [← h, witROk_rn (swapVer_injective _ _)]

/-- Renaming does not change which arguments are typed. -/
theorem argsTypedR_rn {ρ : Binary.IfaceName → Binary.IfaceName} (hρ : Function.Injective ρ)
    (P : RPkg) (e : WEv) : argsTypedR (rnPkg ρ P) e = argsTypedR P e := by
  cases e with
  | imp f a r =>
    simp only [argsTypedR, rnPkg_lookup]
    cases P.1.lookup f with
    | none => rfl
    | some x => simp [rnPkg, argsOkR_rn hρ]
  | _ => rfl

theorem argsTypedR_eq29 {P Q : RPkg} (h : rnPkg rn29 P = Q) (e : WEv) :
    argsTypedR P e = argsTypedR Q e := by
  rw [← h, argsTypedR_rn (swapVer_injective _ _)]

/-- On `cli2L` (which has no `exit-with-code`), the 0.2.9 slice renames to the 0.2.12 one. -/
theorem p29_rn_cli2L : rrestrict (rnPkg rn29 p29P) cli2L = rrestrict p2P cli2L := by
  decide +kernel

theorem witROk_cli2L29 (e : WEv) :
    witROk (rrestrict p29P cli2L) e = witROk (rrestrict p2P cli2L) e := by
  rw [← witROk_rn (swapVer_injective "0.2.9" "0.2.12"), rnPkg_rrestrict, p29_rn_cli2L]

/-- The type environments of the two slices correspond. -/
theorem p29_env : rnEnv rn29 p29P.2 = p2P.2 := by
  have h := congrArg Prod.snd p29_rn_cli2L
  simpa [rrestrict, rnPkg] using h

/-- A 0.2.9 entry of a `cli2L` function is the renamed 0.2.12 entry. -/
theorem p29_lookup {f : FnName} (hf : f ∈ cli2L) :
    p2P.1.lookup f = (p29P.1.lookup f).map fun x => (rn29 x.1, rnSig rn29 x.2) := by
  have h := congrArg (fun P : RPkg => P.1.lookup f) p29_rn_cli2L
  simp only [lookup_rrestrict, hf, ite_true, rnPkg_lookup] at h
  exact h.symm

/-! ## Typing results -/

/-- **On named-type-free results, `P2.cliOk` is the resolved check against the 0.2.9
signature**, and every function of `cli2X` has one. -/
theorem cliOk_eqR29 (f : FnName) (hf : f ∈ cli2X) :
    (p29P.1.lookup f).isSome = true ∧
      ∀ i s, p29P.1.lookup f = some (i, s) →
        ∀ r, P2.cliOk f r = resOkR p29P.2 i s r := by
  have hL := cli2X_sub f hf
  obtain ⟨i2, s2, hl2, hi2, hs2⟩ := resOkR_entry hL
  have hl := p29_lookup hL
  refine ⟨?_, fun i s hl9 r => ?_⟩
  · cases h9 : p29P.1.lookup f with
    | none => simp [h9, hl2] at hl
    | some _ => rfl
  · rw [hl9, hl2] at hl
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    rw [cliOk_eqR f hf r, ← hi2, ← resOkR_result hs2,
      ← resOkR_rn (swapVer_injective "0.2.9" "0.2.12") p29P.2 i s r, p29_env]

/-- Arguments typed against a 0.2.9 entry are typed against the 0.2.12 entry. -/
theorem argsOkR_29 {f : FnName} (hL : f ∈ cli2L) {a : List Val}
    (ha : ∀ i s, p29P.1.lookup f = some (i, s) → argsOkR p29P.2 i s a = true)
    {i : Binary.IfaceName} {s : Binary.Sig} (hl2 : p2P.1.lookup f = some (i, s)) :
    argsOkR p2P.2 i s a = true := by
  have hm : (p29P.1.lookup f).map (fun x => (rn29 x.1, rnSig rn29 x.2)) = some (i, s) :=
    (p29_lookup hL).symm.trans hl2
  obtain ⟨⟨i', s'⟩, h9, hx⟩ : ∃ x, p29P.1.lookup f = some x ∧
      (rn29 x.1, rnSig rn29 x.2) = (i, s) := Option.map_eq_some_iff.1 hm
  have hi : rn29 i' = i := congrArg Prod.fst hx
  have hs : rnSig rn29 s' = s := congrArg Prod.snd hx
  rw [← hi, ← hs, ← p29_env, argsOkR_rn (swapVer_injective _ _)]
  exact ha _ _ h9

/-- **Converse for `cli2C` against 0.2.9**: on arguments typed against the 0.2.9 signature, a
0.2.9-typed answer passes `P2.p2Ok`. -/
theorem witR_p2Ok29 (f : FnName) (hf : f ∈ cli2C) (a : List Val) (r : Option (List Val))
    (ha : ∀ i s, p29P.1.lookup f = some (i, s) → argsOkR p29P.2 i s a = true)
    (h : witROk (rrestrict p29P cli2C) (.imp f a r) = true) : P2.p2Ok (.imp f a r) = true := by
  have hL : f ∈ cli2L := cli2C_sub f hf
  have e9 : witROk (rrestrict p29P cli2C) (.imp f a r) =
      witROk (rrestrict p29P cli2L) (.imp f a r) := by
    simp [witROk, lookup_rrestrict, rrestrict_snd, hf, hL]
  have e2 : witROk (rrestrict p2P cli2C) (.imp f a r) =
      witROk (rrestrict p2P cli2L) (.imp f a r) := by
    simp [witROk, lookup_rrestrict, rrestrict_snd, hf, hL]
  have h2 : witROk (rrestrict p2P cli2C) (.imp f a r) = true := by
    rw [e2, ← witROk_cli2L29, ← e9]; exact h
  exact witR_p2Ok f hf a r (fun _ _ hl2 => argsOkR_29 hL ha hl2) h2

/-- **An accepted `finish-connect` answer on a pending socket is typed against 0.2.9**, for a
typed network. -/
theorem tcpOk_witR29 (N : Net.Network) (hN : TypedNet N 21) (q : Net.TcpSt) (s : BitVec 32)
    (rest : List Val) (r : Option (List Val)) (hp : (Net.lookup s q).isSome = true)
    (h : Net.tcpOk N q (.imp Net.finishConnect (.u32 s :: rest) r) = true) :
    witROk (rrestrict sock29P [Net.finishConnect]) (.imp Net.finishConnect (.u32 s :: rest) r) =
      true := by
  rw [witROk_29 sock29_rn]
  exact tcpOk_witR N hN q s rest r hp h

/-- **On a future of a request, an accepted `get` answer is typed against 0.2.9**, for a web
that never fails. -/
theorem httpOk_witR_up29 (W : Net.Web) (hW : WebUp W) (q : Net.HttpSt) (h0 : BitVec 32)
    (rest : List Val) (r : Option (List Val)) (hp : (Net.lookup h0 q.futs).isSome = true)
    (h : Net.httpOk W q (.imp Net.futGet (.u32 h0 :: rest) r) = true) :
    witROk (rrestrict http29P [Net.futGet]) (.imp Net.futGet (.u32 h0 :: rest) r) = true := by
  rw [witROk_29 http29_rn]
  exact httpOk_witR_up W hW q h0 rest r hp h

/-- **`Random.ok2` is the 0.2.9 resolved typing plus the length checks.** -/
theorem ok2R_eq29 (e : WEv) : Random.ok2 e = (witROk rand29P e && len2 e) := by
  rw [ok2R_eq, witROk_eq29 rand29_rn]

/-! ## Refutations -/

/-- **REFUTED for 0.2.9: a 0.2.9-typed `write` without a permit is rejected by `P2.ioTh`.** -/
theorem witR_not_ioTh29 :
    witROk (rrestrict io29P io2L) writeOkNoPermit = true ∧
      ¬ (P2.ioTh .loose).Accepts [writeOkNoPermit] ∧
      ¬ (P2.ioTh .strict).Accepts [writeOkNoPermit] := by
  rw [witROk_29 io29_rn]
  exact witR_not_ioTh

/-- **REFUTED converse for the wall clock and `exit`, against 0.2.9.** -/
theorem witR_not_p2Ok29 :
    (witROk (rrestrict p29P cli2L) badWall = true ∧ P2.p2Ok badWall = false) ∧
    (witROk (rrestrict p29P cli2L) exitReturns = true ∧ P2.p2Ok exitReturns = false) := by
  rw [witROk_cli2L29, witROk_cli2L29]
  exact witR_not_p2Ok

/-- **REFUTED sound direction for `read-via-stream` and `get-type`, against 0.2.9.** -/
theorem cliOk_not_witR29 :
    (P2.p2Ok badViaStream = true ∧ witROk (rrestrict p29P cli2L) badViaStream = false) ∧
    (P2.p2Ok badGetType = true ∧ witROk (rrestrict p29P cli2L) badGetType = false) := by
  rw [witROk_cli2L29, witROk_cli2L29]
  exact cliOk_not_witR

/-- **REFUTED for an untyped network, against 0.2.9.** -/
theorem tcpOk_not_witR_code29 :
    Net.tcpOk net21 [(0, .u32 0)] finish21 = true ∧
      witROk (rrestrict sock29P [Net.finishConnect]) finish21 = false := by
  rw [witROk_29 sock29_rn]
  exact tcpOk_not_witR_code

/-- **REFUTED converse for `finish-connect`, against 0.2.9.** -/
theorem finish_witR_not_tcpOk29 :
    witROk (rrestrict sock29P [Net.finishConnect]) finishDenied = true ∧
      Net.tcpOk Net.netUp [(0, .u32 0)] finishDenied = false := by
  rw [witROk_29 sock29_rn]
  exact finish_witR_not_tcpOk

/-- **REFUTED for a failing web, against 0.2.9.** -/
theorem httpOk_not_witR29 :
    Net.httpOk Net.webDown futState getJunk = true ∧
      witROk (rrestrict http29P [Net.futGet]) getJunk = false := by
  rw [witROk_29 http29_rn]
  exact httpOk_not_witR

/-- **REFUTED sound direction for UDP, accept and 0.2 name lookup, against 0.2.9.** -/
theorem netMore_not_witR29 :
    (Net.udpOk Net.udpQuiet udpTied recvBad = true ∧ argsTypedR sock29P recvBad = true ∧
      witROk sock29P recvBad = false) ∧
    (Net.accOk Net.noPeers accBound acceptBad = true ∧ argsTypedR sock29P acceptBad = true ∧
      witROk sock29P acceptBad = false) ∧
    (Net.dnsOk Net.dnsEmpty dnsNamed nextBad = true ∧ argsTypedR sock29P nextBad = true ∧
      witROk sock29P nextBad = false) := by
  simp only [argsTypedR_eq29 sock29_rn, witROk_eq29 sock29_rn]
  exact ⟨netMore_not_witR.1, netMore_not_witR.2.1, netMore_not_witR.2.2.1⟩

/-- **REFUTED converse for UDP, accept and 0.2 name lookup, against 0.2.9**: the decisive
events are 0.2.9-typed. -/
theorem netMore_typed_decisive29 :
    (argsTypedR sock29P recvOne = true ∧ witROk sock29P recvOne = true ∧
      Net.udpDecisive udpTied recvOne ∧
      Net.udpOk udpAll udpTied recvOne = true ∧ Net.udpOk Net.udpQuiet udpTied recvOne = false) ∧
    (argsTypedR sock29P acceptOne = true ∧ witROk sock29P acceptOne = true ∧
      Net.accDecisive accBound acceptOne ∧
      Net.accOk allPeers accBound acceptOne = true ∧
      Net.accOk Net.noPeers accBound acceptOne = false) ∧
    (argsTypedR sock29P nextOne = true ∧ witROk sock29P nextOne = true ∧
      Net.dnsDecisive dnsNamed nextOne ∧
      Net.dnsOk dnsAll dnsNamed nextOne = true ∧
      Net.dnsOk Net.dnsEmpty dnsNamed nextOne = false) := by
  simp only [argsTypedR_eq29 sock29_rn, witROk_eq29 sock29_rn]
  exact ⟨netMore_typed_decisive.1, netMore_typed_decisive.2.1, netMore_typed_decisive.2.2.1⟩

end Silmaril.Wasi.Versions.WitImport
