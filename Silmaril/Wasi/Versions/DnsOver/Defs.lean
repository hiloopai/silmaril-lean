module

public import Silmaril.Wasi.Versions.Udp.Over.Defs
public import Silmaril.Wasi.Versions.WitImport.PickRest.Defs

@[expose] public section

/-!
# Name lookup across versions: 0.3 over 0.2 and 0.2 over 0.3

Two components between the 0.2 name lookup slice (`dns2Fns`: `instance-network`,
`resolve-addresses`, `resolve-address-stream.resolve-next-address`; theory `dnsTh R`) and the
0.3 one (`dns3Fns`: the async `resolve-addresses`, sync-lowered; theory `dnsTh3 R`), for the same
resolver `R`.

0.3 `wasi:sockets/ip-name-lookup` has its own `error-code` (`specs/wasi/0.3.2/sockets/
ip-name-lookup.wit`): `access-denied`, `invalid-argument`, `name-unresolvable`,
`temporary-resolver-failure`, `permanent-resolver-failure`, `other(option<string>)`
(`dnsCodes3`). `dnsE2to3`/`dnsE3to2` translate by name (checked against the case lists in
`DnsOver.Thms`); codes without a counterpart go to `other` (0.3) and `unknown` (0.2).

**`dns3Over2 rounds`** (relation (b)): `resolve-addresses(name)` calls `instance-network()` and
the 0.2 `resolve-addresses(network, name)`, then reads `resolve-next-address` until it answers
`ok(none)`, at most `rounds` times (retrying on `would-block`), and answers the list. It traps
when the rounds run out and on ill-typed answers; a 0.2 error is translated.

**`dns2Over3`** (relation (c)): `resolve-addresses(network, name)` calls the 0.3
`resolve-addresses(name)` (sync-lowered) and stores the list under a fresh stream handle;
`resolve-next-address(stream)` pops it (`ok(some a)`, then `ok(none)`), and answers
`error(invalid-state)` for an unknown stream.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-- The 0.2 name lookup functions, **read from the vendored WIT** (`sock2T` with the keys
`WitImport.dns2Keys`). Proofs that need the members rewrite with `dns2Fns_eq`. -/
def dns2Fns : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.sock2T) WitImport.dns2Keys}

/-- **The imported 0.2 name lookup functions are the hand-written ones.** -/
theorem dns2Fns_eq : dns2Fns = {instanceNetwork, resolve2, resolveNext} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.sock2T) WitImport.dns2Keys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.sock2T) WitImport.dns2Keys).Perm
    [instanceNetwork, resolve2, resolveNext] by decide +kernel).mem_iff]
  simp

/-- The 0.3 name lookup functions, **read from the vendored WIT** (`sock3T` with the keys
`WitImport.dns3Keys`). Proofs that need the members rewrite with `dns3Fns_eq`. -/
def dns3Fns : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.sock3T) WitImport.dns3Keys}

/-- **The imported 0.3 name lookup functions are the hand-written one.** -/
theorem dns3Fns_eq : dns3Fns = {resolve3} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.sock3T) WitImport.dns3Keys ↔ _
  rw [(show WitImport.pick (WitImport.names WitImport.sock3T) WitImport.dns3Keys = [resolve3] by
    decide +kernel)]
  simp

/-- The cases of 0.3 `ip-name-lookup.error-code`, in order, **read from the vendored WIT**
(`WitImport.dnsCodes3W`; `dnsCodes3_eq_hand`). -/
def dnsCodes3 : List String := WitImport.dnsCodes3W

/-- 0.3 lookup `error-code.other` (`dnsOther3_wit`: the case number of `other`). -/
abbrev dnsOther3 : Nat := 5

/-- A 0.2 code as a 0.3 lookup code, by name (`other` without a counterpart), from the WIT
(`dnsE2to3_eq_hand`). -/
def dnsE2to3 : Nat → Nat := WitImport.dnsE2to3W

/-- A 0.3 lookup code as a 0.2 code, by name (`unknown` without a counterpart), from the WIT
(`dnsE3to2_eq_hand`). -/
def dnsE3to2 : Nat → Nat := WitImport.dnsE3to2W

/-- The value of a 0.3 lookup `error-code` (`other` carries `option::none`), from the WIT
payloads (`dnsEcV3_eq_hand`). -/
def dnsEcV3 : Nat → Val := WitImport.dnsEcV3W

/-! ### The hand-written tables (related variants) -/

/-- `dnsCodes3`, as written by hand. -/
def dnsCodes3H : List String :=
  ["access-denied", "invalid-argument", "name-unresolvable", "temporary-resolver-failure",
   "permanent-resolver-failure", "other"]

/-- `dnsE2to3`, as written by hand. -/
def dnsE2to3H : Nat → Nat
  | 1 => 0 | 3 => 1 | 18 => 2 | 19 => 3 | 20 => 4
  | _ => dnsOther3

/-- `dnsE3to2`, as written by hand. -/
def dnsE3to2H : Nat → Nat
  | 0 => 1 | 1 => 3 | 2 => 18 | 3 => 19 | 4 => 20
  | _ => 0

/-- `dnsEcV3`, as written by hand. -/
def dnsEcV3H (k : Nat) : Val :=
  if k = dnsOther3 then .variant k (some (.variant 0 none)) else .variant k none

/-- **The WIT-derived lookup codes are the hand-written ones.** -/
theorem dnsCodes3_eq_hand : dnsCodes3 = dnsCodes3H := by decide +kernel

/-- The literal is the case number of `other` in the WIT. -/
theorem dnsOther3_wit : dnsOther3 = WitImport.caseIdx dnsCodes3 "other" := by decide +kernel

theorem dnsE2to3_lt_hand : ∀ k, k < 21 → dnsE2to3 k = dnsE2to3H k := by decide +kernel
theorem dnsE3to2_lt_hand : ∀ k, k < 6 → dnsE3to2 k = dnsE3to2H k := by decide +kernel

/-- **The WIT-derived 0.2 → 0.3 lookup translation is the hand-written table**, defaults
included. -/
theorem dnsE2to3_eq_hand : dnsE2to3 = dnsE2to3H := by
  funext k
  by_cases hk : k < 21
  · exact dnsE2to3_lt_hand k hk
  · have h1 : WitImport.codes2W[k]? = none := by
      rw [show WitImport.codes2W = codes2H by decide +kernel]
      exact List.getElem?_eq_none (by simp [codes2H]; omega)
    have h2 : dnsE2to3H k = dnsOther3 := by
      unfold dnsE2to3H
      split <;> omega
    have h3 : WitImport.dnsOther3W = dnsOther3 := by decide +kernel
    show WitImport.dnsE2to3W k = dnsE2to3H k
    rw [WitImport.dnsE2to3W, h1, h2, h3]

/-- **The WIT-derived 0.3 → 0.2 lookup translation is the hand-written table**, defaults
included. -/
theorem dnsE3to2_eq_hand : dnsE3to2 = dnsE3to2H := by
  funext k
  by_cases hk : k < 6
  · exact dnsE3to2_lt_hand k hk
  · have h1 : WitImport.dnsCodes3W[k]? = none := by
      rw [show WitImport.dnsCodes3W = dnsCodes3H from dnsCodes3_eq_hand]
      exact List.getElem?_eq_none (by simp [dnsCodes3H]; omega)
    have h2 : dnsE3to2H k = 0 := by
      unfold dnsE3to2H
      split <;> omega
    have h3 : WitImport.caseIdx WitImport.codes2W "unknown" = 0 := by decide +kernel
    show WitImport.dnsE3to2W k = dnsE3to2H k
    rw [WitImport.dnsE3to2W, h1, h2, h3]

/-- The payloads of the 0.3 lookup `error-code` cases: only the last, `other`, has one. -/
theorem dnsPayloads3W_eq :
    WitImport.dnsPayloads3W = List.replicate 5 none ++ [some (.option (.prim .string))] := by
  decide +kernel

/-- **The WIT-derived 0.3 lookup code value is the hand-written one.** -/
theorem dnsEcV3_eq_hand : dnsEcV3 = dnsEcV3H := by
  funext k
  show WitImport.dnsEcV3W k = dnsEcV3H k
  unfold WitImport.dnsEcV3W
  rw [dnsPayloads3W_eq]
  rcases Nat.lt_or_ge k 5 with h | h
  · have hk : k ≠ dnsOther3 := by simp only [dnsOther3]; omega
    rw [List.getElem?_append_left (by simpa using h), List.getElem?_replicate]
    simp only [h, ↓reduceIte]
    simp [dnsEcV3H, hk]
  · rcases Nat.eq_or_lt_of_le h with h | h
    · subst h; rfl
    · have hk : k ≠ dnsOther3 := by simp only [dnsOther3]; omega
      rw [List.getElem?_eq_none (by simp; omega)]
      simp [dnsEcV3H, hk]

/-! ## 0.3 over 0.2 -/

/-- `instance-network` as a 0.2 import. -/
def dNet : {f // f ∈ dns2Fns} := ⟨instanceNetwork, by simp [dns2Fns_eq]⟩
/-- `resolve-addresses` as a 0.2 import. -/
def dRes : {f // f ∈ dns2Fns} := ⟨resolve2, by simp [dns2Fns_eq]⟩
/-- `resolve-next-address` as a 0.2 import. -/
def dNext : {f // f ∈ dns2Fns} := ⟨resolveNext, by simp [dns2Fns_eq]⟩

/-- The 0.3 error answer of a 0.2 error answer (a trap otherwise). -/
def dnsErr3 : Option (List Val) → Option (List Val)
  | some [.variant 1 (some (.variant k _))] => some [errV (some (dnsEcV3 (dnsE2to3 k)))]
  | _ => none

/-- Read the stream `st` into `acc`, at most `k` more times. -/
def collect (st : BitVec 32) : Nat → List Val → SProg Unit dns2Fns
  | 0, _ => .pure ((), none)
  | k + 1, acc => .call (dNext, [.u32 st]) fun r =>
    match r with
    | some [.variant 0 (some (.variant 1 (some a)))] => collect st k (acc ++ [a])
    | some [.variant 0 (some (.variant 0 none))] => .pure ((), some [okV (some (.record acc))])
    | r => if isWouldBlock r then collect st k acc else .pure ((), dnsErr3 r)

/-- After the 0.2 `resolve-addresses` answered: read the stream, or translate the error. -/
def afterRes (rounds : Nat) : Option (List Val) → SProg Unit dns2Fns
  | some [.variant 0 (some (.u32 st))] => collect st rounds []
  | r₁ => .pure ((), dnsErr3 r₁)

/-- The program of `resolve-addresses(name)`. -/
def resolve3Prog (rounds : Nat) (a : List Val) : SProg Unit dns2Fns :=
  match a with
  | name :: _ =>
    .call (dNet, []) fun r₀ =>
      match r₀ with
      | some [nv] => .call (dRes, [nv, name]) (afterRes rounds)
      | _ => .pure ((), none)
  | _ => .pure ((), none)

/-- **Name lookup 0.3 over 0.2.** -/
def dns3Over2 (rounds : Nat) : SBody Unit dns2Fns dns3Fns := fun _ q => resolve3Prog rounds q.2

/-! ## 0.2 over 0.3 -/

/-- `resolve-addresses` as a 0.3 import. -/
def eRes3 : {f // f ∈ dns3Fns} := ⟨resolve3, by simp [dns3Fns_eq]⟩

/-- The state of `dns2Over3`: the remaining addresses of each stream, and the next handle. -/
structure DSt where
  /-- The remaining addresses of each stream. -/
  store : List (BitVec 32 × List Val) := []
  /-- The next stream handle. -/
  next : Nat := 0

/-- The 0.2 error answer of a 0.3 lookup error answer (a trap otherwise). -/
def dnsErr2 : Option (List Val) → Option (List Val)
  | some [.variant 1 (some (.variant k _))] => errAnsN (dnsE3to2 k)
  | _ => none

/-- The program of the 0.2 `resolve-addresses(network, name)`. -/
def resolve2Prog (st : DSt) (a : List Val) : SProg DSt dns3Fns :=
  match a with
  | _ :: name :: _ =>
    .call (eRes3, [name]) fun r =>
      match r with
      | some [.variant 0 (some (.record l))] =>
        .pure ({ store := (BitVec.ofNat 32 st.next, l) :: st.store, next := st.next + 1 },
          some [okV (some (.u32 (BitVec.ofNat 32 st.next)))])
      | r => .pure (st, dnsErr2 r)
  | _ => .pure (st, errAnsN eInvalidArg)

/-- The result of `resolve-next-address(stream)` (no import call). -/
def nextRes (st : DSt) (a : List Val) : DSt × Option (List Val) :=
  match a with
  | .u32 h :: _ =>
    match lookup h st.store with
    | some (x :: l) => ({ st with store := (h, l) :: st.store }, some [okV (some (.variant 1 (some x)))])
    | some [] => (st, some [okV (some (.variant 0 none))])
    | none => (st, errAnsN eInvalidState)
  | _ => (st, errAnsN eInvalidArg)

/-- **Name lookup 0.2 over 0.3.** -/
def dns2Over3 : SBody DSt dns3Fns dns2Fns := fun st q =>
  if q.1.1 = instanceNetwork then .pure (st, some [.u32 0])
  else if q.1.1 = resolve2 then resolve2Prog st q.2
  else .pure (nextRes st q.2)

/-- **The invariant of `dns2Over3`** over the resolver `R`: every stream of a name in the 0.2
theory state has a stored list, all of whose addresses are addresses of the name. -/
def JD (R : Resolver) (st : DSt) (_ : Unit) (qG : DnsSt) : Prop :=
  ∀ h name, lookup h qG = some name → ∃ l, lookup h st.store = some l ∧ ∀ x ∈ l, R name x = true

end Silmaril.Wasi.Versions.Net
