module

public import Silmaril.Wasi.Versions.DnsOver.Defs
public import Silmaril.Wasi.Versions.Udp.Over.Thms

@[expose] public section

/-!
# Name lookup across versions: theorems

PROVED (standard axioms):

* `dnsE2to3_names`, `dnsE3to2_names`: the code tables translate by name (against `codes2` and
  `dnsCodes3`), and every code without a counterpart goes to `other` / `unknown`.
* **(b) 0.3 over 0.2**: `dns3Over2_sat`, **`dns3Over2_model`**: for every resolver `R`, every
  number of rounds and every host of `dnsTh R`, the composite is a model of `dnsTh3 R`. Key
  lemma `wp_collect`: reading a stream of a name collects addresses of the name.
* **(c) 0.2 over 0.3**: `dns2Over3_sat`, **`dns2Over3_model`**: for every resolver `R` and every
  host of `dnsTh3 R`, the composite is a model of `dnsTh R`, with the invariant `JD`.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Codes -/

/-- 0.2 codes translate to 0.3 lookup codes by name, or to `other`. -/
theorem dnsE2to3_names : ∀ k < codes2.length, dnsCodes3[dnsE2to3 k]? = codes2[k]? ∨
    (dnsE2to3 k = dnsOther3 ∧ codes2[k]?.all (· ∉ dnsCodes3)) := by
  decide +kernel

/-- 0.3 lookup codes translate to 0.2 codes by name, or to `unknown`. -/
theorem dnsE3to2_names : ∀ k < dnsCodes3.length, codes2[dnsE3to2 k]? = dnsCodes3[k]? ∨
    (dnsE3to2 k = 0 ∧ dnsCodes3[k]?.all (· ∉ codes2)) := by
  decide +kernel

/-! ## The theory states and checks -/

/-- Functions other than `resolve-addresses` keep the 0.2 lookup state. -/
theorem dnsNext_other (q : DnsSt) {f : FnName} (h : f ≠ resolve2) (a : List Val)
    (r : Option (List Val)) : dnsNext q (.imp f a r) = q := by
  unfold dnsNext
  split <;> simp_all

/-- A successful `resolve-addresses` names the stream. -/
theorem dnsNext_res_ok (q : DnsSt) (x name : Val) (rest : List Val) (h : BitVec 32) :
    dnsNext q (.imp resolve2 (x :: name :: rest) (some [.variant 0 (some (.u32 h))])) =
      (h, name) :: q := by
  simp [dnsNext]

/-- An error or a trap of `resolve-addresses` keeps the 0.2 lookup state. -/
theorem dnsNext_res_err (q : DnsSt) (a : List Val) {r : Option (List Val)}
    (hr : r = none ∨ ∃ p, r = some [.variant 1 p]) : dnsNext q (.imp resolve2 a r) = q := by
  unfold dnsNext
  split <;> rcases hr with hr | ⟨p, hr⟩ <;> simp_all

/-- Functions other than `resolve-next-address` pass the 0.2 lookup check. -/
theorem dnsOk_ne (R : Resolver) (q : DnsSt) {f : FnName} (hf : f ≠ resolveNext) (a : List Val)
    (r : Option (List Val)) : dnsOk R q (.imp f a r) = true := by
  unfold dnsOk
  split <;> simp_all

/-- An answer every list check accepts passes the 0.3 lookup check. -/
theorem dnsOk3_of (R : Resolver) (f : FnName) (a : List Val) {r : Option (List Val)}
    (h : ∀ d, listOk d r = true) : dnsOk3 R () (.imp f a r) = true := by
  unfold dnsOk3
  split
  · split
    · simp_all
    · rfl
  · rfl

/-- A translated 0.2 error passes every list check. -/
theorem listOk_dnsErr3 (d : Val → Bool) (r : Option (List Val)) : listOk d (dnsErr3 r) = true := by
  unfold dnsErr3
  split <;> rfl

/-- A translated 0.3 error is an error or a trap. -/
theorem dnsErr2_err (r : Option (List Val)) :
    dnsErr2 r = none ∨ ∃ p, dnsErr2 r = some [.variant 1 p] := by
  unfold dnsErr2
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

/-- An error answer or a trap passes every `resolve-next-address` check. -/
theorem nextOk_err (d : Val → Bool) {r : Option (List Val)}
    (hr : r = none ∨ ∃ p, r = some [.variant 1 p]) : nextOk d r = true := by
  rcases hr with rfl | ⟨p, rfl⟩ <;> rfl

/-- An answer every next check accepts passes the 0.2 lookup check. -/
theorem dnsOk_of (R : Resolver) (q : DnsSt) (f : FnName) (a : List Val) {r : Option (List Val)}
    (h : ∀ d, nextOk d r = true) : dnsOk R q (.imp f a r) = true := by
  unfold dnsOk
  split
  · split
    · split <;> simp_all
    · rfl
  · rfl

/-! ## (b) 0.3 over 0.2 -/

/-- The answer of `collect` when the stream ends: the collected list. -/
theorem collect_done {R : Resolver} {name : Val} {acc : List Val} (hacc : ∀ x ∈ acc, R name x = true)
    (rest : List Val) :
    dnsOk3 R () (.imp resolve3 (name :: rest) (some [okV (some (.record acc))])) = true := by
  simpa [dnsOk3, listOk, okV] using hacc

/-- **Reading a stream of `name`** collects addresses of `name`, or answers an error or traps. -/
theorem wp_collect (R : Resolver) (st : BitVec 32) (name : Val) (rest : List Val) :
    ∀ (k : Nat) (acc : List Val) (qT : DnsSt), lookup st qT = some name →
      (∀ x ∈ acc, R name x = true) →
      Wp (dnsTh R) (collect st k acc)
        (fun x _ => dnsOk3 R () (.imp resolve3 (name :: rest) x.2) = true) qT
  | 0, _, _, _, _ => dnsOk3_of R _ _ fun _ => rfl
  | k + 1, acc, qT, hl, hacc => fun r qT' hstep => by
    obtain ⟨hok, hq⟩ := gated_step_iff.1 hstep
    have hn : dnsNext qT (.imp resolveNext [.u32 st] r) = qT := dnsNext_other qT (by decide) _ _
    have hq' : qT' = qT := hq.trans hn
    have hnext : nextOk (R name) r = true := by simpa [dnsOk, dNext, hl] using hok
    rw [hq']
    beta_reduce
    split
    · next a =>
      have ha : R name a = true := by simpa [nextOk] using hnext
      refine wp_collect R st name rest k (acc ++ [a]) qT hl fun x hx => ?_
      rcases List.mem_append.1 hx with hx | hx
      · exact hacc x hx
      · exact (List.mem_singleton.1 hx) ▸ ha
    · exact collect_done hacc rest
    · next =>
      show Wp (dnsTh R) (if isWouldBlock r then collect st k acc else .pure ((), dnsErr3 r)) _ qT
      by_cases hw : isWouldBlock r = true
      · simpa only [hw, ↓reduceIte] using wp_collect R st name rest k acc qT hl hacc
      · simp only [hw, Bool.false_eq_true, ↓reduceIte]
        exact dnsOk3_of R _ _ fun d => listOk_dnsErr3 d r

/-- After the 0.2 `resolve-addresses(nv, name)` answered `r₁`. -/
theorem wp_resolved (R : Resolver) (rounds : Nat) (nv name : Val) (rest : List Val) (qT : DnsSt)
    (r₁ : Option (List Val)) :
    Wp (dnsTh R) (afterRes rounds r₁)
      (fun x _ => dnsOk3 R () (.imp resolve3 (name :: rest) x.2) = true)
      (dnsNext qT (.imp resolve2 [nv, name] r₁)) := by
  unfold afterRes
  split
  · next st =>
    have hl : lookup st (dnsNext qT (.imp resolve2 [nv, name] (some [.variant 0 (some (.u32 st))])))
        = some name := by
      rw [dnsNext_res_ok]
      exact lookup_cons_self _ _ _
    exact wp_collect R st name rest rounds [] _ hl fun _ hx => absurd hx List.not_mem_nil
  · exact dnsOk3_of R _ _ fun d => listOk_dnsErr3 d _

/-- **`resolve-addresses` over 0.2** passes the 0.3 check. -/
theorem wp_resolve3 (R : Resolver) (rounds : Nat) (a : List Val) (qT : DnsSt) :
    Wp (dnsTh R) (resolve3Prog rounds a)
      (fun x _ => dnsOk3 R () (.imp resolve3 a x.2) = true) qT := by
  unfold resolve3Prog
  split
  · next name rest =>
    intro r₀ qT₁ h₀
    have hn : dnsNext qT (.imp instanceNetwork [] r₀) = qT := dnsNext_other qT (by decide) _ _
    have hq₁ : qT₁ = qT := (gated_step_iff.1 h₀).2.trans hn
    rw [hq₁]
    beta_reduce
    split
    · next nv =>
      exact fun r₁ qT₂ h₁ => (gated_step_iff.1 h₁).2 ▸ wp_resolved R rounds nv name rest qT r₁
    · exact dnsOk3_of R _ _ fun _ => rfl
  · exact dnsOk3_of R _ _ fun _ => rfl

/-- The invariant of `dns3Over2` (none needed). -/
theorem dns3Over2_inv (R : Resolver) (rounds : Nat) :
    WpInv (dns3Over2 rounds) () (dnsTh R) (dnsTh3 R) (fun _ _ _ => True) where
  init := trivial
  call := by
    intro _ qT _ q _
    have hq : q.1.1 = resolve3 := by simpa [dns3Fns_eq] using q.1.2
    exact Wp.mono (fun x _ hx => ⟨(), gated_step_of (by rw [hq]; exact hx), trivial⟩)
      (wp_resolve3 R rounds q.2 qT)

/-- **The component guarantee of name lookup 0.3 over 0.2.** -/
theorem dns3Over2_sat (R : Resolver) (rounds : Nat) :
    (agP (dnsTh R) (retG (dnsTh3 R))).holds (ofSBody (dns3Over2 rounds) ()) :=
  ag_of_wpInv (dns3Over2_inv R rounds)

/-- **Name lookup 0.3 over 0.2**: over every host of `dnsTh R`, the composite is a model of
`dnsTh3 R`. -/
theorem dns3Over2_model (R : Resolver) (rounds : Nat) {Y : Sig.{0}} {η : Host Y dns2Fns}
    (hη : (hostSat (dnsTh R).Accepts).holds η) :
    (hostSat (dnsTh3 R).Accepts).holds (link η (ofSBody (dns3Over2 rounds) ())) :=
  link_model (dns3Over2_sat R rounds) hη

/-! ## (c) 0.2 over 0.3 -/

/-- An exported step of the 0.2 lookup theory that keeps its state. -/
theorem dns_step_keep {R : Resolver} {qG : DnsSt} {e : WEv} (hok : dnsOk R qG e = true)
    (hn : dnsNext qG e = qG) : (dnsTh R).step qG e = some qG :=
  gated_step_iff.2 ⟨hok, hn.symm⟩

/-- A new stream keeps the invariant. -/
theorem jD_cons {R : Resolver} {st : DSt} {qG : DnsSt} (hJ : JD R st () qG) (h : BitVec 32)
    (name : Val) (l : List Val) (hl : ∀ x ∈ l, R name x = true) (n : Nat) :
    JD R { store := (h, l) :: st.store, next := n } () ((h, name) :: qG) := by
  intro h' name' hq
  by_cases he : h' = h
  · rw [he, lookup_cons_self] at hq
    refine ⟨l, by rw [he]; exact lookup_cons_self _ _ _, fun x hx => ?_⟩
    exact Option.some.inj hq ▸ hl x hx
  · rw [lookup_cons_ne he] at hq
    obtain ⟨l', hl', hall⟩ := hJ h' name' hq
    exact ⟨l', by show lookup h' ((h, l) :: st.store) = some l'; rw [lookup_cons_ne he]; exact hl',
      hall⟩

/-- **`resolve-addresses` over 0.3** keeps the invariant. -/
theorem wp_resolve2 (R : Resolver) {st : DSt} {qG : DnsSt} (hJ : JD R st () qG) (a : List Val) :
    Wp (dnsTh3 R) (resolve2Prog st a) (fun x qT' => ∃ qG',
      (dnsTh R).step qG (.imp resolve2 a x.2) = some qG' ∧ JD R x.1 qT' qG') () := by
  have hkeep : ∀ r, (r = none ∨ ∃ p, r = some [.variant 1 p]) →
      ∃ qG', (dnsTh R).step qG (.imp resolve2 a r) = some qG' ∧ JD R st () qG' :=
    fun r hr => ⟨qG, dns_step_keep (dnsOk_ne R qG (by decide) _ _) (dnsNext_res_err qG a hr), hJ⟩
  unfold resolve2Prog
  split
  · next x name rest =>
    intro r qT' h
    have hok : dnsOk3 R () (.imp resolve3 [name] r) = true := (gated_step_iff.1 h).1
    beta_reduce
    split
    · next l =>
      have hl : ∀ y ∈ l, R name y = true := by simpa [dnsOk3, eRes3, listOk] using hok
      refine ⟨(BitVec.ofNat 32 st.next, name) :: qG, gated_step_iff.2
        ⟨dnsOk_ne R qG (by decide) _ _, ?_⟩, jD_cons hJ _ name l hl _⟩
      exact (dnsNext_res_ok qG x name rest _).symm
    · exact hkeep _ (dnsErr2_err _)
  · exact hkeep _ (Or.inr ⟨_, rfl⟩)

/-- A popped stream keeps the invariant. -/
theorem jD_pop {R : Resolver} {st : DSt} {qG : DnsSt} (hJ : JD R st () qG) {h : BitVec 32}
    {x : Val} {l : List Val} (hs : lookup h st.store = some (x :: l)) :
    JD R { st with store := (h, l) :: st.store } () qG := by
  intro h' name hq
  obtain ⟨l', hl', hall⟩ := hJ h' name hq
  by_cases he : h' = h
  · rw [he] at hl'
    rw [hs] at hl'
    have hl'' : l' = x :: l := (Option.some.inj hl').symm
    refine ⟨l, by rw [he]; exact lookup_cons_self _ _ _, fun y hy => ?_⟩
    exact hall y (hl'' ▸ List.mem_cons_of_mem x hy)
  · exact ⟨l', by show lookup h' ((h, l) :: st.store) = some l'; rw [lookup_cons_ne he]; exact hl',
      hall⟩

/-- **`resolve-next-address` over 0.3** answers addresses of the stream's name and keeps the
invariant. -/
theorem next_ok (R : Resolver) {st : DSt} {qG : DnsSt} (hJ : JD R st () qG) (a : List Val) :
    ∃ qG', (dnsTh R).step qG (.imp resolveNext a (nextRes st a).2) = some qG' ∧
      JD R (nextRes st a).1 () qG' := by
  have hn : ∀ r, dnsNext qG (.imp resolveNext a r) = qG := fun r => dnsNext_other qG (by decide) _ _
  unfold nextRes
  split
  · next h rest =>
    split
    · next x l hs =>
      have hok : dnsOk R qG (.imp resolveNext (.u32 h :: rest)
          (some [okV (some (.variant 1 (some x)))])) = true := by
        cases hq : lookup h qG with
        | none => simp [dnsOk, hq]
        | some name =>
          obtain ⟨l', hl', hall⟩ := hJ h name hq
          rw [hs] at hl'
          have hx : R name x = true := hall x (Option.some.inj hl' ▸ List.mem_cons_self ..)
          simpa [dnsOk, hq, nextOk, okV] using hx
      exact ⟨qG, dns_step_keep hok (hn _), jD_pop hJ hs⟩
    · exact ⟨qG, dns_step_keep (dnsOk_of R qG _ _ fun _ => rfl) (hn _), hJ⟩
    · exact ⟨qG, dns_step_keep (dnsOk_of R qG _ _ fun _ => rfl) (hn _), hJ⟩
  · exact ⟨qG, dns_step_keep (dnsOk_of R qG _ _ fun _ => rfl) (hn _), hJ⟩

/-- The invariant of `dns2Over3`. -/
theorem dns2Over3_inv (R : Resolver) : WpInv dns2Over3 {} (dnsTh3 R) (dnsTh R) (JD R) where
  init := fun h name hq => by simp [lookup, dnsTh, gated] at hq
  call := by
    intro st qT qG q hJ
    by_cases h₁ : q.1.1 = instanceNetwork
    · simp only [dns2Over3, h₁, ↓reduceIte]
      exact ⟨qG, dns_step_keep (dnsOk_ne R qG (f := instanceNetwork) (by decide) _ _)
        (dnsNext_other qG (by decide) _ _), hJ⟩
    by_cases h₂ : q.1.1 = resolve2
    · simp only [dns2Over3, h₂, ↓reduceIte]
      exact wp_resolve2 R hJ q.2
    have h₃ : q.1.1 = resolveNext := by
      have hm := q.1.2
      simp only [dns2Fns_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      exact (hm.resolve_left h₁).resolve_left h₂
    simp only [dns2Over3, h₁, h₂, ↓reduceIte]
    rw [h₃]
    exact next_ok R hJ q.2

/-- **The component guarantee of name lookup 0.2 over 0.3.** -/
theorem dns2Over3_sat (R : Resolver) :
    (agP (dnsTh3 R) (retG (dnsTh R))).holds (ofSBody dns2Over3 {}) :=
  ag_of_wpInv (dns2Over3_inv R)

/-- **Name lookup 0.2 over 0.3**: over every host of `dnsTh3 R`, the composite is a model of
`dnsTh R`. -/
theorem dns2Over3_model (R : Resolver) {Y : Sig.{0}} {η : Host Y dns3Fns}
    (hη : (hostSat (dnsTh3 R).Accepts).holds η) :
    (hostSat (dnsTh R).Accepts).holds (link η (ofSBody dns2Over3 {})) :=
  link_model (dns2Over3_sat R) hη

end Silmaril.Wasi.Versions.Net
