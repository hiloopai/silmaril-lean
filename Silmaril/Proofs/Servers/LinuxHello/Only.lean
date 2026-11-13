module

public import Silmaril.Servers.LinuxHello.Defs
public import Silmaril.Servers.Compare.Thms
public import Silmaril.Servers.Wire1.Thms
public import Silmaril.Net.Http1.Framing.Thms
public import Silmaril.Net.Http1.Message.Thms

/-!
# A Linux hello server loop: what any prefix of hello responses frames as

For `Silmaril.Servers.LinuxHello.Thms`: no strict prefix of `helloWire`'s octets frames as a
response (`hello_prefix_err`), so the octets a server has sent, when they are a prefix of
`helloWire` repeated, frame as `helloWire`s only (`parseResponses_hello`), and every exchange
of a connection whose sent octets are such a prefix answers `helloResp` (`onlyHello_of_prefix`).
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.LinuxHello

open Silmaril.Net Silmaril.Net.Http1 Silmaril.Parse.ByteParse Silmaril.Servers.Wire1
open Silmaril.Servers.Compare Silmaril.Servers.LinuxHello Silmaril.Servers.Platform
open Silmaril.Servers.WasiExamples

theorem responseHead_G_mono {k k' : Nat} (hk : k ≤ k') {l : List UInt8} {h : ResponseHead}
    (hg : (Grammar.responseHead k).G l h) : (Grammar.responseHead k').G l h := by
  obtain ⟨l₁, l₂, s, e, hs, fs, hfs, rfl⟩ := hg
  obtain ⟨hsec, hlen⟩ := Grammar.fields_G_iff.1 hfs
  exact ⟨l₁, l₂, s, e, hs, fs, Grammar.fields_G_iff.2 ⟨hsec, by omega⟩, rfl⟩

theorem seg_append (pre p : List UInt8) (j : Nat) :
    seg ⟨(pre ++ p).toArray⟩ pre.length j = p.take (j - pre.length) := by
  simp [seg, List.extract]

theorem hello_content_length : helloResp.content.length = 5 := by decide

theorem hello_valid : helloWire.1.Valid :=
  (helloWire_ok (meth := []) (by decide) (by decide)).1

theorem hello_bodyLength {meth : List UInt8} (h1 : meth ≠ methodHEAD)
    (h2 : meth ≠ methodCONNECT) :
    responseBodyLength meth helloWire.1.line.code helloWire.1.fields = .length 5 := by
  have hf := (helloWire_ok h1 h2).2
  generalize responseBodyLength meth helloWire.1.line.code helloWire.1.fields = L at hf ⊢
  cases L
  all_goals try exact hf.elim
  rename_i n
  have : helloWire.2 = .content helloResp.content := rfl
  rw [this] at hf
  have h5 := hello_content_length
  simp only [Body.Fits] at hf
  rw [← hf, h5]

/-- A response head read where the rest of the octets is a prefix of `helloWire`'s is
`helloWire`'s head, read whole. -/
theorem hello_head {pre p : List UInt8} (hp : p <+: encResponse helloWire.1 helloWire.2)
    {h' : ResponseHead} {j : Nat}
    (hh : (Grammar.responseHead ((⟨(pre ++ p).toArray⟩ : ByteArray).size + 1)).parse
      ⟨(pre ++ p).toArray⟩ (⟨(pre ++ p).toArray⟩ : ByteArray).size pre.length = .ok h' j) :
    h' = helloWire.1 ∧ j = pre.length + (encResponseHead helloWire.1).length := by
  have hE : encResponse helloWire.1 helloWire.2 =
      encResponseHead helloWire.1 ++ encBody helloWire.2 := rfl
  have hv := hello_valid
  have hsz : (⟨(pre ++ p).toArray⟩ : ByteArray).size = (pre ++ p).length := size_ofList _
  obtain ⟨hij, hjs, hg⟩ := (Grammar.responseHead _).sound (by rw [hsz]; simp) le_rfl hh
  rw [seg_append] at hg
  rw [hsz] at hjs
  simp only [List.length_append] at hjs
  have hl'len : (p.take (j - pre.length)).length = j - pre.length := by
    rw [List.length_take]; omega
  have hpre' : p.take (j - pre.length) <+: encResponseHead helloWire.1 ++ encBody helloWire.2 :=
    hE ▸ (List.take_prefix _ _).trans hp
  have hplen : p.length ≤ (encResponseHead helloWire.1 ++ encBody helloWire.2).length :=
    hE ▸ hp.length_le
  have hg' := responseHead_G_mono
    (k' := (pre ++ encResponseHead helloWire.1 ++ encBody helloWire.2).length + 1)
    (by rw [hsz]; simp only [List.length_append] at hplen ⊢; omega) hg
  obtain ⟨t, ht⟩ := hpre'
  have hc := (Grammar.responseHead _).complete hg'
    (bs := ⟨(pre ++ encResponseHead helloWire.1 ++ encBody helloWire.2).toArray⟩)
    (st := (pre ++ encResponseHead helloWire.1 ++ encBody helloWire.2).length)
    (i := pre.length)
    (by
      have := congrArg List.length ht
      simp only [List.length_append] at this ⊢
      omega)
    (by rw [size_ofList])
    (by
      rw [List.append_assoc, seg_append, ← ht]
      simp)
  have hr := responseHead_at hv pre (encBody helloWire.2)
  rw [hr] at hc
  simp only [Res.ok.injEq] at hc
  obtain ⟨rfl, hlen⟩ := hc
  rw [hl'len] at hlen
  exact ⟨rfl, by omega⟩

theorem encResponseHead_hello_pos : 0 < (encResponseHead helloWire.1).length := by
  simp only [encResponseHead, encStatusLine, List.length_append, List.length_cons]
  omega

/-- Nothing is read at the end of the octets after a prefix of `helloWire`'s. -/
theorem hello_end_err (meth pre : List UInt8) (x : WireResp) (k : Nat) :
    parseResponseAt meth ⟨(pre ++ []).toArray⟩ pre.length ≠ .ok x k := by
  intro h
  unfold parseResponseAt at h
  split at h
  · cases h
  · next h' j hh =>
    obtain ⟨-, hj⟩ := hello_head (List.nil_prefix) hh
    have hsz : (⟨(pre ++ []).toArray⟩ : ByteArray).size = pre.length := by
      rw [size_ofList]; simp
    have := (Grammar.responseHead _).sound (by rw [hsz]) le_rfl hh
    rw [hsz] at this
    have := encResponseHead_hello_pos
    omega

/-- **No strict prefix of `helloWire`'s octets frames as a response** to an answerable
request, after any octets. -/
theorem hello_prefix_err {meth : List UInt8} (h1 : meth ≠ methodHEAD)
    (h2 : meth ≠ methodCONNECT) (pre p : List UInt8)
    (hp : p <+: encResponse helloWire.1 helloWire.2)
    (hlt : p.length < (encResponse helloWire.1 helloWire.2).length) (x : WireResp) (k : Nat) :
    parseResponseAt meth ⟨(pre ++ p).toArray⟩ pre.length ≠ .ok x k := by
  intro h
  have hE : encResponse helloWire.1 helloWire.2 =
      encResponseHead helloWire.1 ++ encBody helloWire.2 := rfl
  have hsz : (⟨(pre ++ p).toArray⟩ : ByteArray).size = (pre ++ p).length := size_ofList _
  have hB : (encBody helloWire.2).length = 5 := hello_content_length
  unfold parseResponseAt at h
  split at h
  · cases h
  · next h' j hh =>
    obtain ⟨rfl, rfl⟩ := hello_head hp hh
    rw [hello_bodyLength h1 h2] at h
    simp only [parseBody] at h
    rw [ite_eq_right (by rw [hsz]; simp only [List.length_append, hE] at hlt ⊢; omega)] at h
    cases h

theorem encResponses_replicate_succ (n : Nat) :
    encResponses (List.replicate (n + 1) helloWire) =
      encResponse helloWire.1 helloWire.2 ++ encResponses (List.replicate n helloWire) := by
  simp [encResponses, List.replicate_succ]

theorem prefix_append_cases {α : Type} {a b p : List α} (h : p <+: a ++ b) :
    (p <+: a ∧ p.length < a.length) ∨ ∃ q, p = a ++ q ∧ q <+: b := by
  by_cases hl : p.length < a.length
  · exact .inl ⟨List.prefix_of_prefix_length_le h (List.prefix_append a b) hl.le, hl⟩
  · right
    have ha : a <+: p := List.prefix_of_prefix_length_le (List.prefix_append a b) h (by omega)
    obtain ⟨q, rfl⟩ := ha
    refine ⟨q, rfl, ?_⟩
    obtain ⟨t, ht⟩ := h
    exact ⟨t, by simpa using ht⟩

/-- **The responses framed from a prefix of `k` hello responses are hello responses**, when
the first `k` requests are answerable. -/
theorem parseResponses_hello : ∀ (k : Nat) (rs : List Net.Http.Request) (pre p : List UInt8),
    k ≤ (rs.takeWhile answerable).length → p <+: encResponses (List.replicate k helloWire) →
    ∀ x ∈ parseResponses ⟨(pre ++ p).toArray⟩ (rs.map fun r => r.method.toToken) pre.length,
      x = helloWire
  | _, [], _, _, _, _ => by simp [parseResponses]
  | 0, r :: rs, pre, p, _, hp => by
    have : p = [] := List.prefix_nil.1 (by simpa [encResponses] using hp)
    subst this
    intro x hx
    simp only [List.map_cons, parseResponses] at hx
    split at hx
    · next m k' hm => exact absurd hm (hello_end_err _ pre m k')
    · cases hx
  | k + 1, r :: rs, pre, p, hk, hp => by
    have hra : answerable r = true := by
      by_contra hn
      simp [hn] at hk
    have hk' : k ≤ (rs.takeWhile answerable).length := by
      simp [hra] at hk; omega
    simp only [answerable, Bool.and_eq_true, bne_iff_ne, ne_eq] at hra
    rw [encResponses_replicate_succ] at hp
    intro x hx
    simp only [List.map_cons, parseResponses] at hx
    rcases prefix_append_cases hp with ⟨hp1, hlt⟩ | ⟨q, rfl, hq⟩
    · split at hx
      · next m k' hm => exact absurd hm (hello_prefix_err hra.1 hra.2 pre p hp1 hlt m k')
      · cases hx
    · have hp := parseResponseAt_encode (method := r.method.toToken) (helloWire_ok hra.1 hra.2).1
        (helloWire_ok hra.1 hra.2).2 pre q
      rw [← List.append_assoc, hp] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · have ih := parseResponses_hello k rs (pre ++ encResponse helloWire.1 helloWire.2) q hk' hq
        rw [List.length_append] at ih
        exact ih x hx

/-- **A connection whose sent octets are a prefix of the hello responses its received octets
call for answers every exchange `helloResp`.** -/
theorem connLog_hello {tr : List SockEv} {c : ConnId}
    (h : sent c tr <+: helloOut (helloCount (received c tr))) :
    ∀ p ∈ connLog framing tr c, p.2 = helloResp := by
  intro p hp
  have hmem := (List.of_mem_zip hp).2
  simp only [framing, responses, List.mem_map] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  have := parseResponses_hello (helloCount (received c tr)) (requests (received c tr)) [] _
    le_rfl h x (by simpa using hx)
  rw [← hxe, this]
  exact toResponse_helloWire

end Silmaril.Proofs.Servers.LinuxHello
