module

public import Silmaril.Net.Http1.Chunked.Defs
public import Silmaril.Net.Http1.Message.Thms

/-!
# The chunk-extension automaton accepts exactly the RFC 9112 §7.1.1 ABNF

`isChunkExt_iff_abnf : isChunkExt l = true ↔ ChunkExtAbnf l`.

* **Automaton ⇒ ABNF.** Each state `s` has a *residual* `Res s r`: what the rest `r` of the
  input must look like, given what the state has read, for the whole to be a `chunk-ext`.
  One lemma per state (`res_step_*`) shows that a transition preserves residuals backwards;
  accepting states accept the empty rest; so an accepted input has residual
  `Res .start l = ChunkExtAbnf l`.
* **ABNF ⇒ automaton.** Runs compose (`run_append`); from an accepting state, an item leads
  to an accepting state (`run_item`), passing through invariant sets of states for the
  whitespace, token and quoted-string runs (`run_stay`, `run_inv`).
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)

/-- Every octet is `SP` or `HTAB`. -/
abbrev AllWS (w : Bytes) : Prop := ∀ b ∈ w, isWS b = true

/-- What may follow a name: nothing more of this item, then further items; or a value. -/
inductive AfterName : Bytes → Prop where
  | none {y : Bytes} : ChunkExtAbnf y → AfterName y
  | token {w₃ w₄ v y : Bytes} : AllWS (w₃ ++ w₄) → IsToken v → ChunkExtAbnf y →
      AfterName (w₃ ++ [EQ] ++ w₄ ++ v ++ y)
  | quoted {w₃ w₄ q y : Bytes} : AllWS (w₃ ++ w₄) → QuotedBody q → ChunkExtAbnf y →
      AfterName (w₃ ++ [EQ] ++ w₄ ++ [DQUOTE] ++ q ++ [DQUOTE] ++ y)

/-- What may follow `"="` and its whitespace: a value, then further items. -/
def ValueThen (z : Bytes) : Prop :=
  (∃ v y, z = v ++ y ∧ IsToken v ∧ ChunkExtAbnf y) ∨
    (∃ q y, z = [DQUOTE] ++ q ++ [DQUOTE] ++ y ∧ QuotedBody q ∧ ChunkExtAbnf y)

/-- The residual of each state. -/
def ExtRes : ExtState → Bytes → Prop
  | .start, r | .closed, r => ChunkExtAbnf r
  | .semi, r => ∃ w n x, r = w ++ n ++ x ∧ AllWS w ∧ IsToken n ∧ AfterName x
  | .ws, r => ∃ w t, r = w ++ [SEMI] ++ t ∧ AllWS w ∧ ExtRes .semi t
  | .name, r => ∃ n x, r = n ++ x ∧ (∀ b ∈ n, isTchar b = true) ∧ AfterName x
  | .nameWs, r => ∃ w x, r = w ++ x ∧ AllWS w ∧
      ((∃ t, x = [EQ] ++ t ∧ ExtRes .eq t) ∨ (∃ t, x = [SEMI] ++ t ∧ ExtRes .semi t))
  | .eq, r => ∃ w z, r = w ++ z ∧ AllWS w ∧ ValueThen z
  | .token, r => ∃ v y, r = v ++ y ∧ (∀ b ∈ v, isTchar b = true) ∧ ChunkExtAbnf y
  | .quoted, r => ∃ q y, r = q ++ [DQUOTE] ++ y ∧ QuotedBody q ∧ ChunkExtAbnf y
  | .escape, r => ∃ c q y, r = c :: q ++ [DQUOTE] ++ y ∧ isFieldByte c = true ∧ QuotedBody q ∧
      ChunkExtAbnf y
termination_by s => match s with | .semi => 0 | .eq => 0 | .ws => 1 | .nameWs => 1 | _ => 2

/-! ## Assembling items -/

theorem allWS_nil : AllWS [] := fun _ hb => nomatch hb

theorem allWS_cons {c : UInt8} {w : Bytes} (hc : isWS c = true) (hw : AllWS w) : AllWS (c :: w) := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact hc
  · exact hw b hb

theorem allWS_append {w w' : Bytes} (hw : AllWS w) (hw' : AllWS w') : AllWS (w ++ w') := by
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · exact hw b hb
  · exact hw' b hb

/-- An item and the items after it. -/
theorem abnf_of_afterName {w₁ w₂ n x : Bytes} (h₁ : AllWS w₁) (h₂ : AllWS w₂) (hn : IsToken n)
    (hx : AfterName x) : ChunkExtAbnf (w₁ ++ [SEMI] ++ w₂ ++ n ++ x) := by
  cases hx with
  | none hy => exact .cons (.name h₁ h₂ hn) hy
  | @token w₃ w₄ v y hw hv hy =>
    have hall : AllWS (w₁ ++ w₂ ++ w₃ ++ w₄) := by
      have := allWS_append (allWS_append h₁ h₂) hw
      simpa [List.append_assoc] using this
    have h := ChunkExtAbnf.cons (ChunkExtItem.token hall hn hv) hy
    simpa [List.append_assoc] using h
  | @quoted w₃ w₄ q y hw hq hy =>
    have hall : AllWS (w₁ ++ w₂ ++ w₃ ++ w₄) := by
      have := allWS_append (allWS_append h₁ h₂) hw
      simpa [List.append_assoc] using this
    have h := ChunkExtAbnf.cons (ChunkExtItem.quoted hall hn hq) hy
    simpa [List.append_assoc] using h

theorem abnf_of_semi {w t : Bytes} (hw : AllWS w) (ht : ExtRes .semi t) :
    ChunkExtAbnf (w ++ [SEMI] ++ t) := by
  obtain ⟨w₂, n, x, rfl, h₂, hn, hx⟩ : ∃ w₂ n x, t = w₂ ++ n ++ x ∧ AllWS w₂ ∧ IsToken n ∧
      AfterName x := by
    rw [ExtRes] at ht; exact ht
  have h := abnf_of_afterName hw h₂ hn hx
  simpa [List.append_assoc] using h

/-! ## Residuals, state by state -/

section Unfold
variable {r : Bytes}
theorem res_start : ExtRes .start r ↔ ChunkExtAbnf r := by rw [ExtRes]
theorem res_closed : ExtRes .closed r ↔ ChunkExtAbnf r := by rw [ExtRes]
theorem res_semi : ExtRes .semi r ↔ ∃ w n x, r = w ++ n ++ x ∧ AllWS w ∧ IsToken n ∧ AfterName x := by
  rw [ExtRes]
theorem res_ws : ExtRes .ws r ↔ ∃ w t, r = w ++ [SEMI] ++ t ∧ AllWS w ∧ ExtRes .semi t := by
  rw [ExtRes]
theorem res_name : ExtRes .name r ↔ ∃ n x, r = n ++ x ∧ (∀ b ∈ n, isTchar b = true) ∧ AfterName x := by
  rw [ExtRes]
theorem res_nameWs : ExtRes .nameWs r ↔ ∃ w x, r = w ++ x ∧ AllWS w ∧
    ((∃ t, x = [EQ] ++ t ∧ ExtRes .eq t) ∨ (∃ t, x = [SEMI] ++ t ∧ ExtRes .semi t)) := by
  rw [ExtRes]
theorem res_eq : ExtRes .eq r ↔ ∃ w z, r = w ++ z ∧ AllWS w ∧ ValueThen z := by rw [ExtRes]
theorem res_token : ExtRes .token r ↔
    ∃ v y, r = v ++ y ∧ (∀ b ∈ v, isTchar b = true) ∧ ChunkExtAbnf y := by rw [ExtRes]
theorem res_quoted : ExtRes .quoted r ↔
    ∃ q y, r = q ++ [DQUOTE] ++ y ∧ QuotedBody q ∧ ChunkExtAbnf y := by rw [ExtRes]
theorem res_escape : ExtRes .escape r ↔ ∃ c q y, r = c :: q ++ [DQUOTE] ++ y ∧
    isFieldByte c = true ∧ QuotedBody q ∧ ChunkExtAbnf y := by rw [ExtRes]
end Unfold

theorem tchar_cons {c : UInt8} {n : Bytes} (hc : isTchar c = true) (hn : ∀ b ∈ n, isTchar b = true) :
    ∀ b ∈ c :: n, isTchar b = true := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact hc
  · exact hn b hb

/-- A name ended by `"="`: the value follows. -/
theorem afterName_of_eqRes {w₃ t : Bytes} (hw : AllWS w₃) (ht : ExtRes .eq t) :
    AfterName (w₃ ++ [EQ] ++ t) := by
  obtain ⟨w₄, z, rfl, hw₄, hz⟩ := res_eq.1 ht
  rcases hz with ⟨v, y, rfl, hv, hy⟩ | ⟨q, y, rfl, hq, hy⟩
  · have h := AfterName.token (w₃ := w₃) (allWS_append hw hw₄) hv hy
    simpa [List.append_assoc] using h
  · have h := AfterName.quoted (w₃ := w₃) (allWS_append hw hw₄) hq hy
    simpa [List.append_assoc] using h

/-- A name followed by whitespace. -/
theorem afterName_of_nameWs {c : UInt8} {r : Bytes} (hc : isWS c = true) (hr : ExtRes .nameWs r) :
    AfterName (c :: r) := by
  obtain ⟨w, x, rfl, hw, ⟨t, rfl, ht⟩ | ⟨t, rfl, ht⟩⟩ := res_nameWs.1 hr
  · have h := afterName_of_eqRes (allWS_cons hc hw) ht
    simpa [List.append_assoc] using h
  · have h := abnf_of_semi (allWS_cons hc hw) ht
    exact .none (by simpa [List.append_assoc] using h)

/-! ### Transitions, inverted -/

section Inversion
variable {c : UInt8} {s : ExtState}

theorem inv_startLike {s₀ : ExtState} (h₀ : s₀ = .start ∨ s₀ = .ws ∨ s₀ = .closed)
    (h : chunkExtStep s₀ c = some s) : (c = SEMI ∧ s = .semi) ∨ (isWS c = true ∧ s = .ws) := by
  rcases h₀ with rfl | rfl | rfl <;>
  · simp only [chunkExtStep] at h
    split_ifs at h <;> cases h <;> simp_all

theorem inv_token (h : chunkExtStep .token c = some s) : (isTchar c = true ∧ s = .token) ∨
    (c = SEMI ∧ s = .semi) ∨ (isWS c = true ∧ s = .ws) := by
  simp only [chunkExtStep] at h
  split_ifs at h <;> cases h <;> simp_all

theorem inv_semi (h : chunkExtStep .semi c = some s) :
    (isWS c = true ∧ s = .semi) ∨ (isTchar c = true ∧ s = .name) := by
  simp only [chunkExtStep] at h
  split_ifs at h <;> cases h <;> simp_all

theorem inv_name (h : chunkExtStep .name c = some s) : (isTchar c = true ∧ s = .name) ∨
    (isWS c = true ∧ s = .nameWs) ∨ (c = EQ ∧ s = .eq) ∨ (c = SEMI ∧ s = .semi) := by
  simp only [chunkExtStep] at h
  split_ifs at h <;> cases h <;> simp_all

theorem inv_nameWs (h : chunkExtStep .nameWs c = some s) :
    (isWS c = true ∧ s = .nameWs) ∨ (c = EQ ∧ s = .eq) ∨ (c = SEMI ∧ s = .semi) := by
  simp only [chunkExtStep] at h
  split_ifs at h <;> cases h <;> simp_all

theorem inv_eq (h : chunkExtStep .eq c = some s) : (isWS c = true ∧ s = .eq) ∨
    (isTchar c = true ∧ s = .token) ∨ (c = DQUOTE ∧ s = .quoted) := by
  simp only [chunkExtStep] at h
  split_ifs at h <;> cases h <;> simp_all

theorem inv_quoted (h : chunkExtStep .quoted c = some s) : (c = DQUOTE ∧ s = .closed) ∨
    (c = BSLASH ∧ s = .escape) ∨ (isQdtext c = true ∧ s = .quoted) := by
  simp only [chunkExtStep] at h
  split_ifs at h <;> cases h <;> simp_all

theorem inv_escape (h : chunkExtStep .escape c = some s) : isFieldByte c = true ∧ s = .quoted := by
  simp only [chunkExtStep] at h
  split_ifs at h with hc
  cases h
  exact ⟨hc, rfl⟩

end Inversion

/-! ### Each transition preserves residuals backwards -/

section Steps
variable {c : UInt8} {s : ExtState} {r : Bytes}

theorem res_step_startLike {s₀ : ExtState} (h₀ : s₀ = .start ∨ s₀ = .closed)
    (h : chunkExtStep s₀ c = some s) (hr : ExtRes s r) : ExtRes s₀ (c :: r) := by
  have hab : ChunkExtAbnf (c :: r) := by
    rcases inv_startLike (by rcases h₀ with rfl | rfl <;> simp) h with ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
    · simpa using abnf_of_semi (w := []) allWS_nil hr
    · obtain ⟨w, t, rfl, hw, ht⟩ := res_ws.1 hr
      simpa [List.append_assoc] using abnf_of_semi (allWS_cons hc hw) ht
  rcases h₀ with rfl | rfl
  · exact res_start.2 hab
  · exact res_closed.2 hab

theorem res_step_ws (h : chunkExtStep .ws c = some s) (hr : ExtRes s r) : ExtRes .ws (c :: r) := by
  rw [res_ws]
  rcases inv_startLike (by simp) h with ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
  · exact ⟨[], r, by simp, allWS_nil, hr⟩
  · obtain ⟨w, t, rfl, hw, ht⟩ := res_ws.1 hr
    exact ⟨c :: w, t, by simp, allWS_cons hc hw, ht⟩

theorem res_step_token (h : chunkExtStep .token c = some s) (hr : ExtRes s r) :
    ExtRes .token (c :: r) := by
  rw [res_token]
  rcases inv_token h with ⟨hc, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
  · obtain ⟨v, y, rfl, hv, hy⟩ := res_token.1 hr
    exact ⟨c :: v, y, by simp, tchar_cons hc hv, hy⟩
  · exact ⟨[], SEMI :: r, by simp, by simp, by simpa using abnf_of_semi (w := []) allWS_nil hr⟩
  · obtain ⟨w, t, rfl, hw, ht⟩ := res_ws.1 hr
    have hab : ChunkExtAbnf (c :: w ++ [SEMI] ++ t) := abnf_of_semi (allWS_cons hc hw) ht
    exact ⟨[], c :: (w ++ [SEMI] ++ t), by simp, by simp, by simpa using hab⟩

theorem res_step_semi (h : chunkExtStep .semi c = some s) (hr : ExtRes s r) :
    ExtRes .semi (c :: r) := by
  rw [res_semi]
  rcases inv_semi h with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · obtain ⟨w, n, x, rfl, hw, hn, hx⟩ := res_semi.1 hr
    exact ⟨c :: w, n, x, by simp, allWS_cons hc hw, hn, hx⟩
  · obtain ⟨n, x, rfl, hn, hx⟩ := res_name.1 hr
    exact ⟨[], c :: n, x, by simp, allWS_nil, ⟨by simp, tchar_cons hc hn⟩, hx⟩

theorem res_step_name (h : chunkExtStep .name c = some s) (hr : ExtRes s r) :
    ExtRes .name (c :: r) := by
  rw [res_name]
  rcases inv_name h with ⟨hc, rfl⟩ | ⟨hc, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨n, x, rfl, hn, hx⟩ := res_name.1 hr
    exact ⟨c :: n, x, by simp, tchar_cons hc hn, hx⟩
  · exact ⟨[], c :: r, by simp, by simp, afterName_of_nameWs hc hr⟩
  · exact ⟨[], EQ :: r, by simp, by simp, by simpa using afterName_of_eqRes (w₃ := []) allWS_nil hr⟩
  · exact ⟨[], SEMI :: r, by simp, by simp, .none (by simpa using abnf_of_semi (w := []) allWS_nil hr)⟩

theorem res_step_nameWs (h : chunkExtStep .nameWs c = some s) (hr : ExtRes s r) :
    ExtRes .nameWs (c :: r) := by
  rw [res_nameWs]
  rcases inv_nameWs h with ⟨hc, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨w, x, rfl, hw, hx⟩ := res_nameWs.1 hr
    exact ⟨c :: w, x, by simp, allWS_cons hc hw, hx⟩
  · exact ⟨[], EQ :: r, by simp, allWS_nil, .inl ⟨r, rfl, hr⟩⟩
  · exact ⟨[], SEMI :: r, by simp, allWS_nil, .inr ⟨r, rfl, hr⟩⟩

theorem res_step_eq (h : chunkExtStep .eq c = some s) (hr : ExtRes s r) : ExtRes .eq (c :: r) := by
  rw [res_eq]
  rcases inv_eq h with ⟨hc, rfl⟩ | ⟨hc, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨w, z, rfl, hw, hz⟩ := res_eq.1 hr
    exact ⟨c :: w, z, by simp, allWS_cons hc hw, hz⟩
  · obtain ⟨v, y, rfl, hv, hy⟩ := res_token.1 hr
    exact ⟨[], c :: (v ++ y), by simp, allWS_nil, .inl ⟨c :: v, y, by simp, ⟨by simp, tchar_cons hc hv⟩, hy⟩⟩
  · obtain ⟨q, y, rfl, hq, hy⟩ := res_quoted.1 hr
    exact ⟨[], DQUOTE :: (q ++ [DQUOTE] ++ y), by simp, allWS_nil, .inr ⟨q, y, by simp, hq, hy⟩⟩

theorem res_step_quoted (h : chunkExtStep .quoted c = some s) (hr : ExtRes s r) :
    ExtRes .quoted (c :: r) := by
  rw [res_quoted]
  rcases inv_quoted h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
  · exact ⟨[], r, by simp, .nil, res_closed.1 hr⟩
  · obtain ⟨c', q, y, rfl, hc', hq, hy⟩ := res_escape.1 hr
    exact ⟨BSLASH :: c' :: q, y, by simp, .pair hc' hq, hy⟩
  · obtain ⟨q, y, rfl, hq, hy⟩ := res_quoted.1 hr
    exact ⟨c :: q, y, by simp, .qdtext hc hq, hy⟩

theorem res_step_escape (h : chunkExtStep .escape c = some s) (hr : ExtRes s r) :
    ExtRes .escape (c :: r) := by
  obtain ⟨hc, rfl⟩ := inv_escape h
  obtain ⟨q, y, rfl, hq, hy⟩ := res_quoted.1 hr
  exact res_escape.2 ⟨c, q, y, by simp, hc, hq, hy⟩

theorem res_step : ∀ {s₀ : ExtState}, chunkExtStep s₀ c = some s → ExtRes s r → ExtRes s₀ (c :: r)
  | .start, h, hr => res_step_startLike (.inl rfl) h hr
  | .closed, h, hr => res_step_startLike (.inr rfl) h hr
  | .ws, h, hr => res_step_ws h hr
  | .token, h, hr => res_step_token h hr
  | .semi, h, hr => res_step_semi h hr
  | .name, h, hr => res_step_name h hr
  | .nameWs, h, hr => res_step_nameWs h hr
  | .eq, h, hr => res_step_eq h hr
  | .quoted, h, hr => res_step_quoted h hr
  | .escape, h, hr => res_step_escape h hr

end Steps

theorem res_nil : ∀ {s : ExtState}, s.accepting = true → ExtRes s []
  | .start, _ => res_start.2 .nil
  | .closed, _ => res_closed.2 .nil
  | .name, _ => res_name.2 ⟨[], [], rfl, by simp, .none .nil⟩
  | .token, _ => res_token.2 ⟨[], [], rfl, by simp, .nil⟩
  | .ws, h | .semi, h | .nameWs, h | .eq, h | .quoted, h | .escape, h => by
    simp [ExtState.accepting] at h

theorem res_of_run : ∀ (r : Bytes) {s s' : ExtState}, chunkExtRun s r = some s' →
    s'.accepting = true → ExtRes s r
  | [], _, _, h, ha => by
    cases h; exact res_nil ha
  | c :: r, s, s', h, ha => by
    obtain ⟨s'', hs, hr⟩ : ∃ s'', chunkExtStep s c = some s'' ∧ chunkExtRun s'' r = some s' := by
      simpa [chunkExtRun, Option.bind_eq_some_iff] using h
    exact res_step hs (res_of_run r hr ha)

/-- Automaton ⇒ ABNF. -/
theorem abnf_of_isChunkExt {l : Bytes} (h : isChunkExt l = true) : ChunkExtAbnf l := by
  have hrun : (chunkExtRun .start l).map ExtState.accepting = some true := by
    simp only [isChunkExt, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  obtain ⟨s', hs', ha⟩ : ∃ s', chunkExtRun .start l = some s' ∧ s'.accepting = true := by
    simpa [Option.map_eq_some_iff] using hrun
  exact res_start.1 (res_of_run l hs' ha)

/-! ## ABNF ⇒ automaton -/

theorem run_append : ∀ (s : ExtState) (a b : Bytes),
    chunkExtRun s (a ++ b) = (chunkExtRun s a).bind fun s' => chunkExtRun s' b
  | _, [], _ => rfl
  | s, c :: a, b => by
    simp only [List.cons_append, chunkExtRun]
    cases chunkExtStep s c with
    | none => rfl
    | some s' => exact run_append s' a b

/-- A run of octets of class `P` keeps the automaton inside the set `S`. -/
theorem run_inv {S : ExtState → Prop} {P : UInt8 → Prop}
    (hstep : ∀ s c, S s → P c → ∃ s', S s' ∧ chunkExtStep s c = some s') :
    ∀ {s : ExtState} (w rest : Bytes), S s → (∀ c ∈ w, P c) →
      ∃ s', S s' ∧ chunkExtRun s (w ++ rest) = chunkExtRun s' rest
  | s, [], _, hs, _ => ⟨s, hs, rfl⟩
  | s, c :: w, rest, hs, hw => by
    obtain ⟨s', hs', hst⟩ := hstep s c hs (hw c (by simp))
    obtain ⟨s'', hs'', e⟩ := run_inv hstep w rest hs' (fun b hb => hw b (by simp [hb]))
    exact ⟨s'', hs'', by simp only [List.cons_append, chunkExtRun, hst, Option.bind_some, e]⟩

/-- A run of octets of class `P` that `s` loops on. -/
theorem run_stay {s : ExtState} {P : UInt8 → Prop} (hstep : ∀ c, P c → chunkExtStep s c = some s)
    (w rest : Bytes) (hw : ∀ c ∈ w, P c) : chunkExtRun s (w ++ rest) = chunkExtRun s rest := by
  obtain ⟨s', rfl, e⟩ := run_inv (S := (· = s)) (fun _ c hs hc => ⟨s, rfl, hs ▸ hstep c hc⟩)
    w rest rfl hw
  exact e

/-- States from which `BWS ";"` starts an item. -/
def PreSemi (s : ExtState) : Prop :=
  s = .start ∨ s = .ws ∨ s = .name ∨ s = .nameWs ∨ s = .token ∨ s = .closed

theorem step_ws_facts : ∀ c : UInt8, isWS c = true →
    chunkExtStep .start c = some .ws ∧ chunkExtStep .ws c = some .ws ∧
    chunkExtStep .name c = some .nameWs ∧ chunkExtStep .nameWs c = some .nameWs ∧
    chunkExtStep .token c = some .ws ∧ chunkExtStep .closed c = some .ws ∧
    chunkExtStep .semi c = some .semi ∧ chunkExtStep .eq c = some .eq := by decide

theorem step_tchar_facts : ∀ c : UInt8, isTchar c = true →
    chunkExtStep .semi c = some .name ∧ chunkExtStep .name c = some .name ∧
    chunkExtStep .eq c = some .token ∧ chunkExtStep .token c = some .token := by decide

theorem step_quoted_facts : (∀ c : UInt8, isQdtext c = true → chunkExtStep .quoted c = some .quoted) ∧
    (∀ c : UInt8, isFieldByte c = true → chunkExtStep .escape c = some .quoted) := by decide

theorem preSemi_ws {s : ExtState} {c : UInt8} (hs : PreSemi s) (hc : isWS c = true) :
    ∃ s', PreSemi s' ∧ chunkExtStep s c = some s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := step_ws_facts c hc
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [PreSemi], h1⟩
  · exact ⟨_, by simp [PreSemi], h2⟩
  · exact ⟨_, by simp [PreSemi], h3⟩
  · exact ⟨_, by simp [PreSemi], h4⟩
  · exact ⟨_, by simp [PreSemi], h5⟩
  · exact ⟨_, by simp [PreSemi], h6⟩

theorem preSemi_semi {s : ExtState} (hs : PreSemi s) : chunkExtStep s SEMI = some .semi := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `BWS ";"` from a state where an item may start. -/
theorem run_bws_semi {s : ExtState} (hs : PreSemi s) {w : Bytes} (hw : AllWS w) (rest : Bytes) :
    chunkExtRun s (w ++ SEMI :: rest) = chunkExtRun .semi rest := by
  obtain ⟨s', hs', e⟩ := run_inv (fun _ _ hs hc => preSemi_ws hs hc) w (SEMI :: rest) hs hw
  rw [e]
  simp only [chunkExtRun, preSemi_semi hs', Option.bind_some]

/-- `BWS "="` after a name. -/
theorem run_bws_eq {w : Bytes} (hw : AllWS w) (rest : Bytes) :
    chunkExtRun .name (w ++ EQ :: rest) = chunkExtRun .eq rest := by
  obtain ⟨s', hs', e⟩ := run_inv (S := fun s => s = .name ∨ s = .nameWs)
    (fun s c hs hc => by
      obtain ⟨-, -, h3, h4, -⟩ := step_ws_facts c hc
      rcases hs with rfl | rfl
      · exact ⟨_, .inr rfl, h3⟩
      · exact ⟨_, .inr rfl, h4⟩) w (EQ :: rest) (.inl rfl) hw
  rw [e]
  rcases hs' with rfl | rfl <;> rfl

theorem run_token {s₀ s : ExtState} (h₀ : ∀ c, isTchar c = true → chunkExtStep s₀ c = some s)
    (hs : ∀ c, isTchar c = true → chunkExtStep s c = some s) {n : Bytes} (hn : IsToken n)
    (rest : Bytes) : chunkExtRun s₀ (n ++ rest) = chunkExtRun s rest := by
  obtain ⟨c, n', rfl⟩ := List.exists_cons_of_ne_nil hn.1
  have hc : isTchar c = true := hn.2 c (by simp)
  simp only [List.cons_append, chunkExtRun, h₀ c hc, Option.bind_some]
  exact run_stay hs n' rest fun b hb => hn.2 b (by simp [hb])

theorem run_quotedBody {q : Bytes} (hq : QuotedBody q) (rest : Bytes) :
    chunkExtRun .quoted (q ++ rest) = chunkExtRun .quoted rest := by
  induction hq with
  | nil => rfl
  | @qdtext c q hc _ ih =>
    simp only [List.cons_append, chunkExtRun, step_quoted_facts.1 c hc, Option.bind_some, ih]
  | @pair c q hc _ ih =>
    have hb : chunkExtStep .quoted BSLASH = some .escape := rfl
    simp only [List.cons_append, chunkExtRun, hb, step_quoted_facts.2 c hc, Option.bind_some, ih]

theorem allWS_left {w w' : Bytes} (h : AllWS (w ++ w')) : AllWS w := fun b hb => h b (by simp [hb])
theorem allWS_right {w w' : Bytes} (h : AllWS (w ++ w')) : AllWS w' := fun b hb => h b (by simp [hb])

/-- The value after `"="`. -/
theorem run_eq_value {w : Bytes} (hw : AllWS w) {v : Bytes} (hv : IsToken v) (rest : Bytes) :
    chunkExtRun .eq (w ++ (v ++ rest)) = chunkExtRun .token rest := by
  rw [run_stay (fun c hc => (step_ws_facts c hc).2.2.2.2.2.2.2) w _ hw]
  exact run_token (fun c hc => (step_tchar_facts c hc).2.2.1)
    (fun c hc => (step_tchar_facts c hc).2.2.2) hv rest

theorem run_eq_quoted {w : Bytes} (hw : AllWS w) {q : Bytes} (hq : QuotedBody q) (rest : Bytes) :
    chunkExtRun .eq (w ++ DQUOTE :: (q ++ DQUOTE :: rest)) = chunkExtRun .closed rest := by
  rw [run_stay (fun c hc => (step_ws_facts c hc).2.2.2.2.2.2.2) w _ hw]
  have h1 : chunkExtStep .eq DQUOTE = some .quoted := rfl
  have h2 : chunkExtStep .quoted DQUOTE = some .closed := rfl
  simp only [chunkExtRun, h1, Option.bind_some, run_quotedBody hq, h2]

/-- After `BWS ";" BWS name`. -/
theorem run_item_head {s : ExtState} (hs : PreSemi s) {w₁ w₂ n : Bytes} (h₁ : AllWS w₁)
    (h₂ : AllWS w₂) (hn : IsToken n) (rest : Bytes) :
    chunkExtRun s (w₁ ++ SEMI :: (w₂ ++ (n ++ rest))) = chunkExtRun .name rest := by
  rw [run_bws_semi hs h₁, run_stay (fun c hc => (step_ws_facts c hc).2.2.2.2.2.2.1) w₂ _ h₂]
  exact run_token (fun c hc => (step_tchar_facts c hc).1) (fun c hc => (step_tchar_facts c hc).2.1)
    hn rest

theorem accepting_preSemi {s : ExtState} (h : s.accepting = true) : PreSemi s := by
  cases s <;> simp_all [ExtState.accepting, PreSemi]

/-- From an accepting state, an item leads to an accepting state. -/
theorem run_item {i : Bytes} (hi : ChunkExtItem i) {s : ExtState} (hs : s.accepting = true) :
    ∃ s', s'.accepting = true ∧ ∀ rest, chunkExtRun s (i ++ rest) = chunkExtRun s' rest := by
  have hp := accepting_preSemi hs
  cases hi with
  | name h₁ h₂ hn => exact ⟨.name, rfl, fun rest => by
      simpa [List.append_assoc] using run_item_head hp h₁ h₂ hn rest⟩
  | @token w₁ w₂ n w₃ w₄ v hw hn hv => exact ⟨.token, rfl, fun rest => by
      have h := run_item_head hp (allWS_left (allWS_left (allWS_left hw)))
        (allWS_right (allWS_left (allWS_left hw))) hn (w₃ ++ EQ :: (w₄ ++ (v ++ rest)))
      have e : w₁ ++ [SEMI] ++ w₂ ++ n ++ w₃ ++ [EQ] ++ w₄ ++ v ++ rest =
          w₁ ++ SEMI :: (w₂ ++ (n ++ (w₃ ++ EQ :: (w₄ ++ (v ++ rest))))) := by simp
      rw [e, h, run_bws_eq (allWS_right (allWS_left hw)), run_eq_value (allWS_right hw) hv]⟩
  | @quoted w₁ w₂ n w₃ w₄ q hw hn hq => exact ⟨.closed, rfl, fun rest => by
      have h := run_item_head hp (allWS_left (allWS_left (allWS_left hw)))
        (allWS_right (allWS_left (allWS_left hw))) hn
        (w₃ ++ EQ :: (w₄ ++ DQUOTE :: (q ++ DQUOTE :: rest)))
      have e : w₁ ++ [SEMI] ++ w₂ ++ n ++ w₃ ++ [EQ] ++ w₄ ++ [DQUOTE] ++ q ++ [DQUOTE] ++ rest =
          w₁ ++ SEMI :: (w₂ ++ (n ++ (w₃ ++ EQ :: (w₄ ++ DQUOTE :: (q ++ DQUOTE :: rest))))) := by
        simp
      rw [e, h, run_bws_eq (allWS_right (allWS_left hw)), run_eq_quoted (allWS_right hw) hq]⟩

theorem run_abnf {l : Bytes} (hl : ChunkExtAbnf l) :
    ∀ {s : ExtState}, s.accepting = true → ∃ s', s'.accepting = true ∧ chunkExtRun s l = some s' := by
  induction hl with
  | nil => exact fun hs => ⟨_, hs, rfl⟩
  | cons hi _ ih =>
    intro s hs
    obtain ⟨s', hs', e⟩ := run_item hi hs
    rw [e]
    exact ih hs'

theorem fb_ws : ∀ c : UInt8, isWS c = true → isFieldByte c = true := by decide
theorem fb_qd : ∀ c : UInt8, isQdtext c = true → isFieldByte c = true := by decide

theorem quotedBody_fb {q : Bytes} (hq : QuotedBody q) : ∀ b ∈ q, isFieldByte b = true := by
  induction hq with
  | nil => simp
  | qdtext hc _ ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact fb_qd _ hc
    · exact ih b hb
  | pair hc _ ih =>
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · rfl
    · exact hc
    · exact ih b hb

theorem fb_tok {n : Bytes} (hn : IsToken n) : ∀ b ∈ n, isFieldByte b = true :=
  fun b h => isFieldByte_of_tchar b (hn.2 b h)

theorem fb_allWS {w : Bytes} (hw : AllWS w) : ∀ b ∈ w, isFieldByte b = true :=
  fun b h => fb_ws b (hw b h)

theorem fb_append {x y : Bytes} (hx : ∀ b ∈ x, isFieldByte b = true)
    (hy : ∀ b ∈ y, isFieldByte b = true) : ∀ b ∈ x ++ y, isFieldByte b = true := by
  intro b hb
  rcases List.mem_append.1 hb with h | h
  · exact hx b h
  · exact hy b h

theorem fb_lit {c : UInt8} (hc : isFieldByte c = true) : ∀ b ∈ [c], isFieldByte b = true := by
  intro b hb
  rw [List.mem_singleton.1 hb]; exact hc

theorem item_fb {i : Bytes} (hi : ChunkExtItem i) : ∀ b ∈ i, isFieldByte b = true := by
  cases hi with
  | name h₁ h₂ hn =>
    exact fb_append (fb_append (fb_append (fb_allWS h₁) (fb_lit rfl)) (fb_allWS h₂)) (fb_tok hn)
  | token hw hn hv =>
    have hws := fb_allWS hw
    exact fb_append (fb_append (fb_append (fb_append (fb_append (fb_append (fb_append
      (fun b h => hws b (by simp [h])) (fb_lit rfl)) (fun b h => hws b (by simp [h])))
      (fb_tok hn)) (fun b h => hws b (by simp [h]))) (fb_lit rfl))
      (fun b h => hws b (by simp [h]))) (fb_tok hv)
  | quoted hw hn hq =>
    have hws := fb_allWS hw
    exact fb_append (fb_append (fb_append (fb_append (fb_append (fb_append (fb_append
      (fb_append (fb_append (fun b h => hws b (by simp [h])) (fb_lit rfl))
      (fun b h => hws b (by simp [h]))) (fb_tok hn)) (fun b h => hws b (by simp [h])))
      (fb_lit rfl)) (fun b h => hws b (by simp [h]))) (fb_lit rfl)) (quotedBody_fb hq))
      (fb_lit rfl)

theorem abnf_fb {l : Bytes} (hl : ChunkExtAbnf l) : ∀ b ∈ l, isFieldByte b = true := by
  induction hl with
  | nil => simp
  | cons hi _ ih =>
    intro b hb
    rcases List.mem_append.1 hb with h | h
    · exact item_fb hi b h
    · exact ih b h

theorem head_ws_semi {w : Bytes} (hw : AllWS w) (x : Bytes) :
    ∃ c t, w ++ [SEMI] ++ x = c :: t ∧ (c == SEMI || isWS c) = true := by
  cases w with
  | nil => exact ⟨SEMI, x, rfl, rfl⟩
  | cons c w => exact ⟨c, _, rfl, by simp [hw c (by simp)]⟩

theorem item_head {i : Bytes} (hi : ChunkExtItem i) :
    ∃ c t, i = c :: t ∧ (c == SEMI || isWS c) = true := by
  cases hi with
  | name h₁ _ _ => simpa [List.append_assoc] using head_ws_semi h₁ _
  | token hw _ _ => simpa [List.append_assoc] using head_ws_semi (allWS_left (allWS_left (allWS_left hw))) _
  | quoted hw _ _ =>
    simpa [List.append_assoc] using head_ws_semi (allWS_left (allWS_left (allWS_left hw))) _

theorem abnf_head {l : Bytes} (hl : ChunkExtAbnf l) :
    (l.head?.all fun c => c == SEMI || isWS c) = true := by
  cases hl with
  | nil => rfl
  | cons hi _ =>
    obtain ⟨c, t, rfl, hc⟩ := item_head hi
    simpa using hc

/-- ABNF ⇒ automaton. -/
theorem isChunkExt_of_abnf {l : Bytes} (hl : ChunkExtAbnf l) : isChunkExt l = true := by
  obtain ⟨s', hs', e⟩ := run_abnf hl (s := .start) rfl
  have hfb : l.all isFieldByte = true := List.all_eq_true.2 (abnf_fb hl)
  simp only [isChunkExt, hfb, abnf_head hl, e, Option.map_some, hs', Bool.true_and]
  rfl

/-- The chunk-extension automaton accepts exactly RFC 9112 §7.1.1's `chunk-ext`. -/
theorem isChunkExt_iff_abnf (l : Bytes) : isChunkExt l = true ↔ ChunkExtAbnf l :=
  ⟨abnf_of_isChunkExt, isChunkExt_of_abnf⟩

end Silmaril.Net.Http1
