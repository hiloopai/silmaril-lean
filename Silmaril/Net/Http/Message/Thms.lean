module

public import Silmaril.Net.Http.Message.Defs
public import Silmaril.Net.Http.Method.Thms
public import Silmaril.Net.Http.Status.Thms

@[expose] public section

/-!
# HTTP messages: theorems

PROVED (standard axioms):

* `stripContent_stripContent`, `stripContent_control`, `stripContent_headers`;
* `Response.isValid_stripContent`: stripping content (and trailers) keeps a response valid.
-/

namespace Silmaril.Net.Http

open Silmaril.Net.Http.Field

namespace Message

variable {C : Type}

@[simp] theorem stripContent_stripContent (m : Message C) :
    m.stripContent.stripContent = m.stripContent := rfl

@[simp] theorem stripContent_control (m : Message C) : m.stripContent.control = m.control := rfl

@[simp] theorem stripContent_headers (m : Message C) : m.stripContent.headers = m.headers := rfl

end Message

theorem Response.isValid_stripContent {r : Response} (h : r.isValid = true) :
    Response.isValid r.stripContent = true := by
  simp only [Response.isValid, Message.fieldsValid, Bool.and_eq_true] at h
  have hs : Status.isValid r.control = true := h.1.1
  have hh : r.headers.all Line.isValid = true := h.1.2.1
  simp only [Response.isValid, Message.fieldsValid, Message.stripContent, Response.status, hs,
    Section.isValid, List.all_nil, List.isEmpty_nil, Bool.or_true, hh,
    Bool.and_true]

end Silmaril.Net.Http
