module

public import Silmaril.Net.Qpack.Static.Defs

@[expose] public section

/-!
# QPACK static table: checks

CHECKED by kernel evaluation (`decide +kernel`): the table has 99 entries (Appendix A), and
several indices hold the entries of Table 4, including the first and the last; index 99 is
invalid (§3.1).
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (Entry Entry.ofStrings)

example : staticTable.length = staticLength := by decide +kernel
example : staticLookup 0 = some (Entry.ofStrings ":authority" "") := by decide +kernel
example : staticLookup 1 = some (Entry.ofStrings ":path" "/") := by decide +kernel
example : staticLookup 17 = some (Entry.ofStrings ":method" "GET") := by decide +kernel
example : staticLookup 25 = some (Entry.ofStrings ":status" "200") := by decide +kernel
example : staticLookup 31 = some (Entry.ofStrings "accept-encoding" "gzip, deflate, br") := by
  decide +kernel
example : staticLookup 52 = some (Entry.ofStrings "content-type" "text/html; charset=utf-8") := by
  decide +kernel
example : staticLookup 58 = some (Entry.ofStrings "strict-transport-security"
    "max-age=31536000; includesubdomains; preload") := by decide +kernel
example : staticLookup 85 = some (Entry.ofStrings "content-security-policy"
    "script-src 'none'; object-src 'none'; base-uri 'none'") := by decide +kernel
example : staticLookup 98 = some (Entry.ofStrings "x-frame-options" "sameorigin") := by
  decide +kernel
example : staticLookup 99 = none := by decide +kernel

end Silmaril.Net.Qpack
