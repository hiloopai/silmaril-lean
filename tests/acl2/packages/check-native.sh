#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 ACL2_CHECKOUT NEW_RESULTS_DIRECTORY" >&2
  exit 2
fi

acl2_root=$(cd "$1" && pwd)
pin=bc6f4f49e81a0711214a8d91f0d06e0e084d2204
if [[ $(git -C "$acl2_root" rev-parse HEAD) != "$pin" || ! -x "$acl2_root/saved_acl2" ]]; then
  echo "Build saved_acl2 in an ACL2 checkout at $pin first." >&2
  exit 2
fi

fixtures=$(cd "$(dirname "$0")" && pwd)
mkdir "$2"
cd "$2"
cp "$fixtures"/{setup.lsp,package-home.lisp,package-use.lisp,observe.lsp,SHA256SUMS} .
sha256sum -c SHA256SUMS

export ACL2_CUSTOMIZATION=NONE
acl2="$acl2_root/saved_acl2"
"$acl2" >certify.log 2>&1 <<'LISP'
(ld "setup.lsp")
(certify-book "package-home" 3 nil)
(ubt! 1)
(include-book "package-home")
(certify-book "package-use" 1 nil)
(quit)
LISP
"$acl2" <observe.lsp >observe.log 2>&1

for log in certify.log observe.log; do
  if grep -Eq '^ACL2 (Error|!>Unhandled)|\*\*\*\*\*\*\*\* FAILED' "$log"; then
    cat "$log" >&2
    exit 1
  fi
done
test -s package-home.cert && test -s package-use.cert
grep -Fq 'ACL2 !> :PASSED' observe.log
grep -Fq 'ACL2 !> :SILMARIL-PACKAGE-CHECK-PASSED' observe.log

"$acl2" >reject.log 2>&1 <<'LISP'
(include-book "package-use")
:trans (silmaril-c2-other::|takeFirst| nil)
:trans (silmaril-c2-use::|takeFirst| nil nil)
(quit)
LISP
grep -Fq 'neither a function nor macro definition' reject.log
grep -Fq 'it is given 2 arguments' reject.log
echo "ACL2 8.7 certified both books, checked the translated bodies and result, and rejected both invalid calls."
