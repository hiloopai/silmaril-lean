# Process raw evidence

Generated probe observations are pinned by
`examples/verification-projects/theorem-dev/lps-probes/SHA256SUMS` and the
Lean modules under `Silmaril/Process/LPS/Probes/Data`.  New generated evidence
belongs under this directory when it is not part of an upstream-compatible
namespace; proof modules should be the only imports of raw evidence.
