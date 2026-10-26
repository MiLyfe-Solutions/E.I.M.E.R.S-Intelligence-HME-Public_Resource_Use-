import FiniteStepDescent.FiniteStepDescent

namespace FiniteStepDescent

/-!
This is only the terminal arithmetic implication represented by V185's
documented bound. It does not formalize V185's valuation-word, residue
partition, or tail-valuation premises.

The Library V185 package `EIMERS_Collatz_V185_Uniform_Tail_Descent.zip`
(SHA-256 d59d631ffdd77349f836cec3630fee327d32769426f9a711912e571c930fdc6e)
contains Python `prove.py` and README text, and explicitly records
`lean_compiled: false`; the original package is not modified here.
-/

/--
V185-shaped endpoint implication. For its reported constants, instantiate
`scale = 2^37`, `slope = 3^23`, and
`offset = 3 * 60899841373 + 2^29`.

Given the V185-style affine upper bound and a strict margin at `n`, this
proves the endpoint is below `n`. The premises must be established separately
for each claimed input family.
-/
theorem v185_shaped_endpoint_descent
    {n endpoint : Nat}
    (hbound : (2 ^ 37) * endpoint ≤ (3 ^ 23) * n + (3 * 60899841373 + 2 ^ 29))
    (hmargin : (3 ^ 23) * n + (3 * 60899841373 + 2 ^ 29) < (2 ^ 37) * n) :
    endpoint < n := by
  exact strict_descent_from_affine_bound hbound hmargin

end FiniteStepDescent
