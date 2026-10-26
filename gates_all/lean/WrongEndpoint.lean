import Child24Proof
open CollatzResearch EimersChild24
theorem rejected_wrong_endpoint (u : Nat) :
  ordinaryRun 133 (4835732101496250010959899 + u * 2^83) =
  2153706800091972785348136 + 4307387926151115532621494 * u := by
  exact child_q8388658_exact_endpoint u
