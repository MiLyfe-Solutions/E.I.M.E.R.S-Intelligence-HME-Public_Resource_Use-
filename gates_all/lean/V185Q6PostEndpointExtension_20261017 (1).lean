import V185PostEndpointExtension

/-!
Lean candidate for the V185 q = 6 (mod 2^22) subfamily.
This candidate has not been compiled in Lean yet.
-/

namespace EimersV185Q6Extension

open EimersV185Bridge EimersV185Full EimersV185Extension

def q6Param (t : Nat) : Nat := 6 + 4194304 * t
def q6Endpoint (t : Nat) : Nat := 603124850533 + 394865111526801408 * t
def q6Next (t : Nat) : Nat := 113085909475 + 74037208411275264 * t

theorem q6Endpoint_odd (t : Nat) : q6Endpoint t % 2 = 1 := by
  simp only [q6Endpoint]
  omega

theorem q6Next_odd (t : Nat) : q6Next t % 2 = 1 := by
  simp only [q6Next]
  omega

theorem q6_endpoint_eq (t : Nat) :
    iterateA 23 (start (q6Param t)) = q6Endpoint t := by
  change acceleratedTest (iterateA 22 (start (q6Param t))) = q6Endpoint t
  rw [iter22 (q6Param t)]
  have hform :
      38265777571 + q6Param t * 94143178827 = q6Endpoint t := by
    simp only [q6Param, q6Endpoint]
    ring
  have htail := tail_divisible (q6Param t)
  have hstep :
      3 * state22 (q6Param t) + 1 = 2 ^ 8 * q6Endpoint t := by
    rw [htail, hform]
    norm_num
  exact exact_accelerated_step (state22 (q6Param t)) (q6Endpoint t) 8
    hstep (q6Endpoint_odd t)

theorem q6_step (t : Nat) :
    3 * q6Endpoint t + 1 = 2 ^ 4 * q6Next t := by
  simp only [q6Endpoint, q6Next]
  ring

theorem q6_iter1 (t : Nat) :
    iterateA 1 (q6Endpoint t) = q6Next t := by
  change acceleratedTest (q6Endpoint t) = q6Next t
  exact exact_accelerated_step (q6Endpoint t) (q6Next t) 4
    (q6_step t) (q6Next_odd t)

theorem q6_post_step_descent (t : Nat) :
    iterateA 1 (q6Endpoint t) < q6Endpoint t := by
  rw [q6_iter1 t]
  simp only [q6Next, q6Endpoint]
  omega

theorem v185_q6_24_descent (t : Nat) :
    iterateA 24 (start (q6Param t)) < start (q6Param t) := by
  have hcomp := iterateA_comp 23 1 (start (q6Param t))
  have h24 :
      iterateA 24 (start (q6Param t)) =
        iterateA 1 (iterateA 23 (start (q6Param t))) := by
    simpa using hcomp
  rw [h24, q6_endpoint_eq t]
  have hV185 : q6Endpoint t < start (q6Param t) := by
    rw [← q6_endpoint_eq t]
    exact V185_finite_descent (q6Param t)
  exact lt_trans (q6_post_step_descent t) hV185

end EimersV185Q6Extension

#print EimersV185Q6Extension.v185_q6_24_descent
#print axioms EimersV185Q6Extension.v185_q6_24_descent
