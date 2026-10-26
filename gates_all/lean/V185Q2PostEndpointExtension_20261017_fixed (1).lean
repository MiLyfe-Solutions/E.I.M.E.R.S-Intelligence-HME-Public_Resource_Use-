import V185PostEndpointExtension

/-!
Corrected Lean extension for the V185 q = 2 (mod 2^22) subfamily.
The earlier candidate had a proof-composition type mismatch. This version
rewrites the V185 endpoint equality before composing the two descent facts.
-/

namespace EimersV185Q2Extension

open EimersV185Bridge EimersV185Full EimersV185Extension

def q2Param (t : Nat) : Nat := 2 + 4194304 * t
def q2Endpoint (t : Nat) : Nat := 226552135225 + 394865111526801408 * t
def q2Next (t : Nat) : Nat := 169914101419 + 296148833645101056 * t

theorem q2Endpoint_odd (t : Nat) : q2Endpoint t % 2 = 1 := by
  simp only [q2Endpoint]
  omega

theorem q2Next_odd (t : Nat) : q2Next t % 2 = 1 := by
  simp only [q2Next]
  omega

theorem q2_endpoint_eq (t : Nat) :
    iterateA 23 (start (q2Param t)) = q2Endpoint t := by
  change acceleratedTest (iterateA 22 (start (q2Param t))) = q2Endpoint t
  rw [iter22 (q2Param t)]
  have hform :
      38265777571 + q2Param t * 94143178827 = q2Endpoint t := by
    simp only [q2Param, q2Endpoint]
    ring
  have htail := tail_divisible (q2Param t)
  have hstep :
      3 * state22 (q2Param t) + 1 = 2 ^ 8 * q2Endpoint t := by
    rw [htail, hform]
    norm_num
  exact exact_accelerated_step (state22 (q2Param t)) (q2Endpoint t) 8
    hstep (q2Endpoint_odd t)

theorem q2_step (t : Nat) :
    3 * q2Endpoint t + 1 = 2 ^ 2 * q2Next t := by
  simp only [q2Endpoint, q2Next]
  ring

theorem q2_iter1 (t : Nat) :
    iterateA 1 (q2Endpoint t) = q2Next t := by
  change acceleratedTest (q2Endpoint t) = q2Next t
  exact exact_accelerated_step (q2Endpoint t) (q2Next t) 2
    (q2_step t) (q2Next_odd t)

theorem q2_post_step_descent (t : Nat) :
    iterateA 1 (q2Endpoint t) < q2Endpoint t := by
  rw [q2_iter1 t]
  simp only [q2Next, q2Endpoint]
  omega

theorem v185_q2_24_descent (t : Nat) :
    iterateA 24 (start (q2Param t)) < start (q2Param t) := by
  have hcomp := iterateA_comp 23 1 (start (q2Param t))
  have h24 :
      iterateA 24 (start (q2Param t)) =
        iterateA 1 (iterateA 23 (start (q2Param t))) := by
    simpa using hcomp
  rw [h24, q2_endpoint_eq t]
  have hV185 : q2Endpoint t < start (q2Param t) := by
    rw [← q2_endpoint_eq t]
    exact V185_finite_descent (q2Param t)
  exact lt_trans (q2_post_step_descent t) hV185

end EimersV185Q2Extension

#print EimersV185Q2Extension.v185_q2_24_descent
#print axioms EimersV185Q2Extension.v185_q2_24_descent
