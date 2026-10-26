import V185PostEndpointExtension

/-!
Lean candidate for the V185 q = 10 (mod 2^22) subfamily.
This candidate has not been compiled in Lean yet.
-/

namespace EimersV185Q10Extension

open EimersV185Bridge EimersV185Full EimersV185Extension

def q10Param (t : Nat) : Nat := 10 + 4194304 * t
def q10Endpoint (t : Nat) : Nat := 979697565841 + 394865111526801408 * t
def q10Next (t : Nat) : Nat := 734773174381 + 296148833645101056 * t

theorem q10Endpoint_odd (t : Nat) : q10Endpoint t % 2 = 1 := by
  simp only [q10Endpoint]
  omega

theorem q10Next_odd (t : Nat) : q10Next t % 2 = 1 := by
  simp only [q10Next]
  omega

theorem q10_endpoint_eq (t : Nat) :
    iterateA 23 (start (q10Param t)) = q10Endpoint t := by
  change acceleratedTest (iterateA 22 (start (q10Param t))) = q10Endpoint t
  rw [iter22 (q10Param t)]
  have hform :
      38265777571 + q10Param t * 94143178827 = q10Endpoint t := by
    simp only [q10Param, q10Endpoint]
    ring
  have htail := tail_divisible (q10Param t)
  have hstep :
      3 * state22 (q10Param t) + 1 = 2 ^ 8 * q10Endpoint t := by
    rw [htail, hform]
    norm_num
  exact exact_accelerated_step (state22 (q10Param t)) (q10Endpoint t) 8
    hstep (q10Endpoint_odd t)

theorem q10_step (t : Nat) :
    3 * q10Endpoint t + 1 = 2 ^ 2 * q10Next t := by
  simp only [q10Endpoint, q10Next]
  ring

theorem q10_iter1 (t : Nat) :
    iterateA 1 (q10Endpoint t) = q10Next t := by
  change acceleratedTest (q10Endpoint t) = q10Next t
  exact exact_accelerated_step (q10Endpoint t) (q10Next t) 2
    (q10_step t) (q10Next_odd t)

theorem q10_post_step_descent (t : Nat) :
    iterateA 1 (q10Endpoint t) < q10Endpoint t := by
  rw [q10_iter1 t]
  simp only [q10Next, q10Endpoint]
  omega

theorem v185_q10_24_descent (t : Nat) :
    iterateA 24 (start (q10Param t)) < start (q10Param t) := by
  have hcomp := iterateA_comp 23 1 (start (q10Param t))
  have h24 :
      iterateA 24 (start (q10Param t)) =
        iterateA 1 (iterateA 23 (start (q10Param t))) := by
    simpa using hcomp
  rw [h24, q10_endpoint_eq t]
  have hV185 : q10Endpoint t < start (q10Param t) := by
    rw [← q10_endpoint_eq t]
    exact V185_finite_descent (q10Param t)
  exact lt_trans (q10_post_step_descent t) hV185

end EimersV185Q10Extension

#print EimersV185Q10Extension.v185_q10_24_descent
#print axioms EimersV185Q10Extension.v185_q10_24_descent
