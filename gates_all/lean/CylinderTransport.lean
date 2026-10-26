import Mathlib

namespace CPOQ

-- Affine identities compose without assuming any Collatz trajectory semantics.
theorem prefix_transport (n x y p r S T BP CW : Nat)
    (hp : 2 ^ S * x = 3 ^ p * n + BP)
    (hs : 2 ^ T * y = 3 ^ r * x + CW) :
    2 ^ (S + T) * y = 3 ^ (p + r) * n + (3 ^ r * BP + 2 ^ S * CW) := by
  calc
    2 ^ (S + T) * y = 2 ^ S * (2 ^ T * y) := by simp only [pow_add, mul_assoc]
    _ = 2 ^ S * (3 ^ r * x + CW) := by rw [hs]
    _ = 3 ^ r * (2 ^ S * x) + 2 ^ S * CW := by ring
    _ = 3 ^ r * (3 ^ p * n + BP) + 2 ^ S * CW := by rw [hp]
    _ = 3 ^ (p + r) * n + (3 ^ r * BP + 2 ^ S * CW) := by
      rw [pow_add]
      ring

-- A strict inequality at the affine endpoint yields descent.
theorem affine_descent_uniform (n y k S B : Nat)
    (hidentity : 2 ^ S * y = 3 ^ k * n + B)
    (hbound : 3 ^ k * n + B < 2 ^ S * n) : y < n := by
  have h : 2 ^ S * y < 2 ^ S * n := by omega
  exact (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ S)).mp h

-- Congruence transport under a step that is a multiple of the guard modulus.
theorem suffix_guard_transport (x d a T : Nat)
    (hguard : x % (2 ^ (T + 1)) = a % (2 ^ (T + 1)))
    (hstep : 2 ^ (T + 1) ∣ d) :
    ∀ u : Nat, (x + d * u) % (2 ^ (T + 1)) = a % (2 ^ (T + 1)) := by
  intro u
  rcases hstep with ⟨c, rfl⟩
  simpa [Nat.add_mod, Nat.mul_mod] using hguard

-- The uniform cylinder endpoint is below its corresponding start.
theorem cylinder_descent (n0 y0 D E u : Nat)
    (hbase : y0 < n0)
    (hslope : E ≤ D) : y0 + E * u < n0 + D * u := by
  have hmul : E * u <= D * u := Nat.mul_le_mul_right u hslope
  omega

#print axioms CPOQ.prefix_transport
#print axioms CPOQ.affine_descent_uniform
#print axioms CPOQ.suffix_guard_transport
#print axioms CPOQ.cylinder_descent

end CPOQ
