import Mathlib

namespace CPOQCylinder

/-- Exact transport of a prefix affine identity across a source cylinder.
    No trajectory or valuation claim is assumed by this algebraic lemma. -/
theorem prefix_transport
    (n x u p S D B : Nat)
    (h : 2^S * x = 3^p * n + B)
    (hD : 2^S ∣ D) :
    2^S * (x + 3^p * (D / 2^S) * u) =
      3^p * (n + D * u) + B := by
  obtain ⟨d, hd⟩ := hD
  subst D
  calc
    2^S * (x + 3^p * d * u) = 2^S*x + 2^S*(3^p*d*u) := by ring
    _ = (3^p*n+B) + 3^p*(2^S*d*u) := by rw [h]; ring
    _ = 3^p*(n + (2^S*d)*u)+B := by ring

/-- A representative affine descent inequality remains true for every
    nonnegative displacement when its linear coefficient contracts. -/
theorem affine_descent_uniform
    (n u k S B D : Nat)
    (hbase : 3^k*n+B < 2^S*n)
    (hslope : 3^k < 2^S) :
    3^k*(n+D*u)+B < 2^S*(n+D*u) := by
  have hnonneg : 3^k*(D*u) <= 2^S*(D*u) :=
    Nat.mul_le_mul_right (D*u) (Nat.le_of_lt hslope)
  nlinarith [hbase, hnonneg]

/-- The suffix's input is unchanged modulo 2^(T+1) if the
    transported prefix displacement is a multiple of that modulus. -/
theorem suffix_guard_transport
    (x u p T E : Nat)
    (hE : 2^(T+1) ∣ E) :
    (x + 3^p * E * u) % 2^(T+1) = x % 2^(T+1) := by
  obtain ⟨d, hd⟩ := hE
  subst E
  simp [Nat.add_mod, Nat.mul_mod]

/-- End-to-end algebraic descent, conditional on the exact affine identity. -/
theorem cylinder_descent
    (n y u k S B D : Nat)
    (hfinal : 2^S*y = 3^k*(n+D*u)+B)
    (hbase : 3^k*n+B < 2^S*n)
    (hslope : 3^k < 2^S) : y < n+D*u := by
  have hb := affine_descent_uniform n u k S B D hbase hslope
  have hlt : 2^S*y < 2^S*(n+D*u) := by omega
  exact (Nat.mul_lt_mul_left (by positivity : 0 < 2^S)).mp hlt

#print axioms prefix_transport
#print axioms affine_descent_uniform
#print axioms suffix_guard_transport
#print axioms cylinder_descent
end CPOQCylinder
