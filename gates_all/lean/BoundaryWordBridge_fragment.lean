namespace EimersCollatz

/-- A representative exact word, its affine identity, and one boundary
divisibility certificate yield a descending quotient for every lift.
The quotient is not asserted odd; the final actual-step bridge remains open. -/
theorem certified_word_boundary_descent
    (b k S B r x : Nat) (vs : List Nat)
    (hword : ExactWord r vs x)
    (hcount : vs.length = k)
    (hsum : vs.sum = S)
    (hbits : S < b)
    (hrep : 2 ^ S * x = 3 ^ k * r + B)
    (hterminal : 2 ^ (b - S) ∣ 3 * x + 1)
    (hpower : 3 ^ (k + 1) < 2 ^ b)
    (hcert : (2 ^ b - 3 ^ (k + 1)) * r > 3 * B + 2 ^ S) :
    ∀ q : Nat, ∃ y : Nat,
      y < r + 2 ^ b * q ∧
      ExactWord (r + 2 ^ b * q) vs
        (x + 3 ^ k * 2 ^ (b - S) * q) ∧
      2 ^ (b - S) * y =
        3 * (x + 3 ^ k * 2 ^ (b - S) * q) + 1 := by
  intro q
  have hwq : ExactWord (r + 2 ^ b * q) vs
      (x + 3 ^ k * 2 ^ (b - S) * q) := by
    simpa only [hcount, hsum] using exact_word_lift hword b q hbits
  have hpref := affine_prefix_lift b k S B r x q (by omega) hrep
  have hd := terminal_divisibility_lifts k (b - S) x q hterminal
  obtain ⟨y, hy⟩ := hd
  have hcross : b ≤ S + (b - S) := by omega
  have hr : r ≤ r + 2 ^ b * q := by omega
  have hmass : (2 ^ b - 3 ^ (k + 1)) * r ≤
      (2 ^ b - 3 ^ (k + 1)) * (r + 2 ^ b * q) :=
    Nat.mul_le_mul_left _ hr
  have hsub : (2 ^ b - 3 ^ (k + 1)) + 3 ^ (k + 1) = 2 ^ b :=
    Nat.sub_add_cancel (Nat.le_of_lt hpower)
  have hineq : 3 ^ (k + 1) * (r + 2 ^ b * q) +
      (3 * B + 2 ^ S) < 2 ^ b * (r + 2 ^ b * q) := by
    nlinarith [hmass, hcert]
  have hlt := boundary_descent_one b k S (b - S)
    (x + 3 ^ k * 2 ^ (b - S) * q) y
    (r + 2 ^ b * q) B hpref hy.symm hcross hineq
  exact ⟨y, hlt, hwq, hy.symm⟩

#print axioms certified_word_boundary_descent

end EimersCollatz
