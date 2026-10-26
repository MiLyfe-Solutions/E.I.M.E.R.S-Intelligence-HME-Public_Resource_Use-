import Mathlib

/-!
V185 exact symbolic step-chain, generated from independent integer arithmetic.
No sorry, custom axioms, or unproved theorem identifiers.
This validates the symbolic 22-step recurrence, NOT YET that these are
the iterations of the valuation-defined accelerated Collatz map.
-/

namespace EimersV185Bridge

def start (q : ℕ) : ℕ := 55863935003 + q * 137438953472

def state0 (q : ℕ) : ℕ := 55863935003 + q * 137438953472
def state1 (q : ℕ) : ℕ := 83795902505 + q * 206158430208
def state2 (q : ℕ) : ℕ := 62846926879 + q * 154618822656
def state3 (q : ℕ) : ℕ := 94270390319 + q * 231928233984
def state4 (q : ℕ) : ℕ := 141405585479 + q * 347892350976
def state5 (q : ℕ) : ℕ := 212108378219 + q * 521838526464
def state6 (q : ℕ) : ℕ := 318162567329 + q * 782757789696
def state7 (q : ℕ) : ℕ := 238621925497 + q * 587068342272
def state8 (q : ℕ) : ℕ := 178966444123 + q * 440301256704
def state9 (q : ℕ) : ℕ := 268449666185 + q * 660451885056
def state10 (q : ℕ) : ℕ := 201337249639 + q * 495338913792
def state11 (q : ℕ) : ℕ := 302005874459 + q * 743008370688
def state12 (q : ℕ) : ℕ := 453008811689 + q * 1114512556032
def state13 (q : ℕ) : ℕ := 339756608767 + q * 835884417024
def state14 (q : ℕ) : ℕ := 509634913151 + q * 1253826625536
def state15 (q : ℕ) : ℕ := 764452369727 + q * 1880739938304
def state16 (q : ℕ) : ℕ := 1146678554591 + q * 2821109907456
def state17 (q : ℕ) : ℕ := 1720017831887 + q * 4231664861184
def state18 (q : ℕ) : ℕ := 2580026747831 + q * 6347497291776
def state19 (q : ℕ) : ℕ := 3870040121747 + q * 9521245937664
def state20 (q : ℕ) : ℕ := 5805060182621 + q * 14281868906496
def state21 (q : ℕ) : ℕ := 2176897568483 + q * 5355700839936
def state22 (q : ℕ) : ℕ := 3265346352725 + q * 8033551259904

theorem start_eq_state0 (q : ℕ) : start q = state0 q := by rfl

/-- Exact step 1: division by 2^1; its quotient is odd for all q. -/
theorem step1_identity (q : ℕ) :
    3 * state0 q + 1 = 2 * state1 q := by
  simp only [state0, state1]
  ring

theorem step1_odd (q : ℕ) : state1 q % 2 = 1 := by
  simp only [state1]
  omega

/-- Exact step 2: division by 2^2; its quotient is odd for all q. -/
theorem step2_identity (q : ℕ) :
    3 * state1 q + 1 = 4 * state2 q := by
  simp only [state1, state2]
  ring

theorem step2_odd (q : ℕ) : state2 q % 2 = 1 := by
  simp only [state2]
  omega

/-- Exact step 3: division by 2^1; its quotient is odd for all q. -/
theorem step3_identity (q : ℕ) :
    3 * state2 q + 1 = 2 * state3 q := by
  simp only [state2, state3]
  ring

theorem step3_odd (q : ℕ) : state3 q % 2 = 1 := by
  simp only [state3]
  omega

/-- Exact step 4: division by 2^1; its quotient is odd for all q. -/
theorem step4_identity (q : ℕ) :
    3 * state3 q + 1 = 2 * state4 q := by
  simp only [state3, state4]
  ring

theorem step4_odd (q : ℕ) : state4 q % 2 = 1 := by
  simp only [state4]
  omega

/-- Exact step 5: division by 2^1; its quotient is odd for all q. -/
theorem step5_identity (q : ℕ) :
    3 * state4 q + 1 = 2 * state5 q := by
  simp only [state4, state5]
  ring

theorem step5_odd (q : ℕ) : state5 q % 2 = 1 := by
  simp only [state5]
  omega

/-- Exact step 6: division by 2^1; its quotient is odd for all q. -/
theorem step6_identity (q : ℕ) :
    3 * state5 q + 1 = 2 * state6 q := by
  simp only [state5, state6]
  ring

theorem step6_odd (q : ℕ) : state6 q % 2 = 1 := by
  simp only [state6]
  omega

/-- Exact step 7: division by 2^2; its quotient is odd for all q. -/
theorem step7_identity (q : ℕ) :
    3 * state6 q + 1 = 4 * state7 q := by
  simp only [state6, state7]
  ring

theorem step7_odd (q : ℕ) : state7 q % 2 = 1 := by
  simp only [state7]
  omega

/-- Exact step 8: division by 2^2; its quotient is odd for all q. -/
theorem step8_identity (q : ℕ) :
    3 * state7 q + 1 = 4 * state8 q := by
  simp only [state7, state8]
  ring

theorem step8_odd (q : ℕ) : state8 q % 2 = 1 := by
  simp only [state8]
  omega

/-- Exact step 9: division by 2^1; its quotient is odd for all q. -/
theorem step9_identity (q : ℕ) :
    3 * state8 q + 1 = 2 * state9 q := by
  simp only [state8, state9]
  ring

theorem step9_odd (q : ℕ) : state9 q % 2 = 1 := by
  simp only [state9]
  omega

/-- Exact step 10: division by 2^2; its quotient is odd for all q. -/
theorem step10_identity (q : ℕ) :
    3 * state9 q + 1 = 4 * state10 q := by
  simp only [state9, state10]
  ring

theorem step10_odd (q : ℕ) : state10 q % 2 = 1 := by
  simp only [state10]
  omega

/-- Exact step 11: division by 2^1; its quotient is odd for all q. -/
theorem step11_identity (q : ℕ) :
    3 * state10 q + 1 = 2 * state11 q := by
  simp only [state10, state11]
  ring

theorem step11_odd (q : ℕ) : state11 q % 2 = 1 := by
  simp only [state11]
  omega

/-- Exact step 12: division by 2^1; its quotient is odd for all q. -/
theorem step12_identity (q : ℕ) :
    3 * state11 q + 1 = 2 * state12 q := by
  simp only [state11, state12]
  ring

theorem step12_odd (q : ℕ) : state12 q % 2 = 1 := by
  simp only [state12]
  omega

/-- Exact step 13: division by 2^2; its quotient is odd for all q. -/
theorem step13_identity (q : ℕ) :
    3 * state12 q + 1 = 4 * state13 q := by
  simp only [state12, state13]
  ring

theorem step13_odd (q : ℕ) : state13 q % 2 = 1 := by
  simp only [state13]
  omega

/-- Exact step 14: division by 2^1; its quotient is odd for all q. -/
theorem step14_identity (q : ℕ) :
    3 * state13 q + 1 = 2 * state14 q := by
  simp only [state13, state14]
  ring

theorem step14_odd (q : ℕ) : state14 q % 2 = 1 := by
  simp only [state14]
  omega

/-- Exact step 15: division by 2^1; its quotient is odd for all q. -/
theorem step15_identity (q : ℕ) :
    3 * state14 q + 1 = 2 * state15 q := by
  simp only [state14, state15]
  ring

theorem step15_odd (q : ℕ) : state15 q % 2 = 1 := by
  simp only [state15]
  omega

/-- Exact step 16: division by 2^1; its quotient is odd for all q. -/
theorem step16_identity (q : ℕ) :
    3 * state15 q + 1 = 2 * state16 q := by
  simp only [state15, state16]
  ring

theorem step16_odd (q : ℕ) : state16 q % 2 = 1 := by
  simp only [state16]
  omega

/-- Exact step 17: division by 2^1; its quotient is odd for all q. -/
theorem step17_identity (q : ℕ) :
    3 * state16 q + 1 = 2 * state17 q := by
  simp only [state16, state17]
  ring

theorem step17_odd (q : ℕ) : state17 q % 2 = 1 := by
  simp only [state17]
  omega

/-- Exact step 18: division by 2^1; its quotient is odd for all q. -/
theorem step18_identity (q : ℕ) :
    3 * state17 q + 1 = 2 * state18 q := by
  simp only [state17, state18]
  ring

theorem step18_odd (q : ℕ) : state18 q % 2 = 1 := by
  simp only [state18]
  omega

/-- Exact step 19: division by 2^1; its quotient is odd for all q. -/
theorem step19_identity (q : ℕ) :
    3 * state18 q + 1 = 2 * state19 q := by
  simp only [state18, state19]
  ring

theorem step19_odd (q : ℕ) : state19 q % 2 = 1 := by
  simp only [state19]
  omega

/-- Exact step 20: division by 2^1; its quotient is odd for all q. -/
theorem step20_identity (q : ℕ) :
    3 * state19 q + 1 = 2 * state20 q := by
  simp only [state19, state20]
  ring

theorem step20_odd (q : ℕ) : state20 q % 2 = 1 := by
  simp only [state20]
  omega

/-- Exact step 21: division by 2^3; its quotient is odd for all q. -/
theorem step21_identity (q : ℕ) :
    3 * state20 q + 1 = 8 * state21 q := by
  simp only [state20, state21]
  ring

theorem step21_odd (q : ℕ) : state21 q % 2 = 1 := by
  simp only [state21]
  omega

/-- Exact step 22: division by 2^1; its quotient is odd for all q. -/
theorem step22_identity (q : ℕ) :
    3 * state21 q + 1 = 2 * state22 q := by
  simp only [state21, state22]
  ring

theorem step22_odd (q : ℕ) : state22 q % 2 = 1 := by
  simp only [state22]
  omega

theorem start_odd (q : ℕ) : start q % 2 = 1 := by
  simp only [start]
  omega

/-- The last 3x+1 is divisible by 2^8 on the entire source class. -/
theorem tail_divisible (q : ℕ) :
    3 * state22 q + 1 = 256 * (38265777571 + q * 94143178827) := by
  simp only [state22]
  ring

theorem state22_prefix (q : ℕ) :
    536870912 * state22 q = 31381059609 * start q + 60899841373 := by
  simp only [state22, start]
  ring

theorem bound_if_tail_endpoint (q endpoint : ℕ)
    (h : 256 * endpoint ≤ 3 * state22 q + 1) :
    endpoint < start q := by
  have hprefix := state22_prefix q
  have hbound : 137438953472 * endpoint ≤
       94143178827 * start q + 183236395031 := by
    calc
      137438953472 * endpoint = 536870912 * (256 * endpoint) := by ring
      _ ≤ 536870912 * (3 * state22 q + 1) := Nat.mul_le_mul_left _ h
      _ = 3 * (536870912 * state22 q) + 536870912 := by ring
      _ = 3 * (31381059609 * start q + 60899841373) + 536870912 := by rw [hprefix]
      _ = 94143178827 * start q + 183236395031 := by ring
  have hlow : 55863935003 ≤ start q := by
    dsimp [start]
    omega
  have hpositive :
      183236395031 < 43295774645 * 55863935003 := by
    norm_num
  have hscaled :
      43295774645 * 55863935003 ≤
      43295774645 * start q :=
    Nat.mul_le_mul_left _ hlow
  have htail :
      183236395031 < 43295774645 * start q :=
    lt_of_lt_of_le hpositive hscaled
  have hmargin :
      94143178827 * start q + 183236395031 <
      137438953472 * start q := by
    nlinarith only [htail]
  have hfinal :
      137438953472 * endpoint <
      137438953472 * start q :=
    lt_of_le_of_lt hbound hmargin
  nlinarith only [hfinal]

end EimersV185Bridge
