namespace EimersCollatz

/-- Every n = 3 + 16*q descends by actual ordinary Collatz steps. -/
theorem family_three_mod_sixteen :
    ∀ q : Nat, ∃ y : Nat, y < 3 + 16 * q ∧
      OrdinaryReach (3 + 16 * q) y := by
  have hw : ExactWord 3 [1] 5 := by
    apply ExactWord.next
    · norm_num [ExactOddStep, Odd]
    · exact ExactWord.stop 5
  have h := certified_word_actual_descent
    4 1 1 1 3 5 [1]
    hw (by norm_num [Odd])
    (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using h

/-- Every n = 7 + 128*q descends by actual ordinary Collatz steps. -/
theorem family_seven_mod_128 :
    ∀ q : Nat, ∃ y : Nat, y < 7 + 128 * q ∧
      OrdinaryReach (7 + 128 * q) y := by
  have hw : ExactWord 7 [1, 1, 2] 13 := by
    apply ExactWord.next
    · norm_num [ExactOddStep, Odd]
    · apply ExactWord.next
      · norm_num [ExactOddStep, Odd]
      · apply ExactWord.next
        · norm_num [ExactOddStep, Odd]
        · exact ExactWord.stop 13
  have h := certified_word_actual_descent
    7 3 4 19 7 13 [1, 1, 2]
    hw (by norm_num [Odd])
    (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using h

#print axioms family_three_mod_sixteen
#print axioms family_seven_mod_128

end EimersCollatz
