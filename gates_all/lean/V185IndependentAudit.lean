import V185FinalCandidate

#check EimersV185Full.V185_finite_descent
#print axioms EimersV185Full.V185_finite_descent

#print EimersV185Bridge.start
#print EimersV185Full.iterateA
#check acceleratedTest

theorem independent_v185_explicit (q : Nat) :
    EimersV185Full.iterateA 23 (55863935003 + q * 137438953472) <
      55863935003 + q * 137438953472 := by
  simpa only [EimersV185Bridge.start] using
    EimersV185Full.V185_finite_descent q

#print axioms independent_v185_explicit
