import Mathlib

namespace EimersCollatzConstructive

def OrdinaryCollatzStep (n m : Nat) : Prop :=
  (Odd n ∧ m = 3 * n + 1) ∨
  (∃ z : Nat, n = 2 * z ∧ m = z)

inductive OrdinaryReach : Nat → Nat → Prop where
  | refl (n : Nat) : OrdinaryReach n n
  | cons {a b c : Nat}
      (hs : OrdinaryCollatzStep a b)
      (ht : OrdinaryReach b c) :
      OrdinaryReach a c

theorem family_three_mod_sixteen_constructive :
    ∀ q : Nat, ∃ y : Nat, y < 3 + 16 * q ∧
      OrdinaryReach (3 + 16 * q) y := by
  intro q
  have h01 : OrdinaryCollatzStep (3 + 16*q) (10 + 48*q) := by
    left
    constructor
    · refine ⟨1 + 8*q, by ring⟩
    · ring
  have h12 : OrdinaryCollatzStep (10 + 48*q) (5 + 24*q) := by
    right
    exact ⟨5 + 24*q, by ring, rfl⟩
  have h23 : OrdinaryCollatzStep (5 + 24*q) (16 + 72*q) := by
    left
    constructor
    · refine ⟨2 + 12*q, by ring⟩
    · ring
  have h34 : OrdinaryCollatzStep (16 + 72*q) (8 + 36*q) := by
    right
    exact ⟨8 + 36*q, by ring, rfl⟩
  have h45 : OrdinaryCollatzStep (8 + 36*q) (4 + 18*q) := by
    right
    exact ⟨4 + 18*q, by ring, rfl⟩
  have h56 : OrdinaryCollatzStep (4 + 18*q) (2 + 9*q) := by
    right
    exact ⟨2 + 9*q, by ring, rfl⟩
  refine ⟨2 + 9*q, by omega, ?_⟩
  exact OrdinaryReach.cons h01
    (OrdinaryReach.cons h12
      (OrdinaryReach.cons h23
        (OrdinaryReach.cons h34
          (OrdinaryReach.cons h45
            (OrdinaryReach.cons h56
              (OrdinaryReach.refl (2 + 9*q)))))))

theorem family_seven_mod_128_constructive :
    ∀ q : Nat, ∃ y : Nat, y < 7 + 128 * q ∧
      OrdinaryReach (7 + 128 * q) y := by
  intro q
  have h01 : OrdinaryCollatzStep (7 + 128*q) (22 + 384*q) := by
    left
    constructor
    · refine ⟨3 + 64*q, by ring⟩
    · ring
  have h12 : OrdinaryCollatzStep (22 + 384*q) (11 + 192*q) := by
    right
    exact ⟨11 + 192*q, by ring, rfl⟩
  have h23 : OrdinaryCollatzStep (11 + 192*q) (34 + 576*q) := by
    left
    constructor
    · refine ⟨5 + 96*q, by ring⟩
    · ring
  have h34 : OrdinaryCollatzStep (34 + 576*q) (17 + 288*q) := by
    right
    exact ⟨17 + 288*q, by ring, rfl⟩
  have h45 : OrdinaryCollatzStep (17 + 288*q) (52 + 864*q) := by
    left
    constructor
    · refine ⟨8 + 144*q, by ring⟩
    · ring
  have h56 : OrdinaryCollatzStep (52 + 864*q) (26 + 432*q) := by
    right
    exact ⟨26 + 432*q, by ring, rfl⟩
  have h67 : OrdinaryCollatzStep (26 + 432*q) (13 + 216*q) := by
    right
    exact ⟨13 + 216*q, by ring, rfl⟩
  have h78 : OrdinaryCollatzStep (13 + 216*q) (40 + 648*q) := by
    left
    constructor
    · refine ⟨6 + 108*q, by ring⟩
    · ring
  have h89 : OrdinaryCollatzStep (40 + 648*q) (20 + 324*q) := by
    right
    exact ⟨20 + 324*q, by ring, rfl⟩
  have h910 : OrdinaryCollatzStep (20 + 324*q) (10 + 162*q) := by
    right
    exact ⟨10 + 162*q, by ring, rfl⟩
  have h1011 : OrdinaryCollatzStep (10 + 162*q) (5 + 81*q) := by
    right
    exact ⟨5 + 81*q, by ring, rfl⟩
  refine ⟨5 + 81*q, by omega, ?_⟩
  exact OrdinaryReach.cons h01
    (OrdinaryReach.cons h12
      (OrdinaryReach.cons h23
        (OrdinaryReach.cons h34
          (OrdinaryReach.cons h45
            (OrdinaryReach.cons h56
              (OrdinaryReach.cons h67
                (OrdinaryReach.cons h78
                  (OrdinaryReach.cons h89
                    (OrdinaryReach.cons h910
                      (OrdinaryReach.cons h1011
                        (OrdinaryReach.refl (5 + 81*q))))))))))))

#print axioms family_three_mod_sixteen_constructive
#print axioms family_seven_mod_128_constructive

end EimersCollatzConstructive
