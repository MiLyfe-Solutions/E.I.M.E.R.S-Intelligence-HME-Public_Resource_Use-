import CPOQ.O58SegmentGuards69

namespace CPOQ

/--
Gate 1 transport lift for the largest finite O5/8 segment class (guard 33).

This theorem is intentionally a transport theorem, not a claim that every integer
in a residue cylinder follows the same Collatz valuation word. It proves that the
single certified guard authorizes transport for every integer pair (n,C) whose
source margin is at least the certified lower bound L.
-/
theorem o58_segment33_infinite_transport_authorized
    (n C : Int)
    (hsource :
      (248567718207939398477346995546745342780487237632 : Int) ≤
        margin
          (77371252455336267181195264 : Int)
          (58149737003040059690390169 : Int)
          n C) :
    0 < margin
      (77371252455336267181195264 : Int)
      (58149737003040059690390169 : Int)
      (n + 4869997505073799665549312)
      (C + 8430432401778095394127872) := by
  exact segment_margin_transport_positive
    (77371252455336267181195264 : Int)
    (58149737003040059690390169 : Int)
    n C
    (4869997505073799665549312 : Int)
    (8430432401778095394127872 : Int)
    (248567718207939398477346995546745342780487237632 : Int)
    hsource
    o58_segment_guard_33

/--
Observed-residue wrapper for segment 33. All 311 finite source witnesses in the
cohort have n ≡ 3487011090801549639707 (mod 2^73) and
C ≡ 4882462854978472446429 (mod 2^73).

This theorem lifts the transport authorization over that entire two-parameter
residue lattice, conditional on the certified source-margin lower bound. It does
NOT assert that every such pair is realized by an actual Collatz trajectory.
-/
theorem o58_segment33_residue_lattice_transport
    (q p : Nat)
    (hsource :
      (248567718207939398477346995546745342780487237632 : Int) ≤
        margin
          (77371252455336267181195264 : Int)
          (58149737003040059690390169 : Int)
          ((3487011090801549639707 : Int) +
            (9444732965739290427392 : Int) * (q : Int))
          ((4882462854978472446429 : Int) +
            (9444732965739290427392 : Int) * (p : Int))) :
    0 < margin
      (77371252455336267181195264 : Int)
      (58149737003040059690390169 : Int)
      (((3487011090801549639707 : Int) +
          (9444732965739290427392 : Int) * (q : Int)) +
        4869997505073799665549312)
      (((4882462854978472446429 : Int) +
          (9444732965739290427392 : Int) * (p : Int)) +
        8430432401778095394127872) := by
  exact o58_segment33_infinite_transport_authorized
    ((3487011090801549639707 : Int) +
      (9444732965739290427392 : Int) * (q : Int))
    ((4882462854978472446429 : Int) +
      (9444732965739290427392 : Int) * (p : Int))
    hsource

end CPOQ
