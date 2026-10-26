import CertificateFamilies24
import OrdinaryBridge

set_option maxRecDepth 10000

open CollatzResearch
open CollatzCertificate24

namespace CollatzCertificate24

-- Ordinary-map descent derived from each formal accelerated certificate.
theorem family_1_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 112 (17293822687243665435 + q * 2 ^ 70) = endpoint ∧
      endpoint < 17293822687243665435 + q * 2 ^ 70 := by
  rcases family_1_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_2_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 114 (10376293659602583579 + q * 2 ^ 71) = endpoint ∧
      endpoint < 10376293659602583579 + q * 2 ^ 71 := by
  rcases family_2_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_3_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 113 (12682136668816277531 + q * 2 ^ 72) = endpoint ∧
      endpoint < 12682136668816277531 + q * 2 ^ 72 := by
  rcases family_3_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_4_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 119 (3458764631961501723 + q * 2 ^ 74) = endpoint ∧
      endpoint < 3458764631961501723 + q * 2 ^ 74 := by
  rcases family_4_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_5_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 118 (1152921622747807771 + q * 2 ^ 75) = endpoint ∧
      endpoint < 1152921622747807771 + q * 2 ^ 75 := by
  rcases family_5_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_6_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 121 (11529215164209430555 + q * 2 ^ 76) = endpoint ∧
      endpoint < 11529215164209430555 + q * 2 ^ 76 := by
  rcases family_6_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_7_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 121 (13258597421119701019 + q * 2 ^ 76) = endpoint ∧
      endpoint < 13258597421119701019 + q * 2 ^ 76 := by
  rcases family_7_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_8_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 124 (2305843127354654747 + q * 2 ^ 78) = endpoint ∧
      endpoint < 2305843127354654747 + q * 2 ^ 78 := by
  rcases family_8_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_9_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 127 (16717361934940241947 + q * 2 ^ 79) = endpoint ∧
      endpoint < 16717361934940241947 + q * 2 ^ 79 := by
  rcases family_9_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_10_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 128 (7493989898085466139 + q * 2 ^ 80) = endpoint ∧
      endpoint < 7493989898085466139 + q * 2 ^ 80 := by
  rcases family_10_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_11_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 129 (8070450650388889627 + q * 2 ^ 81) = endpoint ∧
      endpoint < 8070450650388889627 + q * 2 ^ 81 := by
  rcases family_11_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_12_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 132 (2882303879658078235 + q * 2 ^ 82) = endpoint ∧
      endpoint < 2882303879658078235 + q * 2 ^ 82 := by
  rcases family_12_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_13_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 129 (16140901182636818459 + q * 2 ^ 82) = endpoint ∧
      endpoint < 16140901182636818459 + q * 2 ^ 82 := by
  rcases family_13_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_14_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 136 (576460870444384283 + q * 2 ^ 85) = endpoint ∧
      endpoint < 576460870444384283 + q * 2 ^ 85 := by
  rcases family_14_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_15_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 143 (6341068393478619163 + q * 2 ^ 89) = endpoint ∧
      endpoint < 6341068393478619163 + q * 2 ^ 89 := by
  rcases family_15_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_16_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 143 (12105675916512854043 + q * 2 ^ 89) = endpoint ∧
      endpoint < 12105675916512854043 + q * 2 ^ 89 := by
  rcases family_16_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_17_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 145 (10952754411906007067 + q * 2 ^ 90) = endpoint ∧
      endpoint < 10952754411906007067 + q * 2 ^ 90 := by
  rcases family_17_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_18_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 144 (14987979678029971483 + q * 2 ^ 90) = endpoint ∧
      endpoint < 14987979678029971483 + q * 2 ^ 90 := by
  rcases family_18_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_19_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 150 (1729382375051231259 + q * 2 ^ 93) = endpoint ∧
      endpoint < 1729382375051231259 + q * 2 ^ 93 := by
  rcases family_19_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_20_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 159 (14411518925726547995 + q * 2 ^ 99) = endpoint ∧
      endpoint < 14411518925726547995 + q * 2 ^ 99 := by
  rcases family_20_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_21_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 169 (8646911402692313115 + q * 2 ^ 105) = endpoint ∧
      endpoint < 8646911402692313115 + q * 2 ^ 105 := by
  rcases family_21_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_22_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 174 (4035225384264925211 + q * 2 ^ 108) = endpoint ∧
      endpoint < 4035225384264925211 + q * 2 ^ 108 := by
  rcases family_22_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_23_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 175 (6917529145782042651 + q * 2 ^ 109) = endpoint ∧
      endpoint < 6917529145782042651 + q * 2 ^ 109 := by
  rcases family_23_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

theorem family_24_ordinary_descent (q : Nat) :
    ∃ endpoint, ordinaryRun 180 (4611686136568348699 + q * 2 ^ 112) = endpoint ∧
      endpoint < 4611686136568348699 + q * 2 ^ 112 := by
  rcases family_24_all_lifts q with ⟨endpoint, htrace, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary htrace, hlt⟩

#print axioms family_1_ordinary_descent
#print axioms family_2_ordinary_descent
#print axioms family_3_ordinary_descent
#print axioms family_4_ordinary_descent
#print axioms family_5_ordinary_descent
#print axioms family_6_ordinary_descent
#print axioms family_7_ordinary_descent
#print axioms family_8_ordinary_descent
#print axioms family_9_ordinary_descent
#print axioms family_10_ordinary_descent
#print axioms family_11_ordinary_descent
#print axioms family_12_ordinary_descent
#print axioms family_13_ordinary_descent
#print axioms family_14_ordinary_descent
#print axioms family_15_ordinary_descent
#print axioms family_16_ordinary_descent
#print axioms family_17_ordinary_descent
#print axioms family_18_ordinary_descent
#print axioms family_19_ordinary_descent
#print axioms family_20_ordinary_descent
#print axioms family_21_ordinary_descent
#print axioms family_22_ordinary_descent
#print axioms family_23_ordinary_descent
#print axioms family_24_ordinary_descent

end CollatzCertificate24
