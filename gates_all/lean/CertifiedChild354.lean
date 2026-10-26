import BoundedDescent

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace CollatzResearch

def child_r118140960795_b83_q354_word : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 1, 5]

theorem child_r118140960795_b83_q354_representative :
    204067106433552875547 = 118140960795 + 354 * 2^59 := by decide

theorem child_r118140960795_b83_q354_exact_trace :
    WordTrace child_r118140960795_b83_q354_word 204067106433552875547 90886075898424336689 := by
  unfold child_r118140960795_b83_q354_word
  refine ⟨306100659650329313321, by decide, ?_⟩
  refine ⟨229575494737746984991, by decide, ?_⟩
  refine ⟨344363242106620477487, by decide, ?_⟩
  refine ⟨516544863159930716231, by decide, ?_⟩
  refine ⟨774817294739896074347, by decide, ?_⟩
  refine ⟨1162225942109844111521, by decide, ?_⟩
  refine ⟨871669456582383083641, by decide, ?_⟩
  refine ⟨653752092436787312731, by decide, ?_⟩
  refine ⟨980628138655180969097, by decide, ?_⟩
  refine ⟨735471103991385726823, by decide, ?_⟩
  refine ⟨1103206655987078590235, by decide, ?_⟩
  refine ⟨1654809983980617885353, by decide, ?_⟩
  refine ⟨1241107487985463414015, by decide, ?_⟩
  refine ⟨1861661231978195121023, by decide, ?_⟩
  refine ⟨2792491847967292681535, by decide, ?_⟩
  refine ⟨4188737771950939022303, by decide, ?_⟩
  refine ⟨6283106657926408533455, by decide, ?_⟩
  refine ⟨9424659986889612800183, by decide, ?_⟩
  refine ⟨14136989980334419200275, by decide, ?_⟩
  refine ⟨21205484970501628800413, by decide, ?_⟩
  refine ⟨7952056863938110800155, by decide, ?_⟩
  refine ⟨11928085295907166200233, by decide, ?_⟩
  refine ⟨8946063971930374650175, by decide, ?_⟩
  refine ⟨13419095957895561975263, by decide, ?_⟩
  refine ⟨20128643936843342962895, by decide, ?_⟩
  refine ⟨30192965905265014444343, by decide, ?_⟩
  refine ⟨45289448857897521666515, by decide, ?_⟩
  refine ⟨67934173286846282499773, by decide, ?_⟩
  refine ⟨25475314982567355937415, by decide, ?_⟩
  refine ⟨38212972473851033906123, by decide, ?_⟩
  refine ⟨57319458710776550859185, by decide, ?_⟩
  refine ⟨42989594033082413144389, by decide, ?_⟩
  refine ⟨8060548881202952464573, by decide, ?_⟩
  refine ⟨3022705830451107174215, by decide, ?_⟩
  refine ⟨4534058745676660761323, by decide, ?_⟩
  refine ⟨6801088118514991141985, by decide, ?_⟩
  refine ⟨5100816088886243356489, by decide, ?_⟩
  refine ⟨3825612066664682517367, by decide, ?_⟩
  refine ⟨5738418099997023776051, by decide, ?_⟩
  refine ⟨8607627149995535664077, by decide, ?_⟩
  refine ⟨3227860181248325874029, by decide, ?_⟩
  refine ⟨1210447567968122202761, by decide, ?_⟩
  refine ⟨907835675976091652071, by decide, ?_⟩
  refine ⟨1361753513964137478107, by decide, ?_⟩
  refine ⟨2042630270946206217161, by decide, ?_⟩
  refine ⟨1531972703209654662871, by decide, ?_⟩
  refine ⟨2297959054814481994307, by decide, ?_⟩
  refine ⟨3446938582221722991461, by decide, ?_⟩
  refine ⟨646300984166573060899, by decide, ?_⟩
  refine ⟨969451476249859591349, by decide, ?_⟩
  refine ⟨90886075898424336689, by decide, ?_⟩
  rfl

theorem child_r118140960795_b83_q354_arithmetic :
    child_r118140960795_b83_q354_word.length = 51 ∧ child_r118140960795_b83_q354_word.sum = 82 ∧
    82 < 83 ∧ 3^51 < 2^82 ∧
    2^82 * 90886075898424336689 = 3^51 * 204067106433552875547 + 5569040538100073667161447 ∧
    2^82 = 3^51 + 2682009315382958932513957 ∧
    2682009315382958932513957 * 204067106433552875547 > 5569040538100073667161447 ∧ 90886075898424336689 < 204067106433552875547 := by decide

theorem child_r118140960795_b83_q354_exact_endpoint :
    ordinaryRun 133 204067106433552875547 = 90886075898424336689 := by
  have h := wordTrace_ordinary child_r118140960795_b83_q354_exact_trace
  simpa only [child_r118140960795_b83_q354_arithmetic.1, child_r118140960795_b83_q354_arithmetic.2.1] using h

theorem child_r118140960795_b83_q354_ordinary_descent :
    ∀ u : Nat, ∃ endpoint,
      ordinaryRun 133 (204067106433552875547 + u * 2^83) = endpoint ∧
      endpoint < 204067106433552875547 + u * 2^83 := by
  have htrace : BoundedWordTrace child_r118140960795_b83_q354_word 204067106433552875547 90886075898424336689 := by
    refine ⟨90886075898424336689, child_r118140960795_b83_q354_exact_trace, Nat.le_refl _, ?_⟩
    rw [child_r118140960795_b83_q354_arithmetic.2.1]
    decide
  have hcontract : 3^child_r118140960795_b83_q354_word.length < 2^child_r118140960795_b83_q354_word.sum := by
    rw [child_r118140960795_b83_q354_arithmetic.1, child_r118140960795_b83_q354_arithmetic.2.1]
    decide
  have hbound : 90886075898424336689 < 204067106433552875547 := by decide
  have h := family_descent_by_bound child_r118140960795_b83_q354_word 204067106433552875547 90886075898424336689 htrace hcontract hbound
  simpa only [child_r118140960795_b83_q354_arithmetic.1, child_r118140960795_b83_q354_arithmetic.2.1, LIFT_BITS] using h

#print axioms child_r118140960795_b83_q354_representative
#print axioms child_r118140960795_b83_q354_exact_trace
#print axioms child_r118140960795_b83_q354_arithmetic
#print axioms child_r118140960795_b83_q354_exact_endpoint
#print axioms child_r118140960795_b83_q354_ordinary_descent

end CollatzResearch
