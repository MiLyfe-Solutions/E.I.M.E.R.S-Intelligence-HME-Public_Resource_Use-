import BoundedDescent

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace CollatzResearch

/-- Exact valuation word, independently replayed before source emission. -/
def child_r118140960795_b83_q154_word : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 6]

theorem child_r118140960795_b83_q154_representative :
    88774955972868177947 = 118140960795 + 154 * 2^59 := by decide

theorem child_r118140960795_b83_q154_exact_trace :
    WordTrace child_r118140960795_b83_q154_word 88774955972868177947 13179336816271862383 := by
  unfold child_r118140960795_b83_q154_word
  refine ⟨133162433959302266921, by decide, ?_⟩
  refine ⟨99871825469476700191, by decide, ?_⟩
  refine ⟨149807738204215050287, by decide, ?_⟩
  refine ⟨224711607306322575431, by decide, ?_⟩
  refine ⟨337067410959483863147, by decide, ?_⟩
  refine ⟨505601116439225794721, by decide, ?_⟩
  refine ⟨379200837329419346041, by decide, ?_⟩
  refine ⟨284400627997064509531, by decide, ?_⟩
  refine ⟨426600941995596764297, by decide, ?_⟩
  refine ⟨319950706496697573223, by decide, ?_⟩
  refine ⟨479926059745046359835, by decide, ?_⟩
  refine ⟨719889089617569539753, by decide, ?_⟩
  refine ⟨539916817213177154815, by decide, ?_⟩
  refine ⟨809875225819765732223, by decide, ?_⟩
  refine ⟨1214812838729648598335, by decide, ?_⟩
  refine ⟨1822219258094472897503, by decide, ?_⟩
  refine ⟨2733328887141709346255, by decide, ?_⟩
  refine ⟨4099993330712564019383, by decide, ?_⟩
  refine ⟨6149989996068846029075, by decide, ?_⟩
  refine ⟨9224984994103269043613, by decide, ?_⟩
  refine ⟨3459369372788725891355, by decide, ?_⟩
  refine ⟨5189054059183088837033, by decide, ?_⟩
  refine ⟨3891790544387316627775, by decide, ?_⟩
  refine ⟨5837685816580974941663, by decide, ?_⟩
  refine ⟨8756528724871462412495, by decide, ?_⟩
  refine ⟨13134793087307193618743, by decide, ?_⟩
  refine ⟨19702189630960790428115, by decide, ?_⟩
  refine ⟨29553284446441185642173, by decide, ?_⟩
  refine ⟨11082481667415444615815, by decide, ?_⟩
  refine ⟨16623722501123166923723, by decide, ?_⟩
  refine ⟨24935583751684750385585, by decide, ?_⟩
  refine ⟨18701687813763562789189, by decide, ?_⟩
  refine ⟨3506566465080668022973, by decide, ?_⟩
  refine ⟨1314962424405250508615, by decide, ?_⟩
  refine ⟨1972443636607875762923, by decide, ?_⟩
  refine ⟨2958665454911813644385, by decide, ?_⟩
  refine ⟨2218999091183860233289, by decide, ?_⟩
  refine ⟨1664249318387895174967, by decide, ?_⟩
  refine ⟨2496373977581842762451, by decide, ?_⟩
  refine ⟨3744560966372764143677, by decide, ?_⟩
  refine ⟨1404210362389786553879, by decide, ?_⟩
  refine ⟨2106315543584679830819, by decide, ?_⟩
  refine ⟨3159473315377019746229, by decide, ?_⟩
  refine ⟨296200623316595601209, by decide, ?_⟩
  refine ⟨222150467487446700907, by decide, ?_⟩
  refine ⟨333225701231170051361, by decide, ?_⟩
  refine ⟨249919275923377538521, by decide, ?_⟩
  refine ⟨187439456942533153891, by decide, ?_⟩
  refine ⟨281159185413799730837, by decide, ?_⟩
  refine ⟨13179336816271862383, by decide, ?_⟩
  rfl

theorem child_r118140960795_b83_q154_arithmetic :
    child_r118140960795_b83_q154_word.length = 50 ∧ child_r118140960795_b83_q154_word.sum = 82 ∧
    82 < 83 ∧ 3^50 < 2^82 ∧
    2^82 * 13179336816271862383 = 3^50 * 88774955972868177947 + 2031029826268023297210829 ∧
    2^82 = 3^50 + 4117805290766664110054455 ∧
    4117805290766664110054455 * 88774955972868177947 > 2031029826268023297210829 ∧ 13179336816271862383 < 88774955972868177947 := by decide

theorem child_r118140960795_b83_q154_exact_endpoint :
    ordinaryRun 132 88774955972868177947 = 13179336816271862383 := by
  have h := wordTrace_ordinary child_r118140960795_b83_q154_exact_trace
  simpa only [child_r118140960795_b83_q154_arithmetic.1, child_r118140960795_b83_q154_arithmetic.2.1] using h

/-- Descent for every original integer in this one 83-bit child family. -/
theorem child_r118140960795_b83_q154_ordinary_descent :
    ∀ u : Nat, ∃ endpoint,
      ordinaryRun 132 (88774955972868177947 + u * 2^83) = endpoint ∧
      endpoint < 88774955972868177947 + u * 2^83 := by
  have htrace : BoundedWordTrace child_r118140960795_b83_q154_word 88774955972868177947 13179336816271862383 := by
    refine ⟨13179336816271862383, child_r118140960795_b83_q154_exact_trace, Nat.le_refl _, ?_⟩
    rw [child_r118140960795_b83_q154_arithmetic.2.1]
    decide
  have hcontract : 3^child_r118140960795_b83_q154_word.length < 2^child_r118140960795_b83_q154_word.sum := by
    rw [child_r118140960795_b83_q154_arithmetic.1, child_r118140960795_b83_q154_arithmetic.2.1]
    decide
  have hbound : 13179336816271862383 < 88774955972868177947 := by decide
  have h := family_descent_by_bound child_r118140960795_b83_q154_word 88774955972868177947 13179336816271862383 htrace hcontract hbound
  simpa only [child_r118140960795_b83_q154_arithmetic.1, child_r118140960795_b83_q154_arithmetic.2.1, LIFT_BITS] using h

end CollatzResearch
