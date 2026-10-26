import V185TrunkScan23Chunk0285

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1691618 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1691618 : Nat := 118140960795 + 1691618 * 2 ^ 59
def prefixEnd_1691618 : Nat := 4983230072969 + 3 ^ 40 * 1691618 * 2
def baseEnd_1691618 : Nat := 289537705932489256831799

theorem tailTrace_1691618 : CollatzResearch.WordTrace tailWord_1691618 prefixEnd_1691618 289537705932489256831799 := by
  unfold tailWord_1691618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15424594296391091549644877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41132251457042910799053005 15424594296391091549644877)
  ·
    refine ⟨5784222861146659331116829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15424594296391091549644877 5784222861146659331116829)
    ·
      refine ⟨2169083572929997249168811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5784222861146659331116829 2169083572929997249168811)
      ·
        refine ⟨3253625359394995873753217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169083572929997249168811 3253625359394995873753217)
        ·
          refine ⟨2440219019546246905314913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3253625359394995873753217 2440219019546246905314913)
          ·
            refine ⟨1830164264659685178986185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440219019546246905314913 1830164264659685178986185)
            ·
              refine ⟨1372623198494763884239639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830164264659685178986185 1372623198494763884239639)
              ·
                refine ⟨2058934797742145826359459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372623198494763884239639 2058934797742145826359459)
                ·
                  refine ⟨3088402196613218739539189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058934797742145826359459 3088402196613218739539189)
                  ·
                    refine ⟨289537705932489256831799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3088402196613218739539189 289537705932489256831799)
                    ·
                      rfl

theorem cell23_1691618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1691618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691618 prefixEnd_1691618 := by exact prefixLift 1691618
  have htrace : WordTrace (prefixWord ++ tailWord_1691618) baseStart_1691618 baseEnd_1691618 := by
    simpa [prefixWord, tailWord_1691618, baseEnd_1691618] using wordTrace_append hprefix tailTrace_1691618
  have hstable : (prefixWord ++ tailWord_1691618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691618).length < 2 ^ (prefixWord ++ tailWord_1691618).sum := by decide
  have hdescent : baseEnd_1691618 < baseStart_1691618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691638 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_1691638 : Nat := 118140960795 + 1691638 * 2 ^ 59
def prefixEnd_1691638 : Nat := 4983230072969 + 3 ^ 40 * 1691638 * 2
def baseEnd_1691638 : Nat := 868623387410557692245305

theorem tailTrace_1691638 : CollatzResearch.WordTrace tailWord_1691638 prefixEnd_1691638 868623387410557692245305 := by
  unfold tailWord_1691638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856194165343244350894223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41132737763661273076205045 3856194165343244350894223)
  ·
    refine ⟨5784291248014866526341335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3856194165343244350894223 5784291248014866526341335)
    ·
      refine ⟨8676436872022299789512003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5784291248014866526341335 8676436872022299789512003)
      ·
        refine ⟨13014655308033449684268005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8676436872022299789512003 13014655308033449684268005)
        ·
          refine ⟨2440247870256271815800251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13014655308033449684268005 2440247870256271815800251)
          ·
            refine ⟨3660371805384407723700377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440247870256271815800251 3660371805384407723700377)
            ·
              refine ⟨2745278854038305792775283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3660371805384407723700377 2745278854038305792775283)
              ·
                refine ⟨4117918281057458689162925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745278854038305792775283 4117918281057458689162925)
                ·
                  refine ⟨1544219355396547008436097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4117918281057458689162925 1544219355396547008436097)
                  ·
                    refine ⟨1158164516547410256327073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1544219355396547008436097 1158164516547410256327073)
                    ·
                      refine ⟨868623387410557692245305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158164516547410256327073 868623387410557692245305)
                      ·
                        rfl

theorem cell23_1691638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_1691638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691638 prefixEnd_1691638 := by exact prefixLift 1691638
  have htrace : WordTrace (prefixWord ++ tailWord_1691638) baseStart_1691638 baseEnd_1691638 := by
    simpa [prefixWord, tailWord_1691638, baseEnd_1691638] using wordTrace_append hprefix tailTrace_1691638
  have hstable : (prefixWord ++ tailWord_1691638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691638).length < 2 ^ (prefixWord ++ tailWord_1691638).sum := by decide
  have hdescent : baseEnd_1691638 < baseStart_1691638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691647 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 5, 3, 2]
def baseStart_1691647 : Nat := 118140960795 + 1691647 * 2 ^ 59
def prefixEnd_1691647 : Nat := 4983230072969 + 3 ^ 40 * 1691647 * 2
def baseEnd_1691647 : Nat := 868628008736448157032763

theorem tailTrace_1691647 : CollatzResearch.WordTrace tailWord_1691647 prefixEnd_1691647 868628008736448157032763 := by
  unfold tailWord_1691647
  simp only [CollatzResearch.WordTrace]
  refine ⟨61699434902459304151385195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41132956601639536100923463 61699434902459304151385195)
  ·
    refine ⟨92549152353688956227077793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61699434902459304151385195 92549152353688956227077793)
    ·
      refine ⟨69411864265266717170308345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92549152353688956227077793 69411864265266717170308345)
      ·
        refine ⟨52058898198950037877731259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69411864265266717170308345 52058898198950037877731259)
        ·
          refine ⟨78088347298425056816596889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52058898198950037877731259 78088347298425056816596889)
          ·
            refine ⟨58566260473818792612447667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78088347298425056816596889 58566260473818792612447667)
            ·
              refine ⟨87849390710728188918671501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58566260473818792612447667 87849390710728188918671501)
              ·
                refine ⟨32943521516523070844501813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87849390710728188918671501 32943521516523070844501813)
                ·
                  refine ⟨3088455142174037891672045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32943521516523070844501813 3088455142174037891672045)
                  ·
                    refine ⟨1158170678315264209377017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3088455142174037891672045 1158170678315264209377017)
                    ·
                      refine ⟨868628008736448157032763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158170678315264209377017 868628008736448157032763)
                      ·
                        rfl

theorem cell23_1691647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_1691647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691647 prefixEnd_1691647 := by exact prefixLift 1691647
  have htrace : WordTrace (prefixWord ++ tailWord_1691647) baseStart_1691647 baseEnd_1691647 := by
    simpa [prefixWord, tailWord_1691647, baseEnd_1691647] using wordTrace_append hprefix tailTrace_1691647
  have hstable : (prefixWord ++ tailWord_1691647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691647).length < 2 ^ (prefixWord ++ tailWord_1691647).sum := by decide
  have hdescent : baseEnd_1691647 < baseStart_1691647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691661 : List Nat := [1, 7, 1, 2, 1, 1, 1, 9]
def baseStart_1691661 : Nat := 118140960795 + 1691661 * 2 ^ 59
def prefixEnd_1691661 : Nat := 4983230072969 + 3 ^ 40 * 1691661 * 2
def baseEnd_1691661 : Nat := 32171673980207818602137

theorem tailTrace_1691661 : CollatzResearch.WordTrace tailWord_1691661 prefixEnd_1691661 32171673980207818602137 := by
  unfold tailWord_1691661
  simp only [CollatzResearch.WordTrace]
  refine ⟨61699945524408584542394837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41133297016272389694929891 61699945524408584542394837)
  ·
    refine ⟨1446092473228326200212379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 61699945524408584542394837 1446092473228326200212379)
    ·
      refine ⟨2169138709842489300318569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446092473228326200212379 2169138709842489300318569)
      ·
        refine ⟨1626854032381866975238927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2169138709842489300318569 1626854032381866975238927)
        ·
          refine ⟨2440281048572800462858391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626854032381866975238927 2440281048572800462858391)
          ·
            refine ⟨3660421572859200694287587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440281048572800462858391 3660421572859200694287587)
            ·
              refine ⟨5490632359288801041431381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660421572859200694287587 5490632359288801041431381)
              ·
                refine ⟨32171673980207818602137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5490632359288801041431381 32171673980207818602137)
                ·
                  rfl

theorem cell23_1691661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 9].length) (baseStart_1691661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691661 prefixEnd_1691661 := by exact prefixLift 1691661
  have htrace : WordTrace (prefixWord ++ tailWord_1691661) baseStart_1691661 baseEnd_1691661 := by
    simpa [prefixWord, tailWord_1691661, baseEnd_1691661] using wordTrace_append hprefix tailTrace_1691661
  have hstable : (prefixWord ++ tailWord_1691661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691661).length < 2 ^ (prefixWord ++ tailWord_1691661).sum := by decide
  have hdescent : baseEnd_1691661 < baseStart_1691661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691705 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 2, 1, 3]
def baseStart_1691705 : Nat := 118140960795 + 1691705 * 2 ^ 59
def prefixEnd_1691705 : Nat := 4983230072969 + 3 ^ 40 * 1691705 * 2
def baseEnd_1691705 : Nat := 868657790614408930107497

theorem tailTrace_1691705 : CollatzResearch.WordTrace tailWord_1691705 prefixEnd_1691705 868657790614408930107497 := by
  unfold tailWord_1691705
  simp only [CollatzResearch.WordTrace]
  refine ⟨61701550336249180056996569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41134366890832786704664379 61701550336249180056996569)
  ·
    refine ⟨46276162752186885042747427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61701550336249180056996569 46276162752186885042747427)
    ·
      refine ⟨69414244128280327564121141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46276162752186885042747427 69414244128280327564121141)
      ·
        refine ⟨6507585387026280709136357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69414244128280327564121141 6507585387026280709136357)
        ·
          refine ⟨1220172260067427632963067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6507585387026280709136357 1220172260067427632963067)
          ·
            refine ⟨1830258390101141449444601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220172260067427632963067 1830258390101141449444601)
            ·
              refine ⟨1372693792575856087083451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830258390101141449444601 1372693792575856087083451)
              ·
                refine ⟨2059040688863784130625177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372693792575856087083451 2059040688863784130625177)
                ·
                  refine ⟨1544280516647838097968883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2059040688863784130625177 1544280516647838097968883)
                  ·
                    refine ⟨2316420774971757146953325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1544280516647838097968883 2316420774971757146953325)
                    ·
                      refine ⟨868657790614408930107497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2316420774971757146953325 868657790614408930107497)
                      ·
                        rfl

theorem cell23_1691705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_1691705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691705 prefixEnd_1691705 := by exact prefixLift 1691705
  have htrace : WordTrace (prefixWord ++ tailWord_1691705) baseStart_1691705 baseEnd_1691705 := by
    simpa [prefixWord, tailWord_1691705, baseEnd_1691705] using wordTrace_append hprefix tailTrace_1691705
  have hstable : (prefixWord ++ tailWord_1691705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691705).length < 2 ^ (prefixWord ++ tailWord_1691705).sum := by decide
  have hdescent : baseEnd_1691705 < baseStart_1691705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691747 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 2, 5]
def baseStart_1691747 : Nat := 118140960795 + 1691747 * 2 ^ 59
def prefixEnd_1691747 : Nat := 4983230072969 + 3 ^ 40 * 1691747 * 2
def baseEnd_1691747 : Nat := 289559785600632588594101

theorem tailTrace_1691747 : CollatzResearch.WordTrace tailWord_1691747 prefixEnd_1691747 289559785600632588594101 := by
  unfold tailWord_1691747
  simp only [CollatzResearch.WordTrace]
  refine ⟨61703082202097021230025495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41135388134731347486683663 61703082202097021230025495)
  ·
    refine ⟨92554623303145531845038243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61703082202097021230025495 92554623303145531845038243)
    ·
      refine ⟨138831934954718297767557365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92554623303145531845038243 138831934954718297767557365)
      ·
        refine ⟨13015493902004840415708503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138831934954718297767557365 13015493902004840415708503)
        ·
          refine ⟨19523240853007260623562755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13015493902004840415708503 19523240853007260623562755)
          ·
            refine ⟨29284861279510890935344133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19523240853007260623562755 29284861279510890935344133)
            ·
              refine ⟨5490911489908292050377025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29284861279510890935344133 5490911489908292050377025)
              ·
                refine ⟨4118183617431219037782769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5490911489908292050377025 4118183617431219037782769)
                ·
                  refine ⟨3088637713073414278337077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4118183617431219037782769 3088637713073414278337077)
                  ·
                    refine ⟨289559785600632588594101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3088637713073414278337077 289559785600632588594101)
                    ·
                      rfl

theorem cell23_1691747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 5].length) (baseStart_1691747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691747 prefixEnd_1691747 := by exact prefixLift 1691747
  have htrace : WordTrace (prefixWord ++ tailWord_1691747) baseStart_1691747 baseEnd_1691747 := by
    simpa [prefixWord, tailWord_1691747, baseEnd_1691747] using wordTrace_append hprefix tailTrace_1691747
  have hstable : (prefixWord ++ tailWord_1691747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691747).length < 2 ^ (prefixWord ++ tailWord_1691747).sum := by decide
  have hdescent : baseEnd_1691747 < baseStart_1691747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691757 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1691757 : Nat := 118140960795 + 1691757 * 2 ^ 59
def prefixEnd_1691757 : Nat := 4983230072969 + 3 ^ 40 * 1691757 * 2
def baseEnd_1691757 : Nat := 868684491608442726657257

theorem tailTrace_1691757 : CollatzResearch.WordTrace tailWord_1691757 prefixEnd_1691757 868684491608442726657257 := by
  unfold tailWord_1691757
  simp only [CollatzResearch.WordTrace]
  refine ⟨61703446932060792937889525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41135631288040528625259683 61703446932060792937889525)
  ·
    refine ⟨5784698149880699337927143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61703446932060792937889525 5784698149880699337927143)
    ·
      refine ⟨8677047224821049006890715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5784698149880699337927143 8677047224821049006890715)
      ·
        refine ⟨13015570837231573510336073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8677047224821049006890715 13015570837231573510336073)
        ·
          refine ⟨9761678127923680132752055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13015570837231573510336073 9761678127923680132752055)
          ·
            refine ⟨14642517191885520199128083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9761678127923680132752055 14642517191885520199128083)
            ·
              refine ⟨21963775787828280298692125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14642517191885520199128083 21963775787828280298692125)
              ·
                refine ⟨8236415920435605112009547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21963775787828280298692125 8236415920435605112009547)
                ·
                  refine ⟨12354623880653407668014321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8236415920435605112009547 12354623880653407668014321)
                  ·
                    refine ⟨9265967910490055751010741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12354623880653407668014321 9265967910490055751010741)
                    ·
                      refine ⟨868684491608442726657257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9265967910490055751010741 868684491608442726657257)
                      ·
                        rfl

theorem cell23_1691757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1691757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691757 prefixEnd_1691757 := by exact prefixLift 1691757
  have htrace : WordTrace (prefixWord ++ tailWord_1691757) baseStart_1691757 baseEnd_1691757 := by
    simpa [prefixWord, tailWord_1691757, baseEnd_1691757] using wordTrace_append hprefix tailTrace_1691757
  have hstable : (prefixWord ++ tailWord_1691757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691757).length < 2 ^ (prefixWord ++ tailWord_1691757).sum := by decide
  have hdescent : baseEnd_1691757 < baseStart_1691757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691784 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1691784 : Nat := 118140960795 + 1691784 * 2 ^ 59
def prefixEnd_1691784 : Nat := 4983230072969 + 3 ^ 40 * 1691784 * 2
def baseEnd_1691784 : Nat := 868698355586114121019633

theorem tailTrace_1691784 : CollatzResearch.WordTrace tailWord_1691784 prefixEnd_1691784 868698355586114121019633 := by
  unfold tailWord_1691784
  simp only [CollatzResearch.WordTrace]
  refine ⟨30852215851481488274561203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41136287801975317699414937 30852215851481488274561203)
  ·
    refine ⟨46278323777222232411841805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30852215851481488274561203 46278323777222232411841805)
    ·
      refine ⟨17354371416458337154440677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46278323777222232411841805 17354371416458337154440677)
      ·
        refine ⟨3253944640585938216457627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17354371416458337154440677 3253944640585938216457627)
        ·
          refine ⟨4880916960878907324686441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253944640585938216457627 4880916960878907324686441)
          ·
            refine ⟨3660687720659180493514831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4880916960878907324686441 3660687720659180493514831)
            ·
              refine ⟨5491031580988770740272247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660687720659180493514831 5491031580988770740272247)
              ·
                refine ⟨8236547371483156110408371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491031580988770740272247 8236547371483156110408371)
                ·
                  refine ⟨12354821057224734165612557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8236547371483156110408371 12354821057224734165612557)
                  ·
                    refine ⟨4633057896459275312104709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12354821057224734165612557 4633057896459275312104709)
                    ·
                      refine ⟨868698355586114121019633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4633057896459275312104709 868698355586114121019633)
                      ·
                        rfl

theorem cell23_1691784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1691784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691784 prefixEnd_1691784 := by exact prefixLift 1691784
  have htrace : WordTrace (prefixWord ++ tailWord_1691784) baseStart_1691784 baseEnd_1691784 := by
    simpa [prefixWord, tailWord_1691784, baseEnd_1691784] using wordTrace_append hprefix tailTrace_1691784
  have hstable : (prefixWord ++ tailWord_1691784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691784).length < 2 ^ (prefixWord ++ tailWord_1691784).sum := by decide
  have hdescent : baseEnd_1691784 < baseStart_1691784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691794 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1691794 : Nat := 118140960795 + 1691794 * 2 ^ 59
def prefixEnd_1691794 : Nat := 4983230072969 + 3 ^ 40 * 1691794 * 2
def baseEnd_1691794 : Nat := 289567830130886360631529

theorem tailTrace_1691794 : CollatzResearch.WordTrace tailWord_1691794 prefixEnd_1691794 289567830130886360631529 := by
  unfold tailWord_1691794
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426199108231687064246609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41136530955284498837990957 15426199108231687064246609)
  ·
    refine ⟨11569649331173765298184957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15426199108231687064246609 11569649331173765298184957)
    ·
      refine ⟨4338618499190161986819359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11569649331173765298184957 4338618499190161986819359)
      ·
        refine ⟨6507927748785242980229039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338618499190161986819359 6507927748785242980229039)
        ·
          refine ⟨9761891623177864470343559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507927748785242980229039 9761891623177864470343559)
          ·
            refine ⟨14642837434766796705515339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9761891623177864470343559 14642837434766796705515339)
            ·
              refine ⟨21964256152150195058273009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14642837434766796705515339 21964256152150195058273009)
              ·
                refine ⟨16473192114112646293704757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21964256152150195058273009 16473192114112646293704757)
                ·
                  refine ⟨1544361760698060590034821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16473192114112646293704757 1544361760698060590034821)
                  ·
                    refine ⟨289567830130886360631529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1544361760698060590034821 289567830130886360631529)
                    ·
                      rfl

theorem cell23_1691794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1691794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691794 prefixEnd_1691794 := by exact prefixLift 1691794
  have htrace : WordTrace (prefixWord ++ tailWord_1691794) baseStart_1691794 baseEnd_1691794 := by
    simpa [prefixWord, tailWord_1691794, baseEnd_1691794] using wordTrace_append hprefix tailTrace_1691794
  have hstable : (prefixWord ++ tailWord_1691794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691794).length < 2 ^ (prefixWord ++ tailWord_1691794).sum := by decide
  have hdescent : baseEnd_1691794 < baseStart_1691794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691804 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1691804 : Nat := 118140960795 + 1691804 * 2 ^ 59
def prefixEnd_1691804 : Nat := 4983230072969 + 3 ^ 40 * 1691804 * 2
def baseEnd_1691804 : Nat := 868708625199204042769541

theorem tailTrace_1691804 : CollatzResearch.WordTrace tailWord_1691804 prefixEnd_1691804 868708625199204042769541 := by
  unfold tailWord_1691804
  simp only [CollatzResearch.WordTrace]
  refine ⟨30852580581445259982425233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41136774108593679976566977 30852580581445259982425233)
  ·
    refine ⟨23139435436083944986818925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30852580581445259982425233 23139435436083944986818925)
    ·
      refine ⟨8677288288531479370057097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23139435436083944986818925 8677288288531479370057097)
      ·
        refine ⟨6507966216398609527542823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8677288288531479370057097 6507966216398609527542823)
        ·
          refine ⟨9761949324597914291314235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507966216398609527542823 9761949324597914291314235)
          ·
            refine ⟨14642923986896871436971353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9761949324597914291314235 14642923986896871436971353)
            ·
              refine ⟨10982192990172653577728515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14642923986896871436971353 10982192990172653577728515)
              ·
                refine ⟨16473289485258980366592773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10982192990172653577728515 16473289485258980366592773)
                ·
                  refine ⟨3088741778486058818736145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16473289485258980366592773 3088741778486058818736145)
                  ·
                    refine ⟨2316556333864544114052109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3088741778486058818736145 2316556333864544114052109)
                    ·
                      refine ⟨868708625199204042769541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2316556333864544114052109 868708625199204042769541)
                      ·
                        rfl

theorem cell23_1691804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1691804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691804 prefixEnd_1691804 := by exact prefixLift 1691804
  have htrace : WordTrace (prefixWord ++ tailWord_1691804) baseStart_1691804 baseEnd_1691804 := by
    simpa [prefixWord, tailWord_1691804, baseEnd_1691804] using wordTrace_append hprefix tailTrace_1691804
  have hstable : (prefixWord ++ tailWord_1691804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691804).length < 2 ^ (prefixWord ++ tailWord_1691804).sum := by decide
  have hdescent : baseEnd_1691804 < baseStart_1691804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691862 : List Nat := [5, 2, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1691862 : Nat := 118140960795 + 1691862 * 2 ^ 59
def prefixEnd_1691862 : Nat := 4983230072969 + 3 ^ 40 * 1691862 * 2
def baseEnd_1691862 : Nat := 289579469025721605281425

theorem tailTrace_1691862 : CollatzResearch.WordTrace tailWord_1691862 prefixEnd_1691862 289579469025721605281425 := by
  unfold tailWord_1691862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856704787292524741903865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41138184397786930580307893 3856704787292524741903865)
  ·
    refine ⟨2892528590469393556427899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3856704787292524741903865 2892528590469393556427899)
    ·
      refine ⟨4338792885704090334641849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2892528590469393556427899 4338792885704090334641849)
      ·
        refine ⟨3254094664278067750981387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4338792885704090334641849 3254094664278067750981387)
        ·
          refine ⟨4881141996417101626472081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254094664278067750981387 4881141996417101626472081)
          ·
            refine ⟨3660856497312826219854061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4881141996417101626472081 3660856497312826219854061)
            ·
              refine ⟨1372821186492309832445273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3660856497312826219854061 1372821186492309832445273)
              ·
                refine ⟨1029615889869232374333955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372821186492309832445273 1029615889869232374333955)
                ·
                  refine ⟨1544423834803848561500933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029615889869232374333955 1544423834803848561500933)
                  ·
                    refine ⟨289579469025721605281425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1544423834803848561500933 289579469025721605281425)
                    ·
                      rfl

theorem cell23_1691862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1691862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691862 prefixEnd_1691862 := by exact prefixLift 1691862
  have htrace : WordTrace (prefixWord ++ tailWord_1691862) baseStart_1691862 baseEnd_1691862 := by
    simpa [prefixWord, tailWord_1691862, baseEnd_1691862] using wordTrace_append hprefix tailTrace_1691862
  have hstable : (prefixWord ++ tailWord_1691862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691862).length < 2 ^ (prefixWord ++ tailWord_1691862).sum := by decide
  have hdescent : baseEnd_1691862 < baseStart_1691862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691875 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 6]
def baseStart_1691875 : Nat := 118140960795 + 1691875 * 2 ^ 59
def prefixEnd_1691875 : Nat := 4983230072969 + 3 ^ 40 * 1691875 * 2
def baseEnd_1691875 : Nat := 96527231369519251664635

theorem tailTrace_1691875 : CollatzResearch.WordTrace tailWord_1691875 prefixEnd_1691875 96527231369519251664635 := by
  unfold tailWord_1691875
  simp only [CollatzResearch.WordTrace]
  refine ⟨61707750745633299090685079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41138500497088866060456719 61707750745633299090685079)
  ·
    refine ⟨92561626118449948636027619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61707750745633299090685079 92561626118449948636027619)
    ·
      refine ⟨138842439177674922954041429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92561626118449948636027619 138842439177674922954041429)
      ·
        refine ⟨1627059834113378003367673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 138842439177674922954041429 1627059834113378003367673)
        ·
          refine ⟨1220294875585033502525755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1627059834113378003367673 1220294875585033502525755)
          ·
            refine ⟨1830442313377550253788633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220294875585033502525755 1830442313377550253788633)
            ·
              refine ⟨1372831735033162690341475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830442313377550253788633 1372831735033162690341475)
              ·
                refine ⟨2059247602549744035512213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372831735033162690341475 2059247602549744035512213)
                ·
                  refine ⟨96527231369519251664635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2059247602549744035512213 96527231369519251664635)
                  ·
                    rfl

theorem cell23_1691875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 6].length) (baseStart_1691875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691875 prefixEnd_1691875 := by exact prefixLift 1691875
  have htrace : WordTrace (prefixWord ++ tailWord_1691875) baseStart_1691875 baseEnd_1691875 := by
    simpa [prefixWord, tailWord_1691875, baseEnd_1691875] using wordTrace_append hprefix tailTrace_1691875
  have hstable : (prefixWord ++ tailWord_1691875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691875).length < 2 ^ (prefixWord ++ tailWord_1691875).sum := by decide
  have hdescent : baseEnd_1691875 < baseStart_1691875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691891 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 5, 2, 2]
def baseStart_1691891 : Nat := 118140960795 + 1691891 * 2 ^ 59
def prefixEnd_1691891 : Nat := 4983230072969 + 3 ^ 40 * 1691891 * 2
def baseEnd_1691891 : Nat := 868753298016145202381641

theorem tailTrace_1691891 : CollatzResearch.WordTrace tailWord_1691891 prefixEnd_1691891 868753298016145202381641 := by
  unfold tailWord_1691891
  simp only [CollatzResearch.WordTrace]
  refine ⟨61708334313575333823267527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41138889542383555882178351 61708334313575333823267527)
  ·
    refine ⟨92562501470363000734901291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61708334313575333823267527 92562501470363000734901291)
    ·
      refine ⟨138843752205544501102351937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92562501470363000734901291 138843752205544501102351937)
      ·
        refine ⟨104132814154158375826763953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138843752205544501102351937 104132814154158375826763953)
        ·
          refine ⟨78099610615618781870072965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104132814154158375826763953 78099610615618781870072965)
          ·
            refine ⟨14643676990428521600638681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78099610615618781870072965 14643676990428521600638681)
            ·
              refine ⟨10982757742821391200479011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14643676990428521600638681 10982757742821391200479011)
              ·
                refine ⟨16474136614232086800718517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10982757742821391200479011 16474136614232086800718517)
                ·
                  refine ⟨1544450307584258137567361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16474136614232086800718517 1544450307584258137567361)
                  ·
                    refine ⟨1158337730688193603175521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1544450307584258137567361 1158337730688193603175521)
                    ·
                      refine ⟨868753298016145202381641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158337730688193603175521 868753298016145202381641)
                      ·
                        rfl

theorem cell23_1691891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 2, 2].length) (baseStart_1691891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691891 prefixEnd_1691891 := by exact prefixLift 1691891
  have htrace : WordTrace (prefixWord ++ tailWord_1691891) baseStart_1691891 baseEnd_1691891 := by
    simpa [prefixWord, tailWord_1691891, baseEnd_1691891] using wordTrace_append hprefix tailTrace_1691891
  have hstable : (prefixWord ++ tailWord_1691891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691891).length < 2 ^ (prefixWord ++ tailWord_1691891).sum := by decide
  have hdescent : baseEnd_1691891 < baseStart_1691891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691894 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1691894 : Nat := 118140960795 + 1691894 * 2 ^ 59
def prefixEnd_1691894 : Nat := 4983230072969 + 3 ^ 40 * 1691894 * 2
def baseEnd_1691894 : Nat := 868754838458108690644127

theorem tailTrace_1691894 : CollatzResearch.WordTrace tailWord_1691894 prefixEnd_1691894 868754838458108690644127 := by
  unfold tailWord_1691894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856777733285279083476671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41138962488376310223751157 3856777733285279083476671)
  ·
    refine ⟨5785166599927918625215007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3856777733285279083476671 5785166599927918625215007)
    ·
      refine ⟨8677749899891877937822511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5785166599927918625215007 8677749899891877937822511)
      ·
        refine ⟨13016624849837816906733767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8677749899891877937822511 13016624849837816906733767)
        ·
          refine ⟨19524937274756725360100651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13016624849837816906733767 19524937274756725360100651)
          ·
            refine ⟨29287405912135088040150977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19524937274756725360100651 29287405912135088040150977)
            ·
              refine ⟨21965554434101316030113233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29287405912135088040150977 21965554434101316030113233)
              ·
                refine ⟨16474165825575987022584925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21965554434101316030113233 16474165825575987022584925)
                ·
                  refine ⟨6177812184590995133469347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16474165825575987022584925 6177812184590995133469347)
                  ·
                    refine ⟨9266718276886492700204021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6177812184590995133469347 9266718276886492700204021)
                    ·
                      refine ⟨868754838458108690644127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9266718276886492700204021 868754838458108690644127)
                      ·
                        rfl

theorem cell23_1691894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1691894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691894 prefixEnd_1691894 := by exact prefixLift 1691894
  have htrace : WordTrace (prefixWord ++ tailWord_1691894) baseStart_1691894 baseEnd_1691894 := by
    simpa [prefixWord, tailWord_1691894, baseEnd_1691894] using wordTrace_append hprefix tailTrace_1691894
  have hstable : (prefixWord ++ tailWord_1691894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691894).length < 2 ^ (prefixWord ++ tailWord_1691894).sum := by decide
  have hdescent : baseEnd_1691894 < baseStart_1691894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691951 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 3, 3, 2]
def baseStart_1691951 : Nat := 118140960795 + 1691951 * 2 ^ 59
def prefixEnd_1691951 : Nat := 4983230072969 + 3 ^ 40 * 1691951 * 2
def baseEnd_1691951 : Nat := 868784106855414967631365

theorem tailTrace_1691951 : CollatzResearch.WordTrace tailWord_1691951 prefixEnd_1691951 868784106855414967631365 := by
  unfold tailWord_1691951
  simp only [CollatzResearch.WordTrace]
  refine ⟨61710522693357964070451707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41140348462238642713634471 61710522693357964070451707)
  ·
    refine ⟨92565784040036946105677561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61710522693357964070451707 92565784040036946105677561)
    ·
      refine ⟨69424338030027709579258171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92565784040036946105677561 69424338030027709579258171)
      ·
        refine ⟨104136507045041564368887257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69424338030027709579258171 104136507045041564368887257)
        ·
          refine ⟨78102380283781173276665443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104136507045041564368887257 78102380283781173276665443)
          ·
            refine ⟨117153570425671759914998165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78102380283781173276665443 117153570425671759914998165)
            ·
              refine ⟨5491573613703363746015539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117153570425671759914998165 5491573613703363746015539)
              ·
                refine ⟨8237360420555045619023309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491573613703363746015539 8237360420555045619023309)
                ·
                  refine ⟨3089010157708142107133741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8237360420555045619023309 3089010157708142107133741)
                  ·
                    refine ⟨1158378809140553290175153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089010157708142107133741 1158378809140553290175153)
                    ·
                      refine ⟨868784106855414967631365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158378809140553290175153 868784106855414967631365)
                      ·
                        rfl

theorem cell23_1691951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 3, 2].length) (baseStart_1691951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691951 prefixEnd_1691951 := by exact prefixLift 1691951
  have htrace : WordTrace (prefixWord ++ tailWord_1691951) baseStart_1691951 baseEnd_1691951 := by
    simpa [prefixWord, tailWord_1691951, baseEnd_1691951] using wordTrace_append hprefix tailTrace_1691951
  have hstable : (prefixWord ++ tailWord_1691951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691951).length < 2 ^ (prefixWord ++ tailWord_1691951).sum := by decide
  have hdescent : baseEnd_1691951 < baseStart_1691951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692004 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 7]
def baseStart_1692004 : Nat := 118140960795 + 1692004 * 2 ^ 59
def prefixEnd_1692004 : Nat := 4983230072969 + 3 ^ 40 * 1692004 * 2
def baseEnd_1692004 : Nat := 96534591258900362252069

theorem tailTrace_1692004 : CollatzResearch.WordTrace tailWord_1692004 prefixEnd_1692004 96534591258900362252069 := by
  unfold tailWord_1692004
  simp only [CollatzResearch.WordTrace]
  refine ⟨30856227881082977061065533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41141637174777302748087377 30856227881082977061065533)
  ·
    refine ⟨11571085455406116397899575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30856227881082977061065533 11571085455406116397899575)
    ·
      refine ⟨17356628183109174596849363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11571085455406116397899575 17356628183109174596849363)
      ·
        refine ⟨26034942274663761895274045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17356628183109174596849363 26034942274663761895274045)
        ·
          refine ⟨9763103352998910710727767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26034942274663761895274045 9763103352998910710727767)
          ·
            refine ⟨14644655029498366066091651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9763103352998910710727767 14644655029498366066091651)
            ·
              refine ⟨21966982544247549099137477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14644655029498366066091651 21966982544247549099137477)
              ·
                refine ⟨4118809227046415456088277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21966982544247549099137477 4118809227046415456088277)
                ·
                  refine ⟨96534591258900362252069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4118809227046415456088277 96534591258900362252069)
                  ·
                    rfl

theorem cell23_1692004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_1692004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692004 prefixEnd_1692004 := by exact prefixLift 1692004
  have htrace : WordTrace (prefixWord ++ tailWord_1692004) baseStart_1692004 baseEnd_1692004 := by
    simpa [prefixWord, tailWord_1692004, baseEnd_1692004] using wordTrace_append hprefix tailTrace_1692004
  have hstable : (prefixWord ++ tailWord_1692004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692004).length < 2 ^ (prefixWord ++ tailWord_1692004).sum := by decide
  have hdescent : baseEnd_1692004 < baseStart_1692004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692044 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1692044 : Nat := 118140960795 + 1692044 * 2 ^ 59
def prefixEnd_1692044 : Nat := 4983230072969 + 3 ^ 40 * 1692044 * 2
def baseEnd_1692044 : Nat := 868831860556283103768437

theorem tailTrace_1692044 : CollatzResearch.WordTrace tailWord_1692044 prefixEnd_1692044 868831860556283103768437 := by
  unfold tailWord_1692044
  simp only [CollatzResearch.WordTrace]
  refine ⟨30856957341010520476793593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41142609788014027302391457 30856957341010520476793593)
  ·
    refine ⟨23142718005757890357595195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30856957341010520476793593 23142718005757890357595195)
    ·
      refine ⟨34714077008636835536392793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23142718005757890357595195 34714077008636835536392793)
      ·
        refine ⟨26035557756477626652294595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34714077008636835536392793 26035557756477626652294595)
        ·
          refine ⟨39053336634716439978441893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26035557756477626652294595 39053336634716439978441893)
          ·
            refine ⟨7322500619009332495957855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39053336634716439978441893 7322500619009332495957855)
            ·
              refine ⟨10983750928513998743936783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7322500619009332495957855 10983750928513998743936783)
              ·
                refine ⟨16475626392770998115905175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10983750928513998743936783 16475626392770998115905175)
                ·
                  refine ⟨24713439589156497173857763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16475626392770998115905175 24713439589156497173857763)
                  ·
                    refine ⟨37070159383734745760786645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24713439589156497173857763 37070159383734745760786645)
                    ·
                      refine ⟨868831860556283103768437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37070159383734745760786645 868831860556283103768437)
                      ·
                        rfl

theorem cell23_1692044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1692044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692044 prefixEnd_1692044 := by exact prefixLift 1692044
  have htrace : WordTrace (prefixWord ++ tailWord_1692044) baseStart_1692044 baseEnd_1692044 := by
    simpa [prefixWord, tailWord_1692044, baseEnd_1692044] using wordTrace_append hprefix tailTrace_1692044
  have hstable : (prefixWord ++ tailWord_1692044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692044).length < 2 ^ (prefixWord ++ tailWord_1692044).sum := by decide
  have hdescent : baseEnd_1692044 < baseStart_1692044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692162 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1692162 : Nat := 118140960795 + 1692162 * 2 ^ 59
def prefixEnd_1692162 : Nat := 4983230072969 + 3 ^ 40 * 1692162 * 2
def baseEnd_1692162 : Nat := 96543605697057071343655

theorem tailTrace_1692162 : CollatzResearch.WordTrace tailWord_1692162 prefixEnd_1692162 96543605697057071343655 := by
  unfold tailWord_1692162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429554623898386776595685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41145478997062364737588493 15429554623898386776595685)
  ·
    refine ⟨2893041491980947520611691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15429554623898386776595685 2893041491980947520611691)
    ·
      refine ⟨4339562237971421280917537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2893041491980947520611691 4339562237971421280917537)
      ·
        refine ⟨3254671678478565960688153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4339562237971421280917537 3254671678478565960688153)
        ·
          refine ⟨2441003758858924470516115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3254671678478565960688153 2441003758858924470516115)
          ·
            refine ⟨3661505638288386705774173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441003758858924470516115 3661505638288386705774173)
            ·
              refine ⟨1373064614358145014665315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3661505638288386705774173 1373064614358145014665315)
              ·
                refine ⟨2059596921537217521997973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373064614358145014665315 2059596921537217521997973)
                ·
                  refine ⟨96543605697057071343655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2059596921537217521997973 96543605697057071343655)
                  ·
                    rfl

theorem cell23_1692162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1692162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692162 prefixEnd_1692162 := by exact prefixLift 1692162
  have htrace : WordTrace (prefixWord ++ tailWord_1692162) baseStart_1692162 baseEnd_1692162 := by
    simpa [prefixWord, tailWord_1692162, baseEnd_1692162] using wordTrace_append hprefix tailTrace_1692162
  have hstable : (prefixWord ++ tailWord_1692162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692162).length < 2 ^ (prefixWord ++ tailWord_1692162).sum := by decide
  have hdescent : baseEnd_1692162 < baseStart_1692162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692181 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_1692181 : Nat := 118140960795 + 1692181 * 2 ^ 59
def prefixEnd_1692181 : Nat := 4983230072969 + 3 ^ 40 * 1692181 * 2
def baseEnd_1692181 : Nat := 868902207405949067755307

theorem tailTrace_1692181 : CollatzResearch.WordTrace tailWord_1692181 prefixEnd_1692181 868902207405949067755307 := by
  unfold tailWord_1692181
  simp only [CollatzResearch.WordTrace]
  refine ⟨61718911482524713351324397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41145940988349808900882931 61718911482524713351324397)
  ·
    refine ⟨23144591805946767506746649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61718911482524713351324397 23144591805946767506746649)
    ·
      refine ⟨17358443854460075630059987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23144591805946767506746649 17358443854460075630059987)
      ·
        refine ⟨26037665781690113445089981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17358443854460075630059987 26037665781690113445089981)
        ·
          refine ⟨9764124668133792541908743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26037665781690113445089981 9764124668133792541908743)
          ·
            refine ⟨14646187002200688812863115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764124668133792541908743 14646187002200688812863115)
            ·
              refine ⟨21969280503301033219294673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14646187002200688812863115 21969280503301033219294673)
              ·
                refine ⟨16476960377475774914471005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21969280503301033219294673 16476960377475774914471005)
                ·
                  refine ⟨6178860141553415592926627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16476960377475774914471005 6178860141553415592926627)
                  ·
                    refine ⟨9268290212330123389389941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6178860141553415592926627 9268290212330123389389941)
                    ·
                      refine ⟨868902207405949067755307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9268290212330123389389941 868902207405949067755307)
                      ·
                        rfl

theorem cell23_1692181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_1692181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692181 prefixEnd_1692181 := by exact prefixLift 1692181
  have htrace : WordTrace (prefixWord ++ tailWord_1692181) baseStart_1692181 baseEnd_1692181 := by
    simpa [prefixWord, tailWord_1692181, baseEnd_1692181] using wordTrace_append hprefix tailTrace_1692181
  have hstable : (prefixWord ++ tailWord_1692181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692181).length < 2 ^ (prefixWord ++ tailWord_1692181).sum := by decide
  have hdescent : baseEnd_1692181 < baseStart_1692181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692188 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1692188 : Nat := 118140960795 + 1692188 * 2 ^ 59
def prefixEnd_1692188 : Nat := 4983230072969 + 3 ^ 40 * 1692188 * 2
def baseEnd_1692188 : Nat := 289635267256843513455925

theorem tailTrace_1692188 : CollatzResearch.WordTrace tailWord_1692188 prefixEnd_1692188 289635267256843513455925 := by
  unfold tailWord_1692188
  simp only [CollatzResearch.WordTrace]
  refine ⟨30859583396749676773414609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41146111195666235697886145 30859583396749676773414609)
  ·
    refine ⟨23144687547562257580060957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30859583396749676773414609 23144687547562257580060957)
    ·
      refine ⟨8679257830335846592522859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23144687547562257580060957 8679257830335846592522859)
      ·
        refine ⟨13018886745503769888784289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8679257830335846592522859 13018886745503769888784289)
        ·
          refine ⟨9764165059127827416588217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13018886745503769888784289 9764165059127827416588217)
          ·
            refine ⟨7323123794345870562441163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9764165059127827416588217 7323123794345870562441163)
            ·
              refine ⟨10984685691518805843661745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323123794345870562441163 10984685691518805843661745)
              ·
                refine ⟨8238514268639104382746309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10984685691518805843661745 8238514268639104382746309)
                ·
                  refine ⟨1544721425369832071764933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8238514268639104382746309 1544721425369832071764933)
                  ·
                    refine ⟨289635267256843513455925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1544721425369832071764933 289635267256843513455925)
                    ·
                      rfl

theorem cell23_1692188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1692188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692188 prefixEnd_1692188 := by exact prefixLift 1692188
  have htrace : WordTrace (prefixWord ++ tailWord_1692188) baseStart_1692188 baseEnd_1692188 := by
    simpa [prefixWord, tailWord_1692188, baseEnd_1692188] using wordTrace_append hprefix tailTrace_1692188
  have hstable : (prefixWord ++ tailWord_1692188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692188).length < 2 ^ (prefixWord ++ tailWord_1692188).sum := by decide
  have hdescent : baseEnd_1692188 < baseStart_1692188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692189 : List Nat := [1, 4, 2, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_1692189 : Nat := 118140960795 + 1692189 * 2 ^ 59
def prefixEnd_1692189 : Nat := 4983230072969 + 3 ^ 40 * 1692189 * 2
def baseEnd_1692189 : Nat := 868906315251185036455271

theorem tailTrace_1692189 : CollatzResearch.WordTrace tailWord_1692189 prefixEnd_1692189 868906315251185036455271 := by
  unfold tailWord_1692189
  simp only [CollatzResearch.WordTrace]
  refine ⟨61719203266495730717615621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41146135510997153811743747 61719203266495730717615621)
  ·
    refine ⟨11572350612467949509552929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61719203266495730717615621 11572350612467949509552929)
    ·
      refine ⟨8679262959350962132164697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11572350612467949509552929 8679262959350962132164697)
      ·
        refine ⟨6509447219513221599123523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8679262959350962132164697 6509447219513221599123523)
        ·
          refine ⟨9764170829269832398685285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6509447219513221599123523 9764170829269832398685285)
          ·
            refine ⟨1830782030488093574753491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9764170829269832398685285 1830782030488093574753491)
            ·
              refine ⟨2746173045732140362130237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830782030488093574753491 2746173045732140362130237)
              ·
                refine ⟨1029814892149552635798839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2746173045732140362130237 1029814892149552635798839)
                ·
                  refine ⟨1544722338224328953698259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029814892149552635798839 1544722338224328953698259)
                  ·
                    refine ⟨2317083507336493430547389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1544722338224328953698259 2317083507336493430547389)
                    ·
                      refine ⟨868906315251185036455271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2317083507336493430547389 868906315251185036455271)
                      ·
                        rfl

theorem cell23_1692189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_1692189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692189 prefixEnd_1692189 := by exact prefixLift 1692189
  have htrace : WordTrace (prefixWord ++ tailWord_1692189) baseStart_1692189 baseEnd_1692189 := by
    simpa [prefixWord, tailWord_1692189, baseEnd_1692189] using wordTrace_append hprefix tailTrace_1692189
  have hstable : (prefixWord ++ tailWord_1692189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692189).length < 2 ^ (prefixWord ++ tailWord_1692189).sum := by decide
  have hdescent : baseEnd_1692189 < baseStart_1692189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692191 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1692191 : Nat := 118140960795 + 1692191 * 2 ^ 59
def prefixEnd_1692191 : Nat := 4983230072969 + 3 ^ 40 * 1692191 * 2
def baseEnd_1692191 : Nat := 868907342212494028630261

theorem tailTrace_1692191 : CollatzResearch.WordTrace tailWord_1692191 prefixEnd_1692191 868907342212494028630261 := by
  unfold tailWord_1692191
  simp only [CollatzResearch.WordTrace]
  refine ⟨61719276212488485059188427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41146184141658990039458951 61719276212488485059188427)
  ·
    refine ⟨92578914318732727588782641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61719276212488485059188427 92578914318732727588782641)
    ·
      refine ⟨69434185739049545691586981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92578914318732727588782641 69434185739049545691586981)
      ·
        refine ⟨13018909826071789817172559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69434185739049545691586981 13018909826071789817172559)
        ·
          refine ⟨19528364739107684725758839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13018909826071789817172559 19528364739107684725758839)
          ·
            refine ⟨29292547108661527088638259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19528364739107684725758839 29292547108661527088638259)
            ·
              refine ⟨43938820662992290632957389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29292547108661527088638259 43938820662992290632957389)
              ·
                refine ⟨16477057748622108987359021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43938820662992290632957389 16477057748622108987359021)
                ·
                  refine ⟨6178896655733290870259633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16477057748622108987359021 6178896655733290870259633)
                  ·
                    refine ⟨4634172491799968152694725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178896655733290870259633 4634172491799968152694725)
                    ·
                      refine ⟨868907342212494028630261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4634172491799968152694725 868907342212494028630261)
                      ·
                        rfl

theorem cell23_1692191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1692191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692191 prefixEnd_1692191 := by exact prefixLift 1692191
  have htrace : WordTrace (prefixWord ++ tailWord_1692191) baseStart_1692191 baseEnd_1692191 := by
    simpa [prefixWord, tailWord_1692191, baseEnd_1692191] using wordTrace_append hprefix tailTrace_1692191
  have hstable : (prefixWord ++ tailWord_1692191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692191).length < 2 ^ (prefixWord ++ tailWord_1692191).sum := by decide
  have hdescent : baseEnd_1692191 < baseStart_1692191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692199 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1692199 : Nat := 118140960795 + 1692199 * 2 ^ 59
def prefixEnd_1692199 : Nat := 4983230072969 + 3 ^ 40 * 1692199 * 2
def baseEnd_1692199 : Nat := 868911450057729997330225

theorem tailTrace_1692199 : CollatzResearch.WordTrace tailWord_1692199 prefixEnd_1692199 868911450057729997330225 := by
  unfold tailWord_1692199
  simp only [CollatzResearch.WordTrace]
  refine ⟨61719567996459502425479651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41146378664306334950319767 61719567996459502425479651)
  ·
    refine ⟨92579351994689253638219477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61719567996459502425479651 92579351994689253638219477)
    ·
      refine ⟨2169828562375529382145769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 92579351994689253638219477 2169828562375529382145769)
      ·
        refine ⟨1627371421781647036609327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2169828562375529382145769 1627371421781647036609327)
        ·
          refine ⟨2441057132672470554913991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627371421781647036609327 2441057132672470554913991)
          ·
            refine ⟨3661585699008705832370987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441057132672470554913991 3661585699008705832370987)
            ·
              refine ⟨5492378548513058748556481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661585699008705832370987 5492378548513058748556481)
              ·
                refine ⟨4119283911384794061417361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492378548513058748556481 4119283911384794061417361)
                ·
                  refine ⟨3089462933538595546063021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4119283911384794061417361 3089462933538595546063021)
                  ·
                    refine ⟨1158548600076973329773633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089462933538595546063021 1158548600076973329773633)
                    ·
                      refine ⟨868911450057729997330225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158548600076973329773633 868911450057729997330225)
                      ·
                        rfl

theorem cell23_1692199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1692199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692199 prefixEnd_1692199 := by exact prefixLift 1692199
  have htrace : WordTrace (prefixWord ++ tailWord_1692199) baseStart_1692199 baseEnd_1692199 := by
    simpa [prefixWord, tailWord_1692199, baseEnd_1692199] using wordTrace_append hprefix tailTrace_1692199
  have hstable : (prefixWord ++ tailWord_1692199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692199).length < 2 ^ (prefixWord ++ tailWord_1692199).sum := by decide
  have hdescent : baseEnd_1692199 < baseStart_1692199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692206 : List Nat := [4, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_1692206 : Nat := 118140960795 + 1692206 * 2 ^ 59
def prefixEnd_1692206 : Nat := 4983230072969 + 3 ^ 40 * 1692206 * 2
def baseEnd_1692206 : Nat := 868915044422311469942693

theorem tailTrace_1692206 : CollatzResearch.WordTrace tailWord_1692206 prefixEnd_1692206 868915044422311469942693 := by
  unfold tailWord_1692206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714977913429267827623059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41146548871622761747322981 7714977913429267827623059)
  ·
    refine ⟨11572466870143901741434589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7714977913429267827623059 11572466870143901741434589)
    ·
      refine ⟨4339675076303963153037971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11572466870143901741434589 4339675076303963153037971)
      ·
        refine ⟨6509512614455944729556957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339675076303963153037971 6509512614455944729556957)
        ·
          refine ⟨2441067230420979273583859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6509512614455944729556957 2441067230420979273583859)
          ·
            refine ⟨3661600845631468910375789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441067230420979273583859 3661600845631468910375789)
            ·
              refine ⟨1373100317111800841390921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3661600845631468910375789 1373100317111800841390921)
              ·
                refine ⟨1029825237833850631043191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373100317111800841390921 1029825237833850631043191)
                ·
                  refine ⟨1544737856750775946564787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029825237833850631043191 1544737856750775946564787)
                  ·
                    refine ⟨2317106785126163919847181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1544737856750775946564787 2317106785126163919847181)
                    ·
                      refine ⟨868915044422311469942693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2317106785126163919847181 868915044422311469942693)
                      ·
                        rfl

theorem cell23_1692206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_1692206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692206 prefixEnd_1692206 := by exact prefixLift 1692206
  have htrace : WordTrace (prefixWord ++ tailWord_1692206) baseStart_1692206 baseEnd_1692206 := by
    simpa [prefixWord, tailWord_1692206, baseEnd_1692206] using wordTrace_append hprefix tailTrace_1692206
  have hstable : (prefixWord ++ tailWord_1692206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692206).length < 2 ^ (prefixWord ++ tailWord_1692206).sum := by decide
  have hdescent : baseEnd_1692206 < baseStart_1692206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692255 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 1, 3, 2]
def baseStart_1692255 : Nat := 118140960795 + 1692255 * 2 ^ 59
def prefixEnd_1692255 : Nat := 4983230072969 + 3 ^ 40 * 1692255 * 2
def baseEnd_1692255 : Nat := 868940204974381778229967

theorem tailTrace_1692255 : CollatzResearch.WordTrace tailWord_1692255 prefixEnd_1692255 868940204974381778229967 := by
  unfold tailWord_1692255
  simp only [CollatzResearch.WordTrace]
  refine ⟨61721610484256623989518219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41147740322837749326345479 61721610484256623989518219)
  ·
    refine ⟨92582415726384935984277329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61721610484256623989518219 92582415726384935984277329)
    ·
      refine ⟨69436811794788701988207997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92582415726384935984277329 69436811794788701988207997)
      ·
        refine ⟨26038804423045763245577999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69436811794788701988207997 26038804423045763245577999)
        ·
          refine ⟨39058206634568644868366999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26038804423045763245577999 39058206634568644868366999)
          ·
            refine ⟨58587309951852967302550499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39058206634568644868366999 58587309951852967302550499)
            ·
              refine ⟨87880964927779450953825749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58587309951852967302550499 87880964927779450953825749)
              ·
                refine ⟨2059710115494830881730291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87880964927779450953825749 2059710115494830881730291)
                ·
                  refine ⟨3089565173242246322595437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059710115494830881730291 3089565173242246322595437)
                  ·
                    refine ⟨1158586939965842370973289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089565173242246322595437 1158586939965842370973289)
                    ·
                      refine ⟨868940204974381778229967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158586939965842370973289 868940204974381778229967)
                      ·
                        rfl

theorem cell23_1692255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_1692255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692255 prefixEnd_1692255 := by exact prefixLift 1692255
  have htrace : WordTrace (prefixWord ++ tailWord_1692255) baseStart_1692255 baseEnd_1692255 := by
    simpa [prefixWord, tailWord_1692255, baseEnd_1692255] using wordTrace_append hprefix tailTrace_1692255
  have hstable : (prefixWord ++ tailWord_1692255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692255).length < 2 ^ (prefixWord ++ tailWord_1692255).sum := by decide
  have hdescent : baseEnd_1692255 < baseStart_1692255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692271 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_1692271 : Nat := 118140960795 + 1692271 * 2 ^ 59
def prefixEnd_1692271 : Nat := 4983230072969 + 3 ^ 40 * 1692271 * 2
def baseEnd_1692271 : Nat := 868948420664853715629893

theorem tailTrace_1692271 : CollatzResearch.WordTrace tailWord_1692271 prefixEnd_1692271 868948420664853715629893 := by
  unfold tailWord_1692271
  simp only [CollatzResearch.WordTrace]
  refine ⟨61722194052198658722100667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41148129368132439148067111 61722194052198658722100667)
  ·
    refine ⟨92583291078297988083151001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61722194052198658722100667 92583291078297988083151001)
    ·
      refine ⟨69437468308723491062363251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92583291078297988083151001 69437468308723491062363251)
      ·
        refine ⟨104156202463085236593544877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69437468308723491062363251 104156202463085236593544877)
        ·
          refine ⟨39058575923656963722579329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104156202463085236593544877 39058575923656963722579329)
          ·
            refine ⟨29293931942742722791934497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39058575923656963722579329 29293931942742722791934497)
            ·
              refine ⟨21970448957057042093950873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29293931942742722791934497 21970448957057042093950873)
              ·
                refine ⟨16477836717792781570463155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21970448957057042093950873 16477836717792781570463155)
                ·
                  refine ⟨24716755076689172355694733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16477836717792781570463155 24716755076689172355694733)
                  ·
                    refine ⟨9268783153758439633385525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24716755076689172355694733 9268783153758439633385525)
                    ·
                      refine ⟨868948420664853715629893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9268783153758439633385525 868948420664853715629893)
                      ·
                        rfl

theorem cell23_1692271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_1692271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692271 prefixEnd_1692271 := by exact prefixLift 1692271
  have htrace : WordTrace (prefixWord ++ tailWord_1692271) baseStart_1692271 baseEnd_1692271 := by
    simpa [prefixWord, tailWord_1692271, baseEnd_1692271] using wordTrace_append hprefix tailTrace_1692271
  have hstable : (prefixWord ++ tailWord_1692271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692271).length < 2 ^ (prefixWord ++ tailWord_1692271).sum := by decide
  have hdescent : baseEnd_1692271 < baseStart_1692271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692291 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 9]
def baseStart_1692291 : Nat := 118140960795 + 1692291 * 2 ^ 59
def prefixEnd_1692291 : Nat := 4983230072969 + 3 ^ 40 * 1692291 * 2
def baseEnd_1692291 : Nat := 96550965586438181931089

theorem tailTrace_1692291 : CollatzResearch.WordTrace tailWord_1692291 prefixEnd_1692291 96550965586438181931089 := by
  unfold tailWord_1692291
  simp only [CollatzResearch.WordTrace]
  refine ⟨61722923512126202137828727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41148615674750801425219151 61722923512126202137828727)
  ·
    refine ⟨92584385268189303206743091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61722923512126202137828727 92584385268189303206743091)
    ·
      refine ⟨138876577902283954810114637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92584385268189303206743091 138876577902283954810114637)
      ·
        refine ⟨52078716713356483053792989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138876577902283954810114637 52078716713356483053792989)
        ·
          refine ⟨19529518767508681145172371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52078716713356483053792989 19529518767508681145172371)
          ·
            refine ⟨29294278151263021717758557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19529518767508681145172371 29294278151263021717758557)
            ·
              refine ⟨10985354306723633144159459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29294278151263021717758557 10985354306723633144159459)
              ·
                refine ⟨16478031460085449716239189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10985354306723633144159459 16478031460085449716239189)
                ·
                  refine ⟨96550965586438181931089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16478031460085449716239189 96550965586438181931089)
                  ·
                    rfl

theorem cell23_1692291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 9].length) (baseStart_1692291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692291 prefixEnd_1692291 := by exact prefixLift 1692291
  have htrace : WordTrace (prefixWord ++ tailWord_1692291) baseStart_1692291 baseEnd_1692291 := by
    simpa [prefixWord, tailWord_1692291, baseEnd_1692291] using wordTrace_append hprefix tailTrace_1692291
  have hstable : (prefixWord ++ tailWord_1692291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692291).length < 2 ^ (prefixWord ++ tailWord_1692291).sum := by decide
  have hdescent : baseEnd_1692291 < baseStart_1692291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692302 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_1692302 : Nat := 118140960795 + 1692302 * 2 ^ 59
def prefixEnd_1692302 : Nat := 4983230072969 + 3 ^ 40 * 1692302 * 2
def baseEnd_1692302 : Nat := 868964338565143094342251

theorem tailTrace_1692302 : CollatzResearch.WordTrace tailWord_1692302 prefixEnd_1692302 868964338565143094342251 := by
  unfold tailWord_1692302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7715415589385793877059895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41148883143390900677652773 7715415589385793877059895)
  ·
    refine ⟨11573123384078690815589843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7715415589385793877059895 11573123384078690815589843)
    ·
      refine ⟨17359685076118036223384765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11573123384078690815589843 17359685076118036223384765)
      ·
        refine ⟨6509881903544263583769287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17359685076118036223384765 6509881903544263583769287)
        ·
          refine ⟨9764822855316395375653931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6509881903544263583769287 9764822855316395375653931)
          ·
            refine ⟨14647234282974593063480897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764822855316395375653931 14647234282974593063480897)
            ·
              refine ⟨10985425712230944797610673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14647234282974593063480897 10985425712230944797610673)
              ·
                refine ⟨8239069284173208598208005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10985425712230944797610673 8239069284173208598208005)
                ·
                  refine ⟨1544825490782476612164001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8239069284173208598208005 1544825490782476612164001)
                  ·
                    refine ⟨1158619118086857459123001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1544825490782476612164001 1158619118086857459123001)
                    ·
                      refine ⟨868964338565143094342251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158619118086857459123001 868964338565143094342251)
                      ·
                        rfl

theorem cell23_1692302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_1692302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692302 prefixEnd_1692302 := by exact prefixLift 1692302
  have htrace : WordTrace (prefixWord ++ tailWord_1692302) baseStart_1692302 baseEnd_1692302 := by
    simpa [prefixWord, tailWord_1692302, baseEnd_1692302] using wordTrace_append hprefix tailTrace_1692302
  have hstable : (prefixWord ++ tailWord_1692302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692302).length < 2 ^ (prefixWord ++ tailWord_1692302).sum := by decide
  have hdescent : baseEnd_1692302 < baseStart_1692302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692306 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_1692306 : Nat := 118140960795 + 1692306 * 2 ^ 59
def prefixEnd_1692306 : Nat := 4983230072969 + 3 ^ 40 * 1692306 * 2
def baseEnd_1692306 : Nat := 868966392487761078692233

theorem tailTrace_1692306 : CollatzResearch.WordTrace tailWord_1692306 prefixEnd_1692306 868966392487761078692233 := by
  unfold tailWord_1692306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15430867651767964924906193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41148980404714573133083181 15430867651767964924906193)
  ·
    refine ⟨11573150738825973693679645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15430867651767964924906193 11573150738825973693679645)
    ·
      refine ⟨4339931527059740135129867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11573150738825973693679645 4339931527059740135129867)
      ·
        refine ⟨6509897290589610202694801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339931527059740135129867 6509897290589610202694801)
        ·
          refine ⟨4882422967942207652021101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6509897290589610202694801 4882422967942207652021101)
          ·
            refine ⟨1830908612978327869507913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4882422967942207652021101 1830908612978327869507913)
            ·
              refine ⟨1373181459733745902130935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830908612978327869507913 1373181459733745902130935)
              ·
                refine ⟨2059772189600618853196403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373181459733745902130935 2059772189600618853196403)
                ·
                  refine ⟨3089658284400928279794605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059772189600618853196403 3089658284400928279794605)
                  ·
                    refine ⟨1158621856650348104922977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089658284400928279794605 1158621856650348104922977)
                    ·
                      refine ⟨868966392487761078692233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158621856650348104922977 868966392487761078692233)
                      ·
                        rfl

theorem cell23_1692306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_1692306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692306 prefixEnd_1692306 := by exact prefixLift 1692306
  have htrace : WordTrace (prefixWord ++ tailWord_1692306) baseStart_1692306 baseEnd_1692306 := by
    simpa [prefixWord, tailWord_1692306, baseEnd_1692306] using wordTrace_append hprefix tailTrace_1692306
  have hstable : (prefixWord ++ tailWord_1692306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692306).length < 2 ^ (prefixWord ++ tailWord_1692306).sum := by decide
  have hdescent : baseEnd_1692306 < baseStart_1692306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692372 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_1692372 : Nat := 118140960795 + 1692372 * 2 ^ 59
def prefixEnd_1692372 : Nat := 4983230072969 + 3 ^ 40 * 1692372 * 2
def baseEnd_1692372 : Nat := 289666760736985940155643

theorem tailTrace_1692372 : CollatzResearch.WordTrace tailWord_1692372 prefixEnd_1692372 289666760736985940155643 := by
  unfold tailWord_1692372
  simp only [CollatzResearch.WordTrace]
  refine ⟨30862938912416376485763685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41150585216555168647684913 30862938912416376485763685)
  ·
    refine ⟨5786801046078070591080691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30862938912416376485763685 5786801046078070591080691)
    ·
      refine ⟨8680201569117105886621037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5786801046078070591080691 8680201569117105886621037)
      ·
        refine ⟨3255075588418914707482889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8680201569117105886621037 3255075588418914707482889)
        ·
          refine ⟨2441306691314186030612167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3255075588418914707482889 2441306691314186030612167)
          ·
            refine ⟨3661960036971279045918251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441306691314186030612167 3661960036971279045918251)
            ·
              refine ⟨5492940055456918568877377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661960036971279045918251 5492940055456918568877377)
              ·
                refine ⟨4119705041592688926658033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492940055456918568877377 4119705041592688926658033)
                ·
                  refine ⟨3089778781194516694993525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4119705041592688926658033 3089778781194516694993525)
                  ·
                    refine ⟨289666760736985940155643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3089778781194516694993525 289666760736985940155643)
                    ·
                      rfl

theorem cell23_1692372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_1692372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692372 prefixEnd_1692372 := by exact prefixLift 1692372
  have htrace : WordTrace (prefixWord ++ tailWord_1692372) baseStart_1692372 baseEnd_1692372 := by
    simpa [prefixWord, tailWord_1692372, baseEnd_1692372] using wordTrace_append hprefix tailTrace_1692372
  have hstable : (prefixWord ++ tailWord_1692372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692372).length < 2 ^ (prefixWord ++ tailWord_1692372).sum := by decide
  have hdescent : baseEnd_1692372 < baseStart_1692372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692375 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1692375 : Nat := 118140960795 + 1692375 * 2 ^ 59
def prefixEnd_1692375 : Nat := 4983230072969 + 3 ^ 40 * 1692375 * 2
def baseEnd_1692375 : Nat := 869001822652921308729415

theorem tailTrace_1692375 : CollatzResearch.WordTrace tailWord_1692375 prefixEnd_1692375 869001822652921308729415 := by
  unfold tailWord_1692375
  simp only [CollatzResearch.WordTrace]
  refine ⟨61725987243821884483886579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41150658162547922989257719 61725987243821884483886579)
  ·
    refine ⟨92588980865732826725829869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61725987243821884483886579 92588980865732826725829869)
    ·
      refine ⟨34720867824649810022186201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92588980865732826725829869 34720867824649810022186201)
      ·
        refine ⟨26040650868487357516639651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34720867824649810022186201 26040650868487357516639651)
        ·
          refine ⟨39060976302731036274959477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26040650868487357516639651 39060976302731036274959477)
          ·
            refine ⟨3661966528381034650777451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39060976302731036274959477 3661966528381034650777451)
            ·
              refine ⟨5492949792571551976166177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661966528381034650777451 5492949792571551976166177)
              ·
                refine ⟨4119712344428663982124633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492949792571551976166177 4119712344428663982124633)
                ·
                  refine ⟨3089784258321497986593475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4119712344428663982124633 3089784258321497986593475)
                  ·
                    refine ⟨4634676387482246979890213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3089784258321497986593475 4634676387482246979890213)
                    ·
                      refine ⟨869001822652921308729415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4634676387482246979890213 869001822652921308729415)
                      ·
                        rfl

theorem cell23_1692375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1692375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692375 prefixEnd_1692375 := by exact prefixLift 1692375
  have htrace : WordTrace (prefixWord ++ tailWord_1692375) baseStart_1692375 baseEnd_1692375 := by
    simpa [prefixWord, tailWord_1692375, baseEnd_1692375] using wordTrace_append hprefix tailTrace_1692375
  have hstable : (prefixWord ++ tailWord_1692375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692375).length < 2 ^ (prefixWord ++ tailWord_1692375).sum := by decide
  have hdescent : baseEnd_1692375 < baseStart_1692375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692412 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_1692412 : Nat := 118140960795 + 1692412 * 2 ^ 59
def prefixEnd_1692412 : Nat := 4983230072969 + 3 ^ 40 * 1692412 * 2
def baseEnd_1692412 : Nat := 869020821437137663966745

theorem tailTrace_1692412 : CollatzResearch.WordTrace tailWord_1692412 prefixEnd_1692412 869020821437137663966745 := by
  unfold tailWord_1692412
  simp only [CollatzResearch.WordTrace]
  refine ⟨30863668372343919901491745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41151557829791893201988993 30863668372343919901491745)
  ·
    refine ⟨23147751279257939926118809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30863668372343919901491745 23147751279257939926118809)
    ·
      refine ⟨17360813459443454944589107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23147751279257939926118809 17360813459443454944589107)
      ·
        refine ⟨26041220189165182416883661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17360813459443454944589107 26041220189165182416883661)
        ·
          refine ⟨9765457570936943406331373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26041220189165182416883661 9765457570936943406331373)
          ·
            refine ⟨3662046589101353777374265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9765457570936943406331373 3662046589101353777374265)
            ·
              refine ⟨2746534941826015333030699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662046589101353777374265 2746534941826015333030699)
              ·
                refine ⟨4119802412739022999546049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746534941826015333030699 4119802412739022999546049)
                ·
                  refine ⟨3089851809554267249659537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4119802412739022999546049 3089851809554267249659537)
                  ·
                    refine ⟨2317388857165700437244653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3089851809554267249659537 2317388857165700437244653)
                    ·
                      refine ⟨869020821437137663966745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2317388857165700437244653 869020821437137663966745)
                      ·
                        rfl

theorem cell23_1692412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_1692412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692412 prefixEnd_1692412 := by exact prefixLift 1692412
  have htrace : WordTrace (prefixWord ++ tailWord_1692412) baseStart_1692412 baseEnd_1692412 := by
    simpa [prefixWord, tailWord_1692412, baseEnd_1692412] using wordTrace_append hprefix tailTrace_1692412
  have hstable : (prefixWord ++ tailWord_1692412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692412).length < 2 ^ (prefixWord ++ tailWord_1692412).sum := by decide
  have hdescent : baseEnd_1692412 < baseStart_1692412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692442 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3]
def baseStart_1692442 : Nat := 118140960795 + 1692442 * 2 ^ 59
def prefixEnd_1692442 : Nat := 4983230072969 + 3 ^ 40 * 1692442 * 2
def baseEnd_1692442 : Nat := 869036225856772546591607

theorem tailTrace_1692442 : CollatzResearch.WordTrace tailWord_1692442 prefixEnd_1692442 869036225856772546591607 := by
  unfold tailWord_1692442
  simp only [CollatzResearch.WordTrace]
  refine ⟨15432107733644788731643895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41152287289719436617717053 15432107733644788731643895)
  ·
    refine ⟨23148161600467183097465843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15432107733644788731643895 23148161600467183097465843)
    ·
      refine ⟨34722242400700774646198765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23148161600467183097465843 34722242400700774646198765)
      ·
        refine ⟨13020840900262790492324537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34722242400700774646198765 13020840900262790492324537)
        ·
          refine ⟨9765630675197092869243403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13020840900262790492324537 9765630675197092869243403)
          ·
            refine ⟨14648446012795639303865105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9765630675197092869243403 14648446012795639303865105)
            ·
              refine ⟨10986334509596729477898829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14648446012795639303865105 10986334509596729477898829)
              ·
                refine ⟨4119875441098773554212061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10986334509596729477898829 4119875441098773554212061)
                ·
                  refine ⟨1544953290412040082829523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4119875441098773554212061 1544953290412040082829523)
                  ·
                    refine ⟨2317429935618060124244285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1544953290412040082829523 2317429935618060124244285)
                    ·
                      refine ⟨869036225856772546591607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2317429935618060124244285 869036225856772546591607)
                      ·
                        rfl

theorem cell23_1692442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_1692442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692442 prefixEnd_1692442 := by exact prefixLift 1692442
  have htrace : WordTrace (prefixWord ++ tailWord_1692442) baseStart_1692442 baseEnd_1692442 := by
    simpa [prefixWord, tailWord_1692442, baseEnd_1692442] using wordTrace_append hprefix tailTrace_1692442
  have hstable : (prefixWord ++ tailWord_1692442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692442).length < 2 ^ (prefixWord ++ tailWord_1692442).sum := by decide
  have hdescent : baseEnd_1692442 < baseStart_1692442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692462 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1692462 : Nat := 118140960795 + 1692462 * 2 ^ 59
def prefixEnd_1692462 : Nat := 4983230072969 + 3 ^ 40 * 1692462 * 2
def baseEnd_1692462 : Nat := 289682165156620822780505

theorem tailTrace_1692462 : CollatzResearch.WordTrace tailWord_1692462 prefixEnd_1692462 289682165156620822780505 := by
  unfold tailWord_1692462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7716145049313337292787955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41152773596337798894869093 7716145049313337292787955)
  ·
    refine ⟨11574217573970005939181933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7716145049313337292787955 11574217573970005939181933)
    ·
      refine ⟨4340331590238752227193225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11574217573970005939181933 4340331590238752227193225)
      ·
        refine ⟨3255248692679064170394919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4340331590238752227193225 3255248692679064170394919)
        ·
          refine ⟨4882873039018596255592379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255248692679064170394919 4882873039018596255592379)
          ·
            refine ⟨7324309558527894383388569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882873039018596255592379 7324309558527894383388569)
            ·
              refine ⟨5493232168895920787541427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7324309558527894383388569 5493232168895920787541427)
              ·
                refine ⟨8239848253343881181312141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5493232168895920787541427 8239848253343881181312141)
                ·
                  refine ⟨3089943095003955442992053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8239848253343881181312141 3089943095003955442992053)
                  ·
                    refine ⟨289682165156620822780505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3089943095003955442992053 289682165156620822780505)
                    ·
                      rfl

theorem cell23_1692462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1692462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692462 prefixEnd_1692462 := by exact prefixLift 1692462
  have htrace : WordTrace (prefixWord ++ tailWord_1692462) baseStart_1692462 baseEnd_1692462 := by
    simpa [prefixWord, tailWord_1692462, baseEnd_1692462] using wordTrace_append hprefix tailTrace_1692462
  have hstable : (prefixWord ++ tailWord_1692462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692462).length < 2 ^ (prefixWord ++ tailWord_1692462).sum := by decide
  have hdescent : baseEnd_1692462 < baseStart_1692462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692465 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1692465 : Nat := 118140960795 + 1692465 * 2 ^ 59
def prefixEnd_1692465 : Nat := 4983230072969 + 3 ^ 40 * 1692465 * 2
def baseEnd_1692465 : Nat := 869048035911825956604001

theorem tailTrace_1692465 : CollatzResearch.WordTrace tailWord_1692465 prefixEnd_1692465 869048035911825956604001 := by
  unfold tailWord_1692465
  simp only [CollatzResearch.WordTrace]
  refine ⟨61729269813495829854662849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41152846542330553236441899 61729269813495829854662849)
  ·
    refine ⟨46296952360121872390997137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61729269813495829854662849 46296952360121872390997137)
    ·
      refine ⟨34722714270091404293247853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46296952360121872390997137 34722714270091404293247853)
      ·
        refine ⟨13021017851284276609967945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34722714270091404293247853 13021017851284276609967945)
        ·
          refine ⟨9765763388463207457475959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13021017851284276609967945 9765763388463207457475959)
          ·
            refine ⟨14648645082694811186213939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9765763388463207457475959 14648645082694811186213939)
            ·
              refine ⟨21972967624042216779320909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14648645082694811186213939 21972967624042216779320909)
              ·
                refine ⟨8239862859015831292245341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21972967624042216779320909 8239862859015831292245341)
                ·
                  refine ⟨3089948572130936734592003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8239862859015831292245341 3089948572130936734592003)
                  ·
                    refine ⟨4634922858196405101888005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3089948572130936734592003 4634922858196405101888005)
                    ·
                      refine ⟨869048035911825956604001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4634922858196405101888005 869048035911825956604001)
                      ·
                        rfl

theorem cell23_1692465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1692465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692465 prefixEnd_1692465 := by exact prefixLift 1692465
  have htrace : WordTrace (prefixWord ++ tailWord_1692465) baseStart_1692465 baseEnd_1692465 := by
    simpa [prefixWord, tailWord_1692465, baseEnd_1692465] using wordTrace_append hprefix tailTrace_1692465
  have hstable : (prefixWord ++ tailWord_1692465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692465).length < 2 ^ (prefixWord ++ tailWord_1692465).sum := by decide
  have hdescent : baseEnd_1692465 < baseStart_1692465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692469 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_1692469 : Nat := 118140960795 + 1692469 * 2 ^ 59
def prefixEnd_1692469 : Nat := 4983230072969 + 3 ^ 40 * 1692469 * 2
def baseEnd_1692469 : Nat := 869050089834443940953983

theorem tailTrace_1692469 : CollatzResearch.WordTrace tailWord_1692469 prefixEnd_1692469 869050089834443940953983 := by
  unfold tailWord_1692469
  simp only [CollatzResearch.WordTrace]
  refine ⟨61729415705481338537808461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41152943803654225691872307 61729415705481338537808461)
  ·
    refine ⟨23148530889555501951678173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61729415705481338537808461 23148530889555501951678173)
    ·
      refine ⟨8680699083583313231879315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23148530889555501951678173 8680699083583313231879315)
      ·
        refine ⟨13021048625374969847818973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8680699083583313231879315 13021048625374969847818973)
        ·
          refine ⟨4882893234515613692932115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13021048625374969847818973 4882893234515613692932115)
          ·
            refine ⟨7324339851773420539398173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882893234515613692932115 7324339851773420539398173)
            ·
              refine ⟨2746627444415032702274315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7324339851773420539398173 2746627444415032702274315)
              ·
                refine ⟨4119941166622549053411473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746627444415032702274315 4119941166622549053411473)
                ·
                  refine ⟨3089955874966911790058605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4119941166622549053411473 3089955874966911790058605)
                  ·
                    refine ⟨1158733453112591921271977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089955874966911790058605 1158733453112591921271977)
                    ·
                      refine ⟨869050089834443940953983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158733453112591921271977 869050089834443940953983)
                      ·
                        rfl

theorem cell23_1692469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_1692469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692469 prefixEnd_1692469 := by exact prefixLift 1692469
  have htrace : WordTrace (prefixWord ++ tailWord_1692469) baseStart_1692469 baseEnd_1692469 := by
    simpa [prefixWord, tailWord_1692469, baseEnd_1692469] using wordTrace_append hprefix tailTrace_1692469
  have hstable : (prefixWord ++ tailWord_1692469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692469).length < 2 ^ (prefixWord ++ tailWord_1692469).sum := by decide
  have hdescent : baseEnd_1692469 < baseStart_1692469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692479 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 1, 5]
def baseStart_1692479 : Nat := 118140960795 + 1692479 * 2 ^ 59
def prefixEnd_1692479 : Nat := 4983230072969 + 3 ^ 40 * 1692479 * 2
def baseEnd_1692479 : Nat := 289685074880329633942979

theorem tailTrace_1692479 : CollatzResearch.WordTrace tailWord_1692479 prefixEnd_1692479 289685074880329633942979 := by
  unfold tailWord_1692479
  simp only [CollatzResearch.WordTrace]
  refine ⟨61729780435445110245672491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41153186956963406830448327 61729780435445110245672491)
  ·
    refine ⟨92594670653167665368508737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61729780435445110245672491 92594670653167665368508737)
    ·
      refine ⟨69446002989875749026381553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92594670653167665368508737 69446002989875749026381553)
      ·
        refine ⟨52084502242406811769786165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69446002989875749026381553 52084502242406811769786165)
        ·
          refine ⟨4882922085225638603417453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52084502242406811769786165 4882922085225638603417453)
          ·
            refine ⟨1831095781959614476281545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4882922085225638603417453 1831095781959614476281545)
            ·
              refine ⟨1373321836469710857211159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831095781959614476281545 1373321836469710857211159)
              ·
                refine ⟨2059982754704566285816739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373321836469710857211159 2059982754704566285816739)
                ·
                  refine ⟨3089974132056849428725109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059982754704566285816739 3089974132056849428725109)
                  ·
                    refine ⟨289685074880329633942979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3089974132056849428725109 289685074880329633942979)
                    ·
                      rfl

theorem cell23_1692479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 5].length) (baseStart_1692479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692479 prefixEnd_1692479 := by exact prefixLift 1692479
  have htrace : WordTrace (prefixWord ++ tailWord_1692479) baseStart_1692479 baseEnd_1692479 := by
    simpa [prefixWord, tailWord_1692479, baseEnd_1692479] using wordTrace_append hprefix tailTrace_1692479
  have hstable : (prefixWord ++ tailWord_1692479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692479).length < 2 ^ (prefixWord ++ tailWord_1692479).sum := by decide
  have hdescent : baseEnd_1692479 < baseStart_1692479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692485 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_1692485 : Nat := 118140960795 + 1692485 * 2 ^ 59
def prefixEnd_1692485 : Nat := 4983230072969 + 3 ^ 40 * 1692485 * 2
def baseEnd_1692485 : Nat := 869058305524915878353909

theorem tailTrace_1692485 : CollatzResearch.WordTrace tailWord_1692485 prefixEnd_1692485 869058305524915878353909 := by
  unfold tailWord_1692485
  simp only [CollatzResearch.WordTrace]
  refine ⟨61729999273423373270390909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41153332848948915513593939 61729999273423373270390909)
  ·
    refine ⟨23148749727533764976396591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61729999273423373270390909 23148749727533764976396591)
    ·
      refine ⟨34723124591300647464594887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23148749727533764976396591 34723124591300647464594887)
      ·
        refine ⟨52084686886950971196892331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34723124591300647464594887 52084686886950971196892331)
        ·
          refine ⟨78127030330426456795338497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52084686886950971196892331 78127030330426456795338497)
          ·
            refine ⟨58595272747819842596503873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78127030330426456795338497 58595272747819842596503873)
            ·
              refine ⟨43946454560864881947377905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58595272747819842596503873 43946454560864881947377905)
              ·
                refine ⟨32959840920648661460533429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43946454560864881947377905 32959840920648661460533429)
                ·
                  refine ⟨3089985086310812011925009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32959840920648661460533429 3089985086310812011925009)
                  ·
                    refine ⟨2317488814733109008943757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3089985086310812011925009 2317488814733109008943757)
                    ·
                      refine ⟨869058305524915878353909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2317488814733109008943757 869058305524915878353909)
                      ·
                        rfl

theorem cell23_1692485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_1692485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692485 prefixEnd_1692485 := by exact prefixLift 1692485
  have htrace : WordTrace (prefixWord ++ tailWord_1692485) baseStart_1692485 baseEnd_1692485 := by
    simpa [prefixWord, tailWord_1692485, baseEnd_1692485] using wordTrace_append hprefix tailTrace_1692485
  have hstable : (prefixWord ++ tailWord_1692485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692485).length < 2 ^ (prefixWord ++ tailWord_1692485).sum := by decide
  have hdescent : baseEnd_1692485 < baseStart_1692485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692488 : List Nat := [2, 1, 3, 1, 1, 3, 12]
def baseStart_1692488 : Nat := 118140960795 + 1692488 * 2 ^ 59
def prefixEnd_1692488 : Nat := 4983230072969 + 3 ^ 40 * 1692488 * 2
def baseEnd_1692488 : Nat := 10729133900825671192795

theorem tailTrace_1692488 : CollatzResearch.WordTrace tailWord_1692488 prefixEnd_1692488 10729133900825671192795 := by
  unfold tailWord_1692488
  simp only [CollatzResearch.WordTrace]
  refine ⟨30865054346206252391375059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41153405794941669855166745 30865054346206252391375059)
  ·
    refine ⟨46297581519309378587062589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30865054346206252391375059 46297581519309378587062589)
    ·
      refine ⟨17361593069741016970148471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46297581519309378587062589 17361593069741016970148471)
      ·
        refine ⟨26042389604611525455222707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17361593069741016970148471 26042389604611525455222707)
        ·
          refine ⟨39063584406917288182834061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26042389604611525455222707 39063584406917288182834061)
          ·
            refine ⟨14648844152593983068562773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39063584406917288182834061 14648844152593983068562773)
            ·
              refine ⟨10729133900825671192795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 14648844152593983068562773 10729133900825671192795)
              ·
                rfl

theorem cell23_1692488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 12].length) (baseStart_1692488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692488 prefixEnd_1692488 := by exact prefixLift 1692488
  have htrace : WordTrace (prefixWord ++ tailWord_1692488) baseStart_1692488 baseEnd_1692488 := by
    simpa [prefixWord, tailWord_1692488, baseEnd_1692488] using wordTrace_append hprefix tailTrace_1692488
  have hstable : (prefixWord ++ tailWord_1692488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692488).length < 2 ^ (prefixWord ++ tailWord_1692488).sum := by decide
  have hdescent : baseEnd_1692488 < baseStart_1692488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692492 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_1692492 : Nat := 118140960795 + 1692492 * 2 ^ 59
def prefixEnd_1692492 : Nat := 4983230072969 + 3 ^ 40 * 1692492 * 2
def baseEnd_1692492 : Nat := 289687299963165783655459

theorem tailTrace_1692492 : CollatzResearch.WordTrace tailWord_1692492 prefixEnd_1692492 289687299963165783655459 := by
  unfold tailWord_1692492
  simp only [CollatzResearch.WordTrace]
  refine ⟨30865127292199006732947865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41153503056265342310597153 30865127292199006732947865)
  ·
    refine ⟨23148845469149255049710899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30865127292199006732947865 23148845469149255049710899)
    ·
      refine ⟨34723268203723882574566349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23148845469149255049710899 34723268203723882574566349)
      ·
        refine ⟨13021225576396455965462381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34723268203723882574566349 13021225576396455965462381)
        ·
          refine ⟨4882959591148670987048393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13021225576396455965462381 4882959591148670987048393)
          ·
            refine ⟨3662219693361503240286295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4882959591148670987048393 3662219693361503240286295)
            ·
              refine ⟨5493329540042254860429443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3662219693361503240286295 5493329540042254860429443)
              ·
                refine ⟨8239994310063382290644165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5493329540042254860429443 8239994310063382290644165)
                ·
                  refine ⟨1544998933136884179495781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8239994310063382290644165 1544998933136884179495781)
                  ·
                    refine ⟨289687299963165783655459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1544998933136884179495781 289687299963165783655459)
                    ·
                      rfl

theorem cell23_1692492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_1692492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692492 prefixEnd_1692492 := by exact prefixLift 1692492
  have htrace : WordTrace (prefixWord ++ tailWord_1692492) baseStart_1692492 baseEnd_1692492 := by
    simpa [prefixWord, tailWord_1692492, baseEnd_1692492] using wordTrace_append hprefix tailTrace_1692492
  have hstable : (prefixWord ++ tailWord_1692492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692492).length < 2 ^ (prefixWord ++ tailWord_1692492).sum := by decide
  have hdescent : baseEnd_1692492 < baseStart_1692492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692519 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_1692519 : Nat := 118140960795 + 1692519 * 2 ^ 59
def prefixEnd_1692519 : Nat := 4983230072969 + 3 ^ 40 * 1692519 * 2
def baseEnd_1692519 : Nat := 869075763867168745328753

theorem tailTrace_1692519 : CollatzResearch.WordTrace tailWord_1692519 prefixEnd_1692519 869075763867168745328753 := by
  unfold tailWord_1692519
  simp only [CollatzResearch.WordTrace]
  refine ⟨61731239355300197077128611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41154159570200131384752407 61731239355300197077128611)
  ·
    refine ⟨92596859032950295615692917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61731239355300197077128611 92596859032950295615692917)
    ·
      refine ⟨8680955534339090213971211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92596859032950295615692917 8680955534339090213971211)
      ·
        refine ⟨13021433301508635320956817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8680955534339090213971211 13021433301508635320956817)
        ·
          refine ⟨9766074976131476490717613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13021433301508635320956817 9766074976131476490717613)
          ·
            refine ⟨3662278116049303684019105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9766074976131476490717613 3662278116049303684019105)
            ·
              refine ⟨2746708587036977763014329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662278116049303684019105 2746708587036977763014329)
              ·
                refine ⟨2060031440277733322260747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746708587036977763014329 2060031440277733322260747)
                ·
                  refine ⟨3090047160416599983391121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060031440277733322260747 3090047160416599983391121)
                  ·
                    refine ⟨2317535370312449987543341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3090047160416599983391121 2317535370312449987543341)
                    ·
                      refine ⟨869075763867168745328753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2317535370312449987543341 869075763867168745328753)
                      ·
                        rfl

theorem cell23_1692519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_1692519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692519 prefixEnd_1692519 := by exact prefixLift 1692519
  have htrace : WordTrace (prefixWord ++ tailWord_1692519) baseStart_1692519 baseEnd_1692519 := by
    simpa [prefixWord, tailWord_1692519, baseEnd_1692519] using wordTrace_append hprefix tailTrace_1692519
  have hstable : (prefixWord ++ tailWord_1692519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692519).length < 2 ^ (prefixWord ++ tailWord_1692519).sum := by decide
  have hdescent : baseEnd_1692519 < baseStart_1692519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692533 : List Nat := [1, 3, 4, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_1692533 : Nat := 118140960795 + 1692533 * 2 ^ 59
def prefixEnd_1692533 : Nat := 4983230072969 + 3 ^ 40 * 1692533 * 2
def baseEnd_1692533 : Nat := 869082952596331690553689

theorem tailTrace_1692533 : CollatzResearch.WordTrace tailWord_1692533 prefixEnd_1692533 869082952596331690553689 := by
  unfold tailWord_1692533
  simp only [CollatzResearch.WordTrace]
  refine ⟨61731749977249477468138253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41154499984832984978758835 61731749977249477468138253)
  ·
    refine ⟨23149406241468554050551845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61731749977249477468138253 23149406241468554050551845)
    ·
      refine ⟨4340513670275353884478471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23149406241468554050551845 4340513670275353884478471)
      ·
        refine ⟨6510770505413030826717707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4340513670275353884478471 6510770505413030826717707)
        ·
          refine ⟨9766155758119546240076561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6510770505413030826717707 9766155758119546240076561)
          ·
            refine ⟨7324616818589659680057421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9766155758119546240076561 7324616818589659680057421)
            ·
              refine ⟨2746731306971122380021533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7324616818589659680057421 2746731306971122380021533)
              ·
                refine ⟨1030024240114170892508075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2746731306971122380021533 1030024240114170892508075)
                ·
                  refine ⟨1545036360171256338762113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030024240114170892508075 1545036360171256338762113)
                  ·
                    refine ⟨1158777270128442254071585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1545036360171256338762113 1158777270128442254071585)
                    ·
                      refine ⟨869082952596331690553689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158777270128442254071585 869082952596331690553689)
                      ·
                        rfl

theorem cell23_1692533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_1692533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692533 prefixEnd_1692533 := by exact prefixLift 1692533
  have htrace : WordTrace (prefixWord ++ tailWord_1692533) baseStart_1692533 baseEnd_1692533 := by
    simpa [prefixWord, tailWord_1692533, baseEnd_1692533] using wordTrace_append hprefix tailTrace_1692533
  have hstable : (prefixWord ++ tailWord_1692533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692533).length < 2 ^ (prefixWord ++ tailWord_1692533).sum := by decide
  have hdescent : baseEnd_1692533 < baseStart_1692533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692593 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 1, 3, 2]
def baseStart_1692593 : Nat := 118140960795 + 1692593 * 2 ^ 59
def prefixEnd_1692593 : Nat := 4983230072969 + 3 ^ 40 * 1692593 * 2
def baseEnd_1692593 : Nat := 869113761435601455803413

theorem tailTrace_1692593 : CollatzResearch.WordTrace tailWord_1692593 prefixEnd_1692593 869113761435601455803413 := by
  unfold tailWord_1692593
  simp only [CollatzResearch.WordTrace]
  refine ⟨61733938357032107715322433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41155958904688071810214955 61733938357032107715322433)
  ·
    refine ⟨46300453767774080786491825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61733938357032107715322433 46300453767774080786491825)
    ·
      refine ⟨34725340325830560589868869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46300453767774080786491825 34725340325830560589868869)
      ·
        refine ⟨6511001311093230110600413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34725340325830560589868869 6511001311093230110600413)
        ·
          refine ⟨2441625491659961291475155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6511001311093230110600413 2441625491659961291475155)
          ·
            refine ⟨3662438237489941937212733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441625491659961291475155 3662438237489941937212733)
            ·
              refine ⟨1373414339058728226454775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3662438237489941937212733 1373414339058728226454775)
              ·
                refine ⟨2060121508588092339682163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373414339058728226454775 2060121508588092339682163)
                ·
                  refine ⟨3090182262882138509523245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060121508588092339682163 3090182262882138509523245)
                  ·
                    refine ⟨1158818348580801941071217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3090182262882138509523245 1158818348580801941071217)
                    ·
                      refine ⟨869113761435601455803413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158818348580801941071217 869113761435601455803413)
                      ·
                        rfl

theorem cell23_1692593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_1692593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692593 prefixEnd_1692593 := by exact prefixLift 1692593
  have htrace : WordTrace (prefixWord ++ tailWord_1692593) baseStart_1692593 baseEnd_1692593 := by
    simpa [prefixWord, tailWord_1692593, baseEnd_1692593] using wordTrace_append hprefix tailTrace_1692593
  have hstable : (prefixWord ++ tailWord_1692593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692593).length < 2 ^ (prefixWord ++ tailWord_1692593).sum := by decide
  have hdescent : baseEnd_1692593 < baseStart_1692593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692622 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1692622 : Nat := 118140960795 + 1692622 * 2 ^ 59
def prefixEnd_1692622 : Nat := 4983230072969 + 3 ^ 40 * 1692622 * 2
def baseEnd_1692622 : Nat := 869128652374581842340779

theorem tailTrace_1692622 : CollatzResearch.WordTrace tailWord_1692622 prefixEnd_1692622 869128652374581842340779 := by
  unfold tailWord_1692622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7716874509240880708516015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41156664049284697112085413 7716874509240880708516015)
  ·
    refine ⟨11575311763861321062774023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7716874509240880708516015 11575311763861321062774023)
    ·
      refine ⟨17362967645791981594161035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11575311763861321062774023 17362967645791981594161035)
      ·
        refine ⟨26044451468687972391241553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17362967645791981594161035 26044451468687972391241553)
        ·
          refine ⟨19533338601515979293431165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26044451468687972391241553 19533338601515979293431165)
          ·
            refine ⟨7325001975568492235036687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19533338601515979293431165 7325001975568492235036687)
            ·
              refine ⟨10987502963352738352555031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325001975568492235036687 10987502963352738352555031)
              ·
                refine ⟨16481254445029107528832547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10987502963352738352555031 16481254445029107528832547)
                ·
                  refine ⟨24721881667543661293248821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16481254445029107528832547 24721881667543661293248821)
                  ·
                    refine ⟨2317676406332218246242077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24721881667543661293248821 2317676406332218246242077)
                    ·
                      refine ⟨869128652374581842340779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2317676406332218246242077 869128652374581842340779)
                      ·
                        rfl

theorem cell23_1692622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1692622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692622 prefixEnd_1692622 := by exact prefixLift 1692622
  have htrace : WordTrace (prefixWord ++ tailWord_1692622) baseStart_1692622 baseEnd_1692622 := by
    simpa [prefixWord, tailWord_1692622, baseEnd_1692622] using wordTrace_append hprefix tailTrace_1692622
  have hstable : (prefixWord ++ tailWord_1692622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692622).length < 2 ^ (prefixWord ++ tailWord_1692622).sum := by decide
  have hdescent : baseEnd_1692622 < baseStart_1692622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692625 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 1, 7]
def baseStart_1692625 : Nat := 118140960795 + 1692625 * 2 ^ 59
def prefixEnd_1692625 : Nat := 4983230072969 + 3 ^ 40 * 1692625 * 2
def baseEnd_1692625 : Nat := 289710064272181776867755

theorem tailTrace_1692625 : CollatzResearch.WordTrace tailWord_1692625 prefixEnd_1692625 289710064272181776867755 := by
  unfold tailWord_1692625
  simp only [CollatzResearch.WordTrace]
  refine ⟨61735105492916177180487329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41156736995277451453658219 61735105492916177180487329)
  ·
    refine ⟨46301329119687132885365497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61735105492916177180487329 46301329119687132885365497)
    ·
      refine ⟨34725996839765349664024123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46301329119687132885365497 34725996839765349664024123)
      ·
        refine ⟨52088995259648024496036185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34725996839765349664024123 52088995259648024496036185)
        ·
          refine ⟨39066746444736018372027139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52088995259648024496036185 39066746444736018372027139)
          ·
            refine ⟨58600119667104027558040709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39066746444736018372027139 58600119667104027558040709)
            ·
              refine ⟨10987522437582005167132633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58600119667104027558040709 10987522437582005167132633)
              ·
                refine ⟨8240641828186503875349475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10987522437582005167132633 8240641828186503875349475)
                ·
                  refine ⟨12360962742279755813024213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8240641828186503875349475 12360962742279755813024213)
                  ·
                    refine ⟨289710064272181776867755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12360962742279755813024213 289710064272181776867755)
                    ·
                      rfl

theorem cell23_1692625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_1692625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692625 prefixEnd_1692625 := by exact prefixLift 1692625
  have htrace : WordTrace (prefixWord ++ tailWord_1692625) baseStart_1692625 baseEnd_1692625 := by
    simpa [prefixWord, tailWord_1692625, baseEnd_1692625] using wordTrace_append hprefix tailTrace_1692625
  have hstable : (prefixWord ++ tailWord_1692625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692625).length < 2 ^ (prefixWord ++ tailWord_1692625).sum := by decide
  have hdescent : baseEnd_1692625 < baseStart_1692625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692679 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_1692679 : Nat := 118140960795 + 1692679 * 2 ^ 59
def prefixEnd_1692679 : Nat := 4983230072969 + 3 ^ 40 * 1692679 * 2
def baseEnd_1692679 : Nat := 869157920771888119328017

theorem tailTrace_1692679 : CollatzResearch.WordTrace tailWord_1692679 prefixEnd_1692679 869157920771888119328017 := by
  unfold tailWord_1692679
  simp only [CollatzResearch.WordTrace]
  refine ⟨61737075034720544402953091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41158050023147029601968727 61737075034720544402953091)
  ·
    refine ⟨92605612552080816604429637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61737075034720544402953091 92605612552080816604429637)
    ·
      refine ⟨17363552353515153113330557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92605612552080816604429637 17363552353515153113330557)
      ·
        refine ⟨6511332132568182417498959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17363552353515153113330557 6511332132568182417498959)
        ·
          refine ⟨9766998198852273626248439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6511332132568182417498959 9766998198852273626248439)
          ·
            refine ⟨14650497298278410439372659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766998198852273626248439 14650497298278410439372659)
            ·
              refine ⟨21975745947417615659058989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14650497298278410439372659 21975745947417615659058989)
              ·
                refine ⟨8240904730281605872147121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21975745947417615659058989 8240904730281605872147121)
                ·
                  refine ⟨6180678547711204404110341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8240904730281605872147121 6180678547711204404110341)
                  ·
                    refine ⟨1158877227695850825770689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6180678547711204404110341 1158877227695850825770689)
                    ·
                      refine ⟨869157920771888119328017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158877227695850825770689 869157920771888119328017)
                      ·
                        rfl

theorem cell23_1692679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_1692679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692679 prefixEnd_1692679 := by exact prefixLift 1692679
  have htrace : WordTrace (prefixWord ++ tailWord_1692679) baseStart_1692679 baseEnd_1692679 := by
    simpa [prefixWord, tailWord_1692679, baseEnd_1692679] using wordTrace_append hprefix tailTrace_1692679
  have hstable : (prefixWord ++ tailWord_1692679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692679).length < 2 ^ (prefixWord ++ tailWord_1692679).sum := by decide
  have hdescent : baseEnd_1692679 < baseStart_1692679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692739 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 4, 3, 2]
def baseStart_1692739 : Nat := 118140960795 + 1692739 * 2 ^ 59
def prefixEnd_1692739 : Nat := 4983230072969 + 3 ^ 40 * 1692739 * 2
def baseEnd_1692739 : Nat := 869188729611157884577741

theorem tailTrace_1692739 : CollatzResearch.WordTrace tailWord_1692739 prefixEnd_1692739 869188729611157884577741 := by
  unfold tailWord_1692739
  simp only [CollatzResearch.WordTrace]
  refine ⟨61739263414503174650137271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41159508943002116433424847 61739263414503174650137271)
  ·
    refine ⟨92608895121754761975205907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61739263414503174650137271 92608895121754761975205907)
    ·
      refine ⟨138913342682632142962808861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92608895121754761975205907 138913342682632142962808861)
      ·
        refine ⟨52092503505987053611053323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138913342682632142962808861 52092503505987053611053323)
        ·
          refine ⟨78138755258980580416579985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52092503505987053611053323 78138755258980580416579985)
          ·
            refine ⟨58604066444235435312434989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78138755258980580416579985 58604066444235435312434989)
            ·
              refine ⟨21976524916588288242163121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58604066444235435312434989 21976524916588288242163121)
              ·
                refine ⟨16482393687441216181622341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21976524916588288242163121 16482393687441216181622341)
                ·
                  refine ⟨3090448816395228034054189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16482393687441216181622341 3090448816395228034054189)
                  ·
                    refine ⟨1158918306148210512770321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3090448816395228034054189 1158918306148210512770321)
                    ·
                      refine ⟨869188729611157884577741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158918306148210512770321 869188729611157884577741)
                      ·
                        rfl

theorem cell23_1692739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_1692739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692739 prefixEnd_1692739 := by exact prefixLift 1692739
  have htrace : WordTrace (prefixWord ++ tailWord_1692739) baseStart_1692739 baseEnd_1692739 := by
    simpa [prefixWord, tailWord_1692739, baseEnd_1692739] using wordTrace_append hprefix tailTrace_1692739
  have hstable : (prefixWord ++ tailWord_1692739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692739).length < 2 ^ (prefixWord ++ tailWord_1692739).sum := by decide
  have hdescent : baseEnd_1692739 < baseStart_1692739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692756 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_1692756 : Nat := 118140960795 + 1692756 * 2 ^ 59
def prefixEnd_1692756 : Nat := 4983230072969 + 3 ^ 40 * 1692756 * 2
def baseEnd_1692756 : Nat := 869197458782284318065163

theorem tailTrace_1692756 : CollatzResearch.WordTrace tailWord_1692756 prefixEnd_1692756 869197458782284318065163 := by
  unfold tailWord_1692756
  simp only [CollatzResearch.WordTrace]
  refine ⟨30869941727720793276753061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41159922303627724369004081 30869941727720793276753061)
  ·
    refine ⟨5788114073947648739391199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30869941727720793276753061 5788114073947648739391199)
    ·
      refine ⟨8682171110921473109086799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5788114073947648739391199 8682171110921473109086799)
      ·
        refine ⟨13023256666382209663630199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8682171110921473109086799 13023256666382209663630199)
        ·
          refine ⟨19534884999573314495445299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13023256666382209663630199 19534884999573314495445299)
          ·
            refine ⟨29302327499359971743167949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19534884999573314495445299 29302327499359971743167949)
            ·
              refine ⟨10988372812259989403687981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29302327499359971743167949 10988372812259989403687981)
              ·
                refine ⟨4120639804597496026382993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10988372812259989403687981 4120639804597496026382993)
                ·
                  refine ⟨3090479853448122019787245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4120639804597496026382993 3090479853448122019787245)
                  ·
                    refine ⟨1158929945043045757420217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3090479853448122019787245 1158929945043045757420217)
                    ·
                      refine ⟨869197458782284318065163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1158929945043045757420217 869197458782284318065163)
                      ·
                        rfl

theorem cell23_1692756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_1692756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692756 prefixEnd_1692756 := by exact prefixLift 1692756
  have htrace : WordTrace (prefixWord ++ tailWord_1692756) baseStart_1692756 baseEnd_1692756 := by
    simpa [prefixWord, tailWord_1692756, baseEnd_1692756] using wordTrace_append hprefix tailTrace_1692756
  have hstable : (prefixWord ++ tailWord_1692756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692756).length < 2 ^ (prefixWord ++ tailWord_1692756).sum := by decide
  have hdescent : baseEnd_1692756 < baseStart_1692756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692769 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_1692769 : Nat := 118140960795 + 1692769 * 2 ^ 59
def prefixEnd_1692769 : Nat := 4983230072969 + 3 ^ 40 * 1692769 * 2
def baseEnd_1692769 : Nat := 869204134030792767202603

theorem tailTrace_1692769 : CollatzResearch.WordTrace tailWord_1692769 prefixEnd_1692769 869204134030792767202603 := by
  unfold tailWord_1692769
  simp only [CollatzResearch.WordTrace]
  refine ⟨61740357604394489773729361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41160238402929659849152907 61740357604394489773729361)
  ·
    refine ⟨46305268203295867330297021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61740357604394489773729361 46305268203295867330297021)
    ·
      refine ⟨17364475576235950248861383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46305268203295867330297021 17364475576235950248861383)
      ·
        refine ⟨26046713364353925373292075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17364475576235950248861383 26046713364353925373292075)
        ·
          refine ⟨39070070046530888059938113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26046713364353925373292075 39070070046530888059938113)
          ·
            refine ⟨29302552534898166044953585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39070070046530888059938113 29302552534898166044953585)
            ·
              refine ⟨21976914401173624533715189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29302552534898166044953585 21976914401173624533715189)
              ·
                refine ⟨2060335725110027300035799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21976914401173624533715189 2060335725110027300035799)
                ·
                  refine ⟨3090503587665040950053699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060335725110027300035799 3090503587665040950053699)
                  ·
                    refine ⟨4635755381497561425080549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3090503587665040950053699 4635755381497561425080549)
                    ·
                      refine ⟨869204134030792767202603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4635755381497561425080549 869204134030792767202603)
                      ·
                        rfl

theorem cell23_1692769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_1692769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692769 prefixEnd_1692769 := by exact prefixLift 1692769
  have htrace : WordTrace (prefixWord ++ tailWord_1692769) baseStart_1692769 baseEnd_1692769 := by
    simpa [prefixWord, tailWord_1692769, baseEnd_1692769] using wordTrace_append hprefix tailTrace_1692769
  have hstable : (prefixWord ++ tailWord_1692769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692769).length < 2 ^ (prefixWord ++ tailWord_1692769).sum := by decide
  have hdescent : baseEnd_1692769 < baseStart_1692769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692792 : List Nat := [2, 1, 2, 1, 1, 1, 7, 8]
def baseStart_1692792 : Nat := 118140960795 + 1692792 * 2 ^ 59
def prefixEnd_1692792 : Nat := 4983230072969 + 3 ^ 40 * 1692792 * 2
def baseEnd_1692792 : Nat := 32193183114290599156111

theorem tailTrace_1692792 : CollatzResearch.WordTrace tailWord_1692792 prefixEnd_1692792 32193183114290599156111 := by
  unfold tailWord_1692792
  simp only [CollatzResearch.WordTrace]
  refine ⟨30870598241655582350908315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41160797655540776467877753 30870598241655582350908315)
  ·
    refine ⟨46305897362483373526362473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30870598241655582350908315 46305897362483373526362473)
    ·
      refine ⟨34729423021862530144771855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46305897362483373526362473 34729423021862530144771855)
      ·
        refine ⟨52094134532793795217157783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34729423021862530144771855 52094134532793795217157783)
        ·
          refine ⟨78141201799190692825736675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52094134532793795217157783 78141201799190692825736675)
          ·
            refine ⟨117211802698786039238605013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78141201799190692825736675 117211802698786039238605013)
            ·
              refine ⟨2747151625752797794654805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 117211802698786039238605013 2747151625752797794654805)
              ·
                refine ⟨32193183114290599156111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2747151625752797794654805 32193183114290599156111)
                ·
                  rfl

theorem cell23_1692792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 8].length) (baseStart_1692792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692792 prefixEnd_1692792 := by exact prefixLift 1692792
  have htrace : WordTrace (prefixWord ++ tailWord_1692792) baseStart_1692792 baseEnd_1692792 := by
    simpa [prefixWord, tailWord_1692792, baseEnd_1692792] using wordTrace_append hprefix tailTrace_1692792
  have hstable : (prefixWord ++ tailWord_1692792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692792).length < 2 ^ (prefixWord ++ tailWord_1692792).sum := by decide
  have hdescent : baseEnd_1692792 < baseStart_1692792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692809 : List Nat := [1, 2, 1, 1, 4, 4, 3, 7]
def baseStart_1692809 : Nat := 118140960795 + 1692809 * 2 ^ 59
def prefixEnd_1692809 : Nat := 4983230072969 + 3 ^ 40 * 1692809 * 2
def baseEnd_1692809 : Nat := 32193506416924911507497

theorem tailTrace_1692809 : CollatzResearch.WordTrace tailWord_1692809 prefixEnd_1692809 32193506416924911507497 := by
  unfold tailWord_1692809
  simp only [CollatzResearch.WordTrace]
  refine ⟨61741816524249576605185481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41161211016166384403456987 61741816524249576605185481)
  ·
    refine ⟨46306362393187182453889111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61741816524249576605185481 46306362393187182453889111)
    ·
      refine ⟨69459543589780773680833667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46306362393187182453889111 69459543589780773680833667)
      ·
        refine ⟨104189315384671160521250501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69459543589780773680833667 104189315384671160521250501)
        ·
          refine ⟨19535496634625842597734469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104189315384671160521250501 19535496634625842597734469)
          ·
            refine ⟨3662905618992345487075213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19535496634625842597734469 3662905618992345487075213)
            ·
              refine ⟨1373589607122129557653205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3662905618992345487075213 1373589607122129557653205)
              ·
                refine ⟨32193506416924911507497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1373589607122129557653205 32193506416924911507497)
                ·
                  rfl

theorem cell23_1692809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 7].length) (baseStart_1692809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692809 prefixEnd_1692809 := by exact prefixLift 1692809
  have htrace : WordTrace (prefixWord ++ tailWord_1692809) baseStart_1692809 baseEnd_1692809 := by
    simpa [prefixWord, tailWord_1692809, baseEnd_1692809] using wordTrace_append hprefix tailTrace_1692809
  have hstable : (prefixWord ++ tailWord_1692809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692809).length < 2 ^ (prefixWord ++ tailWord_1692809).sum := by decide
  have hdescent : baseEnd_1692809 < baseStart_1692809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692819 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 3]
def baseStart_1692819 : Nat := 118140960795 + 1692819 * 2 ^ 59
def prefixEnd_1692819 : Nat := 4983230072969 + 3 ^ 40 * 1692819 * 2
def baseEnd_1692819 : Nat := 869229808063517571577373

theorem tailTrace_1692819 : CollatzResearch.WordTrace tailWord_1692819 prefixEnd_1692819 869229808063517571577373 := by
  unfold tailWord_1692819
  simp only [CollatzResearch.WordTrace]
  refine ⟨61742181254213348313049511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41161454169475565542033007 61742181254213348313049511)
  ·
    refine ⟨92613271881320022469574267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61742181254213348313049511 92613271881320022469574267)
    ·
      refine ⟨138919907821980033704361401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92613271881320022469574267 138919907821980033704361401)
      ·
        refine ⟨104189930866485025278271051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138919907821980033704361401 104189930866485025278271051)
        ·
          refine ⟨156284896299727537917406577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104189930866485025278271051 156284896299727537917406577)
          ·
            refine ⟨117213672224795653438054933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156284896299727537917406577 117213672224795653438054933)
            ·
              refine ⟨5494390885537296254908825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117213672224795653438054933 5494390885537296254908825)
              ·
                refine ⟨4120793164152972191181619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5494390885537296254908825 4120793164152972191181619)
                ·
                  refine ⟨6181189746229458286772429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120793164152972191181619 6181189746229458286772429)
                  ·
                    refine ⟨2317946154836046857539661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6181189746229458286772429 2317946154836046857539661)
                    ·
                      refine ⟨869229808063517571577373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2317946154836046857539661 869229808063517571577373)
                      ·
                        rfl

theorem cell23_1692819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_1692819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692819 prefixEnd_1692819 := by exact prefixLift 1692819
  have htrace : WordTrace (prefixWord ++ tailWord_1692819) baseStart_1692819 baseEnd_1692819 := by
    simpa [prefixWord, tailWord_1692819, baseEnd_1692819] using wordTrace_append hprefix tailTrace_1692819
  have hstable : (prefixWord ++ tailWord_1692819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692819).length < 2 ^ (prefixWord ++ tailWord_1692819).sum := by decide
  have hdescent : baseEnd_1692819 < baseStart_1692819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692823 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 1, 2, 3]
def baseStart_1692823 : Nat := 118140960795 + 1692823 * 2 ^ 59
def prefixEnd_1692823 : Nat := 4983230072969 + 3 ^ 40 * 1692823 * 2
def baseEnd_1692823 : Nat := 869231861986135555927355

theorem tailTrace_1692823 : CollatzResearch.WordTrace tailWord_1692823 prefixEnd_1692823 869231861986135555927355 := by
  unfold tailWord_1692823
  simp only [CollatzResearch.WordTrace]
  refine ⟨61742327146198856996195123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41161551430799237997463415 61742327146198856996195123)
  ·
    refine ⟨92613490719298285494292685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61742327146198856996195123 92613490719298285494292685)
    ·
      refine ⟨34730059019736857060359757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92613490719298285494292685 34730059019736857060359757)
      ·
        refine ⟨13023772132401321397634909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34730059019736857060359757 13023772132401321397634909)
        ·
          refine ⟨4883914549650495524113091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13023772132401321397634909 4883914549650495524113091)
          ·
            refine ⟨7325871824475743286169637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883914549650495524113091 7325871824475743286169637)
            ·
              refine ⟨1373600967089201866156807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7325871824475743286169637 1373600967089201866156807)
              ·
                refine ⟨2060401450633802799235211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373600967089201866156807 2060401450633802799235211)
                ·
                  refine ⟨3090602175950704198852817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060401450633802799235211 3090602175950704198852817)
                  ·
                    refine ⟨2317951631963028149139613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3090602175950704198852817 2317951631963028149139613)
                    ·
                      refine ⟨869231861986135555927355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2317951631963028149139613 869231861986135555927355)
                      ·
                        rfl

theorem cell23_1692823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_1692823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692823 prefixEnd_1692823 := by exact prefixLift 1692823
  have htrace : WordTrace (prefixWord ++ tailWord_1692823) baseStart_1692823 baseEnd_1692823 := by
    simpa [prefixWord, tailWord_1692823, baseEnd_1692823] using wordTrace_append hprefix tailTrace_1692823
  have hstable : (prefixWord ++ tailWord_1692823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692823).length < 2 ^ (prefixWord ++ tailWord_1692823).sum := by decide
  have hdescent : baseEnd_1692823 < baseStart_1692823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692830 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1692830 : Nat := 118140960795 + 1692830 * 2 ^ 59
def prefixEnd_1692830 : Nat := 4983230072969 + 3 ^ 40 * 1692830 * 2
def baseEnd_1692830 : Nat := 289745152116905676179941

theorem tailTrace_1692830 : CollatzResearch.WordTrace tailWord_1692830 prefixEnd_1692830 289745152116905676179941 := by
  unfold tailWord_1692830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7717822807146687148962493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41161721638115664794466629 7717822807146687148962493)
  ·
    refine ⟨2894183552680007680860935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7717822807146687148962493 2894183552680007680860935)
    ·
      refine ⟨4341275329020011521291403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2894183552680007680860935 4341275329020011521291403)
      ·
        refine ⟨6511912993530017281937105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341275329020011521291403 6511912993530017281937105)
        ·
          refine ⟨4883934745147512961452829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6511912993530017281937105 4883934745147512961452829)
          ·
            refine ⟨1831475529430317360544811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4883934745147512961452829 1831475529430317360544811)
            ·
              refine ⟨2747213294145476040817217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831475529430317360544811 2747213294145476040817217)
              ·
                refine ⟨2060409970609107030612913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747213294145476040817217 2060409970609107030612913)
                ·
                  refine ⟨1545307477956830272959685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2060409970609107030612913 1545307477956830272959685)
                  ·
                    refine ⟨289745152116905676179941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1545307477956830272959685 289745152116905676179941)
                    ·
                      rfl

theorem cell23_1692830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1692830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692830 prefixEnd_1692830 := by exact prefixLift 1692830
  have htrace : WordTrace (prefixWord ++ tailWord_1692830) baseStart_1692830 baseEnd_1692830 := by
    simpa [prefixWord, tailWord_1692830, baseEnd_1692830] using wordTrace_append hprefix tailTrace_1692830
  have hstable : (prefixWord ++ tailWord_1692830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692830).length < 2 ^ (prefixWord ++ tailWord_1692830).sum := by decide
  have hdescent : baseEnd_1692830 < baseStart_1692830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692939 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 5]
def baseStart_1692939 : Nat := 118140960795 + 1692939 * 2 ^ 59
def prefixEnd_1692939 : Nat := 4983230072969 + 3 ^ 40 * 1692939 * 2
def baseEnd_1692939 : Nat := 869291425742057102076821

theorem tailTrace_1692939 : CollatzResearch.WordTrace tailWord_1692939 prefixEnd_1692939 869291425742057102076821 := by
  unfold tailWord_1692939
  simp only [CollatzResearch.WordTrace]
  refine ⟨61746558013778608807417871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41164372009185739204945247 61746558013778608807417871)
  ·
    refine ⟨92619837020667913211126807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61746558013778608807417871 92619837020667913211126807)
    ·
      refine ⟨138929755531001869816690211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92619837020667913211126807 138929755531001869816690211)
      ·
        refine ⟨208394633296502804725035317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138929755531001869816690211 208394633296502804725035317)
        ·
          refine ⟨19536996871547137942972061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208394633296502804725035317 19536996871547137942972061)
          ·
            refine ⟨7326373826830176728614523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19536996871547137942972061 7326373826830176728614523)
            ·
              refine ⟨10989560740245265092921785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7326373826830176728614523 10989560740245265092921785)
              ·
                refine ⟨8242170555183948819691339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10989560740245265092921785 8242170555183948819691339)
                ·
                  refine ⟨12363255832775923229537009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242170555183948819691339 12363255832775923229537009)
                  ·
                    refine ⟨9272441874581942422152757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12363255832775923229537009 9272441874581942422152757)
                    ·
                      refine ⟨869291425742057102076821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9272441874581942422152757 869291425742057102076821)
                      ·
                        rfl

theorem cell23_1692939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_1692939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692939 prefixEnd_1692939 := by exact prefixLift 1692939
  have htrace : WordTrace (prefixWord ++ tailWord_1692939) baseStart_1692939 baseEnd_1692939 := by
    simpa [prefixWord, tailWord_1692939, baseEnd_1692939] using wordTrace_append hprefix tailTrace_1692939
  have hstable : (prefixWord ++ tailWord_1692939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692939).length < 2 ^ (prefixWord ++ tailWord_1692939).sum := by decide
  have hdescent : baseEnd_1692939 < baseStart_1692939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692949 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_1692949 : Nat := 118140960795 + 1692949 * 2 ^ 59
def prefixEnd_1692949 : Nat := 4983230072969 + 3 ^ 40 * 1692949 * 2
def baseEnd_1692949 : Nat := 869296560548602062951775

theorem tailTrace_1692949 : CollatzResearch.WordTrace tailWord_1692949 prefixEnd_1692949 869296560548602062951775 := by
  unfold tailWord_1692949
  simp only [CollatzResearch.WordTrace]
  refine ⟨61746922743742380515281901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41164615162494920343521267 61746922743742380515281901)
  ·
    refine ⟨23155096028903392693230713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61746922743742380515281901 23155096028903392693230713)
    ·
      refine ⟨17366322021677544519923035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23155096028903392693230713 17366322021677544519923035)
      ·
        refine ⟨26049483032516316779884553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17366322021677544519923035 26049483032516316779884553)
        ·
          refine ⟨19537112274387237584913415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26049483032516316779884553 19537112274387237584913415)
          ·
            refine ⟨29305668411580856377370123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19537112274387237584913415 29305668411580856377370123)
            ·
              refine ⟨43958502617371284566055185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29305668411580856377370123 43958502617371284566055185)
              ·
                refine ⟨32968876963028463424541389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43958502617371284566055185 32968876963028463424541389)
                ·
                  refine ⟨12363328861135673784203021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32968876963028463424541389 12363328861135673784203021)
                  ·
                    refine ⟨4636248322925877669076133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12363328861135673784203021 4636248322925877669076133)
                    ·
                      refine ⟨869296560548602062951775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4636248322925877669076133 869296560548602062951775)
                      ·
                        rfl

theorem cell23_1692949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_1692949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692949 prefixEnd_1692949 := by exact prefixLift 1692949
  have htrace : WordTrace (prefixWord ++ tailWord_1692949) baseStart_1692949 baseEnd_1692949 := by
    simpa [prefixWord, tailWord_1692949, baseEnd_1692949] using wordTrace_append hprefix tailTrace_1692949
  have hstable : (prefixWord ++ tailWord_1692949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692949).length < 2 ^ (prefixWord ++ tailWord_1692949).sum := by decide
  have hdescent : baseEnd_1692949 < baseStart_1692949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692969 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 3]
def baseStart_1692969 : Nat := 118140960795 + 1692969 * 2 ^ 59
def prefixEnd_1692969 : Nat := 4983230072969 + 3 ^ 40 * 1692969 * 2
def baseEnd_1692969 : Nat := 869306830161691984701683

theorem tailTrace_1692969 : CollatzResearch.WordTrace tailWord_1692969 prefixEnd_1692969 869306830161691984701683 := by
  unfold tailWord_1692969
  simp only [CollatzResearch.WordTrace]
  refine ⟨61747652203669923931009961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41165101469113282620673307 61747652203669923931009961)
  ·
    refine ⟨46310739152752442948257471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61747652203669923931009961 46310739152752442948257471)
    ·
      refine ⟨69466108729128664422386207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46310739152752442948257471 69466108729128664422386207)
      ·
        refine ⟨104199163093692996633579311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69466108729128664422386207 104199163093692996633579311)
        ·
          refine ⟨156298744640539494950368967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104199163093692996633579311 156298744640539494950368967)
          ·
            refine ⟨234448116960809242425553451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156298744640539494950368967 234448116960809242425553451)
            ·
              refine ⟨351672175441213863638330177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234448116960809242425553451 351672175441213863638330177)
              ·
                refine ⟨263754131580910397728747633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351672175441213863638330177 263754131580910397728747633)
                ·
                  refine ⟨197815598685682798296560725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263754131580910397728747633 197815598685682798296560725)
                  ·
                    refine ⟨2318151547097845292537821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 197815598685682798296560725 2318151547097845292537821)
                    ·
                      refine ⟨869306830161691984701683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2318151547097845292537821 869306830161691984701683)
                      ·
                        rfl

theorem cell23_1692969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_1692969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692969 prefixEnd_1692969 := by exact prefixLift 1692969
  have htrace : WordTrace (prefixWord ++ tailWord_1692969) baseStart_1692969 baseEnd_1692969 := by
    simpa [prefixWord, tailWord_1692969, baseEnd_1692969] using wordTrace_append hprefix tailTrace_1692969
  have hstable : (prefixWord ++ tailWord_1692969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692969).length < 2 ^ (prefixWord ++ tailWord_1692969).sum := by decide
  have hdescent : baseEnd_1692969 < baseStart_1692969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692976 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 3, 4]
def baseStart_1692976 : Nat := 118140960795 + 1692976 * 2 ^ 59
def prefixEnd_1692976 : Nat := 4983230072969 + 3 ^ 40 * 1692976 * 2
def baseEnd_1692976 : Nat := 289770141508757819104717

theorem tailTrace_1692976 : CollatzResearch.WordTrace tailWord_1692976 prefixEnd_1692976 289770141508757819104717 := by
  unfold tailWord_1692976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30873953757322282063257391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41165271676429709417676521 30873953757322282063257391)
  ·
    refine ⟨46310930635983423094886087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30873953757322282063257391 46310930635983423094886087)
    ·
      refine ⟨69466395953975134642329131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46310930635983423094886087 69466395953975134642329131)
      ·
        refine ⟨104199593930962701963493697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69466395953975134642329131 104199593930962701963493697)
        ·
          refine ⟨78149695448222026472620273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104199593930962701963493697 78149695448222026472620273)
          ·
            refine ⟨58612271586166519854465205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78149695448222026472620273 58612271586166519854465205)
            ·
              refine ⟨5494900461203111236356113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58612271586166519854465205 5494900461203111236356113)
              ·
                refine ⟨4121175345902333427267085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5494900461203111236356113 4121175345902333427267085)
                ·
                  refine ⟨1545440754713375035225157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4121175345902333427267085 1545440754713375035225157)
                  ·
                    refine ⟨289770141508757819104717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1545440754713375035225157 289770141508757819104717)
                    ·
                      rfl

theorem cell23_1692976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 4].length) (baseStart_1692976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692976 prefixEnd_1692976 := by exact prefixLift 1692976
  have htrace : WordTrace (prefixWord ++ tailWord_1692976) baseStart_1692976 baseEnd_1692976 := by
    simpa [prefixWord, tailWord_1692976, baseEnd_1692976] using wordTrace_append hprefix tailTrace_1692976
  have hstable : (prefixWord ++ tailWord_1692976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692976).length < 2 ^ (prefixWord ++ tailWord_1692976).sum := by decide
  have hdescent : baseEnd_1692976 < baseStart_1692976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692986 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_1692986 : Nat := 118140960795 + 1692986 * 2 ^ 59
def prefixEnd_1692986 : Nat := 4983230072969 + 3 ^ 40 * 1692986 * 2
def baseEnd_1692986 : Nat := 869315559332818418189105

theorem tailTrace_1692986 : CollatzResearch.WordTrace tailWord_1692986 prefixEnd_1692986 869315559332818418189105 := by
  unfold tailWord_1692986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15437068061152083958594703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41165514829738890556252541 15437068061152083958594703)
  ·
    refine ⟨23155602091728125937892055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15437068061152083958594703 23155602091728125937892055)
    ·
      refine ⟨34733403137592188906838083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23155602091728125937892055 34733403137592188906838083)
      ·
        refine ⟨52100104706388283360257125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34733403137592188906838083 52100104706388283360257125)
        ·
          refine ⟨9768769632447803130048211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52100104706388283360257125 9768769632447803130048211)
          ·
            refine ⟨14653154448671704695072317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9768769632447803130048211 14653154448671704695072317)
            ·
              refine ⟨5494932918251889260652119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14653154448671704695072317 5494932918251889260652119)
              ·
                refine ⟨8242399377377833890978179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5494932918251889260652119 8242399377377833890978179)
                ·
                  refine ⟨12363599066066750836467269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242399377377833890978179 12363599066066750836467269)
                  ·
                    refine ⟨2318174824887515781837613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12363599066066750836467269 2318174824887515781837613)
                    ·
                      refine ⟨869315559332818418189105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2318174824887515781837613 869315559332818418189105)
                      ·
                        rfl

theorem cell23_1692986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_1692986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1692986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1692986 prefixEnd_1692986 := by exact prefixLift 1692986
  have htrace : WordTrace (prefixWord ++ tailWord_1692986) baseStart_1692986 baseEnd_1692986 := by
    simpa [prefixWord, tailWord_1692986, baseEnd_1692986] using wordTrace_append hprefix tailTrace_1692986
  have hstable : (prefixWord ++ tailWord_1692986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692986).length < 2 ^ (prefixWord ++ tailWord_1692986).sum := by decide
  have hdescent : baseEnd_1692986 < baseStart_1692986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693009 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_1693009 : Nat := 118140960795 + 1693009 * 2 ^ 59
def prefixEnd_1693009 : Nat := 4983230072969 + 3 ^ 40 * 1693009 * 2
def baseEnd_1693009 : Nat := 869327369387871828201499

theorem tailTrace_1693009 : CollatzResearch.WordTrace tailWord_1693009 prefixEnd_1693009 869327369387871828201499 := by
  unfold tailWord_1693009
  simp only [CollatzResearch.WordTrace]
  refine ⟨61749111123525010762466081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41166074082350007174977387 61749111123525010762466081)
  ·
    refine ⟨46311833342643758071849561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61749111123525010762466081 46311833342643758071849561)
    ·
      refine ⟨34733875006982818553887171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46311833342643758071849561 34733875006982818553887171)
      ·
        refine ⟨52100812510474227830830757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34733875006982818553887171 52100812510474227830830757)
        ·
          refine ⟨9768902345713917718280767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52100812510474227830830757 9768902345713917718280767)
          ·
            refine ⟨14653353518570876577421151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9768902345713917718280767 14653353518570876577421151)
            ·
              refine ⟨21980030277856314866131727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14653353518570876577421151 21980030277856314866131727)
              ·
                refine ⟨32970045416784472299197591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21980030277856314866131727 32970045416784472299197591)
                ·
                  refine ⟨49455068125176708448796387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32970045416784472299197591 49455068125176708448796387)
                  ·
                    refine ⟨74182602187765062673194581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49455068125176708448796387 74182602187765062673194581)
                    ·
                      refine ⟨869327369387871828201499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 74182602187765062673194581 869327369387871828201499)
                      ·
                        rfl

theorem cell23_1693009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_1693009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693009 prefixEnd_1693009 := by exact prefixLift 1693009
  have htrace : WordTrace (prefixWord ++ tailWord_1693009) baseStart_1693009 baseEnd_1693009 := by
    simpa [prefixWord, tailWord_1693009, baseEnd_1693009] using wordTrace_append hprefix tailTrace_1693009
  have hstable : (prefixWord ++ tailWord_1693009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693009).length < 2 ^ (prefixWord ++ tailWord_1693009).sum := by decide
  have hdescent : baseEnd_1693009 < baseStart_1693009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693026 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1693026 : Nat := 118140960795 + 1693026 * 2 ^ 59
def prefixEnd_1693026 : Nat := 4983230072969 + 3 ^ 40 * 1693026 * 2
def baseEnd_1693026 : Nat := 869336098558998261688921

theorem tailTrace_1693026 : CollatzResearch.WordTrace tailWord_1693026 prefixEnd_1693026 869336098558998261688921 := by
  unfold tailWord_1693026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15437432791115855666458733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41166487442975615110556621 15437432791115855666458733)
  ·
    refine ⟨5789037296668445874922025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15437432791115855666458733 5789037296668445874922025)
    ·
      refine ⟨4341777972501334406191519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5789037296668445874922025 4341777972501334406191519)
      ·
        refine ⟨6512666958752001609287279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341777972501334406191519 6512666958752001609287279)
        ·
          refine ⟨9769000438128002413930919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6512666958752001609287279 9769000438128002413930919)
          ·
            refine ⟨14653500657192003620896379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9769000438128002413930919 14653500657192003620896379)
            ·
              refine ⟨21980250985788005431344569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14653500657192003620896379 21980250985788005431344569)
              ·
                refine ⟨16485188239341004073508427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21980250985788005431344569 16485188239341004073508427)
                ·
                  refine ⟨24727782359011506110262641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16485188239341004073508427 24727782359011506110262641)
                  ·
                    refine ⟨18545836769258629582696981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24727782359011506110262641 18545836769258629582696981)
                    ·
                      refine ⟨869336098558998261688921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18545836769258629582696981 869336098558998261688921)
                      ·
                        rfl

theorem cell23_1693026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1693026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693026 prefixEnd_1693026 := by exact prefixLift 1693026
  have htrace : WordTrace (prefixWord ++ tailWord_1693026) baseStart_1693026 baseEnd_1693026 := by
    simpa [prefixWord, tailWord_1693026, baseEnd_1693026] using wordTrace_append hprefix tailTrace_1693026
  have hstable : (prefixWord ++ tailWord_1693026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693026).length < 2 ^ (prefixWord ++ tailWord_1693026).sum := by decide
  have hdescent : baseEnd_1693026 < baseStart_1693026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693060 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_1693060 : Nat := 118140960795 + 1693060 * 2 ^ 59
def prefixEnd_1693060 : Nat := 4983230072969 + 3 ^ 40 * 1693060 * 2
def baseEnd_1693060 : Nat := 869353556901251128663765

theorem tailTrace_1693060 : CollatzResearch.WordTrace tailWord_1693060 prefixEnd_1693060 869353556901251128663765 := by
  unfold tailWord_1693060
  simp only [CollatzResearch.WordTrace]
  refine ⟨30875485623170123236286317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41167314164226830981715089 30875485623170123236286317)
  ·
    refine ⟨11578307108688796213607369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30875485623170123236286317 11578307108688796213607369)
    ·
      refine ⟨8683730331516597160205527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11578307108688796213607369 8683730331516597160205527)
      ·
        refine ⟨13025595497274895740308291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8683730331516597160205527 13025595497274895740308291)
        ·
          refine ⟨19538393245912343610462437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13025595497274895740308291 19538393245912343610462437)
          ·
            refine ⟨3663448733608564426961707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19538393245912343610462437 3663448733608564426961707)
            ·
              refine ⟨5495173100412846640442561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663448733608564426961707 5495173100412846640442561)
              ·
                refine ⟨4121379825309634980331921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5495173100412846640442561 4121379825309634980331921)
                ·
                  refine ⟨3091034868982226235248941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4121379825309634980331921 3091034868982226235248941)
                  ·
                    refine ⟨1159138075868334838218353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3091034868982226235248941 1159138075868334838218353)
                    ·
                      refine ⟨869353556901251128663765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159138075868334838218353 869353556901251128663765)
                      ·
                        rfl

theorem cell23_1693060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_1693060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693060 prefixEnd_1693060 := by exact prefixLift 1693060
  have htrace : WordTrace (prefixWord ++ tailWord_1693060) baseStart_1693060 baseEnd_1693060 := by
    simpa [prefixWord, tailWord_1693060, baseEnd_1693060] using wordTrace_append hprefix tailTrace_1693060
  have hstable : (prefixWord ++ tailWord_1693060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693060).length < 2 ^ (prefixWord ++ tailWord_1693060).sum := by decide
  have hdescent : baseEnd_1693060 < baseStart_1693060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693067 : List Nat := [1, 1, 1, 1, 4, 3, 5, 2, 1, 1, 3]
def baseStart_1693067 : Nat := 118140960795 + 1693067 * 2 ^ 59
def prefixEnd_1693067 : Nat := 4983230072969 + 3 ^ 40 * 1693067 * 2
def baseEnd_1693067 : Nat := 869357151265832601276233

theorem tailTrace_1693067 : CollatzResearch.WordTrace tailWord_1693067 prefixEnd_1693067 869357151265832601276233 := by
  unfold tailWord_1693067
  simp only [CollatzResearch.WordTrace]
  refine ⟨61751226557314886668077455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41167484371543257778718303 61751226557314886668077455)
  ·
    refine ⟨92626839835972330002116183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61751226557314886668077455 92626839835972330002116183)
    ·
      refine ⟨138940259753958495003174275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92626839835972330002116183 138940259753958495003174275)
      ·
        refine ⟨208410389630937742504761413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138940259753958495003174275 208410389630937742504761413)
        ·
          refine ⟨39076948055800826719642765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208410389630937742504761413 39076948055800826719642765)
          ·
            refine ⟨14653855520925310019866037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39076948055800826719642765 14653855520925310019866037)
            ·
              refine ⟨1373798955086747814362441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14653855520925310019866037 1373798955086747814362441)
              ·
                refine ⟨1030349216315060860771831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373798955086747814362441 1030349216315060860771831)
                ·
                  refine ⟨1545523824472591291157747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030349216315060860771831 1545523824472591291157747)
                  ·
                    refine ⟨2318285736708886936736621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1545523824472591291157747 2318285736708886936736621)
                    ·
                      refine ⟨869357151265832601276233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2318285736708886936736621 869357151265832601276233)
                      ·
                        rfl

theorem cell23_1693067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 1, 3].length) (baseStart_1693067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693067 prefixEnd_1693067 := by exact prefixLift 1693067
  have htrace : WordTrace (prefixWord ++ tailWord_1693067) baseStart_1693067 baseEnd_1693067 := by
    simpa [prefixWord, tailWord_1693067, baseEnd_1693067] using wordTrace_append hprefix tailTrace_1693067
  have hstable : (prefixWord ++ tailWord_1693067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693067).length < 2 ^ (prefixWord ++ tailWord_1693067).sum := by decide
  have hdescent : baseEnd_1693067 < baseStart_1693067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693074 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 6]
def baseStart_1693074 : Nat := 118140960795 + 1693074 * 2 ^ 59
def prefixEnd_1693074 : Nat := 4983230072969 + 3 ^ 40 * 1693074 * 2
def baseEnd_1693074 : Nat := 96595638403379341543189

theorem tailTrace_1693074 : CollatzResearch.WordTrace tailWord_1693074 prefixEnd_1693074 96595638403379341543189 := by
  unfold tailWord_1693074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15437870467072381715895569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41167654578859684575721517 15437870467072381715895569)
  ·
    refine ⟨11578402850304286286921677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15437870467072381715895569 11578402850304286286921677)
    ·
      refine ⟨4341901068864107357595629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11578402850304286286921677 4341901068864107357595629)
      ·
        refine ⟨1628212900824040259098361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4341901068864107357595629 1628212900824040259098361)
        ·
          refine ⟨1221159675618030194323771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1628212900824040259098361 1221159675618030194323771)
          ·
            refine ⟨1831739513427045291485657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221159675618030194323771 1831739513427045291485657)
            ·
              refine ⟨1373804635070283968614243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831739513427045291485657 1373804635070283968614243)
              ·
                refine ⟨2060706952605425952921365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373804635070283968614243 2060706952605425952921365)
                ·
                  refine ⟨96595638403379341543189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2060706952605425952921365 96595638403379341543189)
                  ·
                    rfl

theorem cell23_1693074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_1693074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693074 prefixEnd_1693074 := by exact prefixLift 1693074
  have htrace : WordTrace (prefixWord ++ tailWord_1693074) baseStart_1693074 baseEnd_1693074 := by
    simpa [prefixWord, tailWord_1693074, baseEnd_1693074] using wordTrace_append hprefix tailTrace_1693074
  have hstable : (prefixWord ++ tailWord_1693074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693074).length < 2 ^ (prefixWord ++ tailWord_1693074).sum := by decide
  have hdescent : baseEnd_1693074 < baseStart_1693074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693090 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1693090 : Nat := 118140960795 + 1693090 * 2 ^ 59
def prefixEnd_1693090 : Nat := 4983230072969 + 3 ^ 40 * 1693090 * 2
def baseEnd_1693090 : Nat := 869368961320886011288627

theorem tailTrace_1693090 : CollatzResearch.WordTrace tailWord_1693090 prefixEnd_1693090 869368961320886011288627 := by
  unfold tailWord_1693090
  simp only [CollatzResearch.WordTrace]
  refine ⟨15438016359057890399041181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41168043624154374397443149 15438016359057890399041181)
  ·
    refine ⟨5789256134646708899640443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15438016359057890399041181 5789256134646708899640443)
    ·
      refine ⟨8683884201970063349460665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5789256134646708899640443 8683884201970063349460665)
      ·
        refine ⟨6512913151477547512095499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8683884201970063349460665 6512913151477547512095499)
        ·
          refine ⟨9769369727216321268143249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6512913151477547512095499 9769369727216321268143249)
          ·
            refine ⟨7327027295412240951107437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9769369727216321268143249 7327027295412240951107437)
            ·
              refine ⟨2747635235779590356665289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7327027295412240951107437 2747635235779590356665289)
              ·
                refine ⟨2060726426834692767498967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747635235779590356665289 2060726426834692767498967)
                ·
                  refine ⟨3091089640252039151248451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060726426834692767498967 3091089640252039151248451)
                  ·
                    refine ⟨4636634460378058726872677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091089640252039151248451 4636634460378058726872677)
                    ·
                      refine ⟨869368961320886011288627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4636634460378058726872677 869368961320886011288627)
                      ·
                        rfl

theorem cell23_1693090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1693090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693090 prefixEnd_1693090 := by exact prefixLift 1693090
  have htrace : WordTrace (prefixWord ++ tailWord_1693090) baseStart_1693090 baseEnd_1693090 := by
    simpa [prefixWord, tailWord_1693090, baseEnd_1693090] using wordTrace_append hprefix tailTrace_1693090
  have hstable : (prefixWord ++ tailWord_1693090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693090).length < 2 ^ (prefixWord ++ tailWord_1693090).sum := by decide
  have hdescent : baseEnd_1693090 < baseStart_1693090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693093 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 3]
def baseStart_1693093 : Nat := 118140960795 + 1693093 * 2 ^ 59
def prefixEnd_1693093 : Nat := 4983230072969 + 3 ^ 40 * 1693093 * 2
def baseEnd_1693093 : Nat := 869370501762849499551113

theorem tailTrace_1693093 : CollatzResearch.WordTrace tailWord_1693093 prefixEnd_1693093 869370501762849499551113 := by
  unfold tailWord_1693093
  simp only [CollatzResearch.WordTrace]
  refine ⟨61752174855220693108523933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41168116570147128739015955 61752174855220693108523933)
  ·
    refine ⟨23157065570707759915696475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61752174855220693108523933 23157065570707759915696475)
    ·
      refine ⟨34735598356061639873544713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23157065570707759915696475 34735598356061639873544713)
      ·
        refine ⟨26051698767046229905158535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34735598356061639873544713 26051698767046229905158535)
        ·
          refine ⟨39077548150569344857737803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26051698767046229905158535 39077548150569344857737803)
          ·
            refine ⟨58616322225854017286606705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39077548150569344857737803 58616322225854017286606705)
            ·
              refine ⟨43962241669390512964955029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58616322225854017286606705 43962241669390512964955029)
              ·
                refine ⟨2060730078252680295232267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43962241669390512964955029 2060730078252680295232267)
                ·
                  refine ⟨3091095117379020442848401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060730078252680295232267 3091095117379020442848401)
                  ·
                    refine ⟨2318321338034265332136301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3091095117379020442848401 2318321338034265332136301)
                    ·
                      refine ⟨869370501762849499551113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2318321338034265332136301 869370501762849499551113)
                      ·
                        rfl

theorem cell23_1693093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_1693093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693093 prefixEnd_1693093 := by exact prefixLift 1693093
  have htrace : WordTrace (prefixWord ++ tailWord_1693093) baseStart_1693093 baseEnd_1693093 := by
    simpa [prefixWord, tailWord_1693093, baseEnd_1693093] using wordTrace_append hprefix tailTrace_1693093
  have hstable : (prefixWord ++ tailWord_1693093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693093).length < 2 ^ (prefixWord ++ tailWord_1693093).sum := by decide
  have hdescent : baseEnd_1693093 < baseStart_1693093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693123 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 3]
def baseStart_1693123 : Nat := 118140960795 + 1693123 * 2 ^ 59
def prefixEnd_1693123 : Nat := 4983230072969 + 3 ^ 40 * 1693123 * 2
def baseEnd_1693123 : Nat := 869385906182484382175975

theorem tailTrace_1693123 : CollatzResearch.WordTrace tailWord_1693123 prefixEnd_1693123 869385906182484382175975 := by
  unfold tailWord_1693123
  simp only [CollatzResearch.WordTrace]
  refine ⟨61753269045112008232116023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41168846030074672154744015 61753269045112008232116023)
  ·
    refine ⟨92629903567668012348174035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61753269045112008232116023 92629903567668012348174035)
    ·
      refine ⟨138944855351502018522261053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92629903567668012348174035 138944855351502018522261053)
      ·
        refine ⟨52104320756813256945847895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138944855351502018522261053 52104320756813256945847895)
        ·
          refine ⟨78156481135219885418771843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52104320756813256945847895 78156481135219885418771843)
          ·
            refine ⟨117234721702829828128157765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78156481135219885418771843 117234721702829828128157765)
            ·
              refine ⟨21981510319280592774029581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117234721702829828128157765 21981510319280592774029581)
              ·
                refine ⟨8243066369730222290261093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21981510319280592774029581 8243066369730222290261093)
                ·
                  refine ⟨1545574944324416679423955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8243066369730222290261093 1545574944324416679423955)
                  ·
                    refine ⟨2318362416486625019135933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1545574944324416679423955 2318362416486625019135933)
                    ·
                      refine ⟨869385906182484382175975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2318362416486625019135933 869385906182484382175975)
                      ·
                        rfl

theorem cell23_1693123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_1693123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693123 prefixEnd_1693123 := by exact prefixLift 1693123
  have htrace : WordTrace (prefixWord ++ tailWord_1693123) baseStart_1693123 baseEnd_1693123 := by
    simpa [prefixWord, tailWord_1693123, baseEnd_1693123] using wordTrace_append hprefix tailTrace_1693123
  have hstable : (prefixWord ++ tailWord_1693123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693123).length < 2 ^ (prefixWord ++ tailWord_1693123).sum := by decide
  have hdescent : baseEnd_1693123 < baseStart_1693123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693163 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 3, 4, 2]
def baseStart_1693163 : Nat := 118140960795 + 1693163 * 2 ^ 59
def prefixEnd_1693163 : Nat := 4983230072969 + 3 ^ 40 * 1693163 * 2
def baseEnd_1693163 : Nat := 869406445408664225675791

theorem tailTrace_1693163 : CollatzResearch.WordTrace tailWord_1693163 prefixEnd_1693163 869406445408664225675791 := by
  unfold tailWord_1693163
  simp only [CollatzResearch.WordTrace]
  refine ⟨61754727964967095063572143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41169818643311396709048095 61754727964967095063572143)
  ·
    refine ⟨92632091947450642595358215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61754727964967095063572143 92632091947450642595358215)
    ·
      refine ⟨138948137921175963893037323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92632091947450642595358215 138948137921175963893037323)
      ·
        refine ⟨208422206881763945839555985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138948137921175963893037323 208422206881763945839555985)
        ·
          refine ⟨156316655161322959379666989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208422206881763945839555985 156316655161322959379666989)
          ·
            refine ⟨58618745685496109767375121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156316655161322959379666989 58618745685496109767375121)
            ·
              refine ⟨43964059264122082325531341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58618745685496109767375121 43964059264122082325531341)
              ·
                refine ⟨16486522224045780872074253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43964059264122082325531341 16486522224045780872074253)
                ·
                  refine ⟨6182445834017167827027845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16486522224045780872074253 6182445834017167827027845)
                  ·
                    refine ⟨1159208593878218967567721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6182445834017167827027845 1159208593878218967567721)
                    ·
                      refine ⟨869406445408664225675791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159208593878218967567721 869406445408664225675791)
                      ·
                        rfl

theorem cell23_1693163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 4, 2].length) (baseStart_1693163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693163 prefixEnd_1693163 := by exact prefixLift 1693163
  have htrace : WordTrace (prefixWord ++ tailWord_1693163) baseStart_1693163 baseEnd_1693163 := by
    simpa [prefixWord, tailWord_1693163, baseEnd_1693163] using wordTrace_append hprefix tailTrace_1693163
  have hstable : (prefixWord ++ tailWord_1693163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693163).length < 2 ^ (prefixWord ++ tailWord_1693163).sum := by decide
  have hdescent : baseEnd_1693163 < baseStart_1693163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693167 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 1, 3, 2]
def baseStart_1693167 : Nat := 118140960795 + 1693167 * 2 ^ 59
def prefixEnd_1693167 : Nat := 4983230072969 + 3 ^ 40 * 1693167 * 2
def baseEnd_1693167 : Nat := 869408499331282210025773

theorem tailTrace_1693167 : CollatzResearch.WordTrace tailWord_1693167 prefixEnd_1693167 869408499331282210025773 := by
  unfold tailWord_1693167
  simp only [CollatzResearch.WordTrace]
  refine ⟨61754873856952603746717755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41169915904635069164478503 61754873856952603746717755)
  ·
    refine ⟨92632310785428905620076633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61754873856952603746717755 92632310785428905620076633)
    ·
      refine ⟨69474233089071679215057475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92632310785428905620076633 69474233089071679215057475)
      ·
        refine ⟨104211349633607518822586213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69474233089071679215057475 104211349633607518822586213)
        ·
          refine ⟨19539628056301409779234915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104211349633607518822586213 19539628056301409779234915)
          ·
            refine ⟨29309442084452114668852373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19539628056301409779234915 29309442084452114668852373)
            ·
              refine ⟨1373880097708692875102455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29309442084452114668852373 1373880097708692875102455)
              ·
                refine ⟨2060820146563039312653683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373880097708692875102455 2060820146563039312653683)
                ·
                  refine ⟨3091230219844558968980525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060820146563039312653683 3091230219844558968980525)
                  ·
                    refine ⟨1159211332441709613367697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3091230219844558968980525 1159211332441709613367697)
                    ·
                      refine ⟨869408499331282210025773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159211332441709613367697 869408499331282210025773)
                      ·
                        rfl

theorem cell23_1693167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 3, 2].length) (baseStart_1693167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693167 prefixEnd_1693167 := by exact prefixLift 1693167
  have htrace : WordTrace (prefixWord ++ tailWord_1693167) baseStart_1693167 baseEnd_1693167 := by
    simpa [prefixWord, tailWord_1693167, baseEnd_1693167] using wordTrace_append hprefix tailTrace_1693167
  have hstable : (prefixWord ++ tailWord_1693167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693167).length < 2 ^ (prefixWord ++ tailWord_1693167).sum := by decide
  have hdescent : baseEnd_1693167 < baseStart_1693167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693174 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_1693174 : Nat := 118140960795 + 1693174 * 2 ^ 59
def prefixEnd_1693174 : Nat := 4983230072969 + 3 ^ 40 * 1693174 * 2
def baseEnd_1693174 : Nat := 869412093695863682638241

theorem tailTrace_1693174 : CollatzResearch.WordTrace tailWord_1693174 prefixEnd_1693174 869412093695863682638241 := by
  unfold tailWord_1693174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3859695572995452746388911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41170086111951495961481717 3859695572995452746388911)
  ·
    refine ⟨5789543359493179119583367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3859695572995452746388911 5789543359493179119583367)
    ·
      refine ⟨8684315039239768679375051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5789543359493179119583367 8684315039239768679375051)
      ·
        refine ⟨13026472558859653019062577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8684315039239768679375051 13026472558859653019062577)
        ·
          refine ⟨9769854419144739764296933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13026472558859653019062577 9769854419144739764296933)
          ·
            refine ⟨1831847703589638705805675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9769854419144739764296933 1831847703589638705805675)
            ·
              refine ⟨2747771555384458058708513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831847703589638705805675 2747771555384458058708513)
              ·
                refine ⟨2060828666538343544031385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747771555384458058708513 2060828666538343544031385)
                ·
                  refine ⟨1545621499903757658023539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2060828666538343544031385 1545621499903757658023539)
                  ·
                    refine ⟨2318432249855636487035309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1545621499903757658023539 2318432249855636487035309)
                    ·
                      refine ⟨869412093695863682638241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2318432249855636487035309 869412093695863682638241)
                      ·
                        rfl

theorem cell23_1693174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_1693174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693174 prefixEnd_1693174 := by exact prefixLift 1693174
  have htrace : WordTrace (prefixWord ++ tailWord_1693174) baseStart_1693174 baseEnd_1693174 := by
    simpa [prefixWord, tailWord_1693174, baseEnd_1693174] using wordTrace_append hprefix tailTrace_1693174
  have hstable : (prefixWord ++ tailWord_1693174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693174).length < 2 ^ (prefixWord ++ tailWord_1693174).sum := by decide
  have hdescent : baseEnd_1693174 < baseStart_1693174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693237 : List Nat := [1, 3, 3, 1, 1, 4, 3, 2, 5]
def baseStart_1693237 : Nat := 118140960795 + 1693237 * 2 ^ 59
def prefixEnd_1693237 : Nat := 4983230072969 + 3 ^ 40 * 1693237 * 2
def baseEnd_1693237 : Nat := 96604938108566326238939

theorem tailTrace_1693237 : CollatzResearch.WordTrace tailWord_1693237 prefixEnd_1693237 96604938108566326238939 := by
  unfold tailWord_1693237
  simp only [CollatzResearch.WordTrace]
  refine ⟨61757426966699005701765965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41171617977799337134510643 61757426966699005701765965)
  ·
    refine ⟨23159035112512127138162237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61757426966699005701765965 23159035112512127138162237)
    ·
      refine ⟨8684638167192047676810839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23159035112512127138162237 8684638167192047676810839)
      ·
        refine ⟨13026957250788071515216259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8684638167192047676810839 13026957250788071515216259)
        ·
          refine ⟨19540435876182107272824389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13026957250788071515216259 19540435876182107272824389)
          ·
            refine ⟨3663831726784145113654573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19540435876182107272824389 3663831726784145113654573)
            ·
              refine ⟨1373936897544054417620465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3663831726784145113654573 1373936897544054417620465)
              ·
                refine ⟨1030452673158040813215349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373936897544054417620465 1030452673158040813215349)
                ·
                  refine ⟨96604938108566326238939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1030452673158040813215349 96604938108566326238939)
                  ·
                    rfl

theorem cell23_1693237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_1693237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693237 prefixEnd_1693237 := by exact prefixLift 1693237
  have htrace : WordTrace (prefixWord ++ tailWord_1693237) baseStart_1693237 baseEnd_1693237 := by
    simpa [prefixWord, tailWord_1693237, baseEnd_1693237] using wordTrace_append hprefix tailTrace_1693237
  have hstable : (prefixWord ++ tailWord_1693237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693237).length < 2 ^ (prefixWord ++ tailWord_1693237).sum := by decide
  have hdescent : baseEnd_1693237 < baseStart_1693237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693253 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_1693253 : Nat := 118140960795 + 1693253 * 2 ^ 59
def prefixEnd_1693253 : Nat := 4983230072969 + 3 ^ 40 * 1693253 * 2
def baseEnd_1693253 : Nat := 869452658667568873550377

theorem tailTrace_1693253 : CollatzResearch.WordTrace tailWord_1693253 prefixEnd_1693253 869452658667568873550377 := by
  unfold tailWord_1693253
  simp only [CollatzResearch.WordTrace]
  refine ⟨61758010534641040434348413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41172007023094026956232275 61758010534641040434348413)
  ·
    refine ⟨23159253950490390162880655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61758010534641040434348413 23159253950490390162880655)
    ·
      refine ⟨34738880925735585244320983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23159253950490390162880655 34738880925735585244320983)
      ·
        refine ⟨52108321388603377866481475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34738880925735585244320983 52108321388603377866481475)
        ·
          refine ⟨78162482082905066799722213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52108321388603377866481475 78162482082905066799722213)
          ·
            refine ⟨14655465390544700024947915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78162482082905066799722213 14655465390544700024947915)
            ·
              refine ⟨21983198085817050037421873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14655465390544700024947915 21983198085817050037421873)
              ·
                refine ⟨16487398564362787528066405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21983198085817050037421873 16487398564362787528066405)
                ·
                  refine ⟨3091387230818022661512451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16487398564362787528066405 3091387230818022661512451)
                  ·
                    refine ⟨4637080846227033992268677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091387230818022661512451 4637080846227033992268677)
                    ·
                      refine ⟨869452658667568873550377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4637080846227033992268677 869452658667568873550377)
                      ·
                        rfl

theorem cell23_1693253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_1693253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693253 prefixEnd_1693253 := by exact prefixLift 1693253
  have htrace : WordTrace (prefixWord ++ tailWord_1693253) baseStart_1693253 baseEnd_1693253 := by
    simpa [prefixWord, tailWord_1693253, baseEnd_1693253] using wordTrace_append hprefix tailTrace_1693253
  have hstable : (prefixWord ++ tailWord_1693253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693253).length < 2 ^ (prefixWord ++ tailWord_1693253).sum := by decide
  have hdescent : baseEnd_1693253 < baseStart_1693253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693263 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 5, 4]
def baseStart_1693263 : Nat := 118140960795 + 1693263 * 2 ^ 59
def prefixEnd_1693263 : Nat := 4983230072969 + 3 ^ 40 * 1693263 * 2
def baseEnd_1693263 : Nat := 289819264491371278141777

theorem tailTrace_1693263 : CollatzResearch.WordTrace tailWord_1693263 prefixEnd_1693263 289819264491371278141777 := by
  unfold tailWord_1693263
  simp only [CollatzResearch.WordTrace]
  refine ⟨61758375264604812142212443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41172250176403208094808295 61758375264604812142212443)
  ·
    refine ⟨92637562896907218213318665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61758375264604812142212443 92637562896907218213318665)
    ·
      refine ⟨69478172172680413659988999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92637562896907218213318665 69478172172680413659988999)
      ·
        refine ⟨104217258259020620489983499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69478172172680413659988999 104217258259020620489983499)
        ·
          refine ⟨156325887388530930734975249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104217258259020620489983499 156325887388530930734975249)
          ·
            refine ⟨117244415541398198051231437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156325887388530930734975249 117244415541398198051231437)
            ·
              refine ⟨43966655828024324269211789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117244415541398198051231437 43966655828024324269211789)
              ·
                refine ⟨16487495935509121600954421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43966655828024324269211789 16487495935509121600954421)
                ·
                  refine ⟨1545702743953980150089477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16487495935509121600954421 1545702743953980150089477)
                  ·
                    refine ⟨289819264491371278141777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1545702743953980150089477 289819264491371278141777)
                    ·
                      rfl

theorem cell23_1693263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 4].length) (baseStart_1693263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693263 prefixEnd_1693263 := by exact prefixLift 1693263
  have htrace : WordTrace (prefixWord ++ tailWord_1693263) baseStart_1693263 baseEnd_1693263 := by
    simpa [prefixWord, tailWord_1693263, baseEnd_1693263] using wordTrace_append hprefix tailTrace_1693263
  have hstable : (prefixWord ++ tailWord_1693263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693263).length < 2 ^ (prefixWord ++ tailWord_1693263).sum := by decide
  have hdescent : baseEnd_1693263 < baseStart_1693263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693273 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 3]
def baseStart_1693273 : Nat := 118140960795 + 1693273 * 2 ^ 59
def prefixEnd_1693273 : Nat := 4983230072969 + 3 ^ 40 * 1693273 * 2
def baseEnd_1693273 : Nat := 869462928280658795300285

theorem tailTrace_1693273 : CollatzResearch.WordTrace tailWord_1693273 prefixEnd_1693273 869462928280658795300285 := by
  unfold tailWord_1693273
  simp only [CollatzResearch.WordTrace]
  refine ⟨61758739994568583850076473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41172493329712389233384315 61758739994568583850076473)
  ·
    refine ⟨46319054995926437887557355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61758739994568583850076473 46319054995926437887557355)
    ·
      refine ⟨69478582493889656831336033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46319054995926437887557355 69478582493889656831336033)
      ·
        refine ⟨52108936870417242623502025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69478582493889656831336033 52108936870417242623502025)
        ·
          refine ⟨39081702652812931967626519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52108936870417242623502025 39081702652812931967626519)
          ·
            refine ⟨58622553979219397951439779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39081702652812931967626519 58622553979219397951439779)
            ·
              refine ⟨87933830968829096927159669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58622553979219397951439779 87933830968829096927159669)
              ·
                refine ⟨8243796653327727836921219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87933830968829096927159669 8243796653327727836921219)
                ·
                  refine ⟨12365694979991591755381829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8243796653327727836921219 12365694979991591755381829)
                  ·
                    refine ⟨2318567808748423454134093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12365694979991591755381829 2318567808748423454134093)
                    ·
                      refine ⟨869462928280658795300285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2318567808748423454134093 869462928280658795300285)
                      ·
                        rfl

theorem cell23_1693273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_1693273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693273 prefixEnd_1693273 := by exact prefixLift 1693273
  have htrace : WordTrace (prefixWord ++ tailWord_1693273) baseStart_1693273 baseEnd_1693273 := by
    simpa [prefixWord, tailWord_1693273, baseEnd_1693273] using wordTrace_append hprefix tailTrace_1693273
  have hstable : (prefixWord ++ tailWord_1693273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693273).length < 2 ^ (prefixWord ++ tailWord_1693273).sum := by decide
  have hdescent : baseEnd_1693273 < baseStart_1693273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693303 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_1693303 : Nat := 118140960795 + 1693303 * 2 ^ 59
def prefixEnd_1693303 : Nat := 4983230072969 + 3 ^ 40 * 1693303 * 2
def baseEnd_1693303 : Nat := 869478332700293677925147

theorem tailTrace_1693303 : CollatzResearch.WordTrace tailWord_1693303 prefixEnd_1693303 869478332700293677925147 := by
  unfold tailWord_1693303
  simp only [CollatzResearch.WordTrace]
  refine ⟨61759834184459898973668563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41173222789639932649112375 61759834184459898973668563)
  ·
    refine ⟨92639751276689848460502845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61759834184459898973668563 92639751276689848460502845)
    ·
      refine ⟨34739906728758693172688567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92639751276689848460502845 34739906728758693172688567)
      ·
        refine ⟨52109860093138039759032851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34739906728758693172688567 52109860093138039759032851)
        ·
          refine ⟨78164790139707059638549277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52109860093138039759032851 78164790139707059638549277)
          ·
            refine ⟨29311796302390147364455979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78164790139707059638549277 29311796302390147364455979)
            ·
              refine ⟨43967694453585221046683969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29311796302390147364455979 43967694453585221046683969)
              ·
                refine ⟨32975770840188915785012977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43967694453585221046683969 32975770840188915785012977)
                ·
                  refine ⟨24731828130141686838759733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32975770840188915785012977 24731828130141686838759733)
                  ·
                    refine ⟨2318608887200783141133725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24731828130141686838759733 2318608887200783141133725)
                    ·
                      refine ⟨869478332700293677925147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2318608887200783141133725 869478332700293677925147)
                      ·
                        rfl

theorem cell23_1693303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_1693303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693303 prefixEnd_1693303 := by exact prefixLift 1693303
  have htrace : WordTrace (prefixWord ++ tailWord_1693303) baseStart_1693303 baseEnd_1693303 := by
    simpa [prefixWord, tailWord_1693303, baseEnd_1693303] using wordTrace_append hprefix tailTrace_1693303
  have hstable : (prefixWord ++ tailWord_1693303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693303).length < 2 ^ (prefixWord ++ tailWord_1693303).sum := by decide
  have hdescent : baseEnd_1693303 < baseStart_1693303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693323 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 3, 5]
def baseStart_1693323 : Nat := 118140960795 + 1693323 * 2 ^ 59
def prefixEnd_1693323 : Nat := 4983230072969 + 3 ^ 40 * 1693323 * 2
def baseEnd_1693323 : Nat := 289829534104461199891685

theorem tailTrace_1693323 : CollatzResearch.WordTrace tailWord_1693323 prefixEnd_1693323 289829534104461199891685 := by
  unfold tailWord_1693323
  simp only [CollatzResearch.WordTrace]
  refine ⟨61760563644387442389396623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41173709096258294926264415 61760563644387442389396623)
  ·
    refine ⟨92640845466581163584094935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61760563644387442389396623 92640845466581163584094935)
    ·
      refine ⟨138961268199871745376142403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92640845466581163584094935 138961268199871745376142403)
      ·
        refine ⟨208441902299807618064213605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138961268199871745376142403 208441902299807618064213605)
        ·
          refine ⟨39082856681213928387040051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208441902299807618064213605 39082856681213928387040051)
          ·
            refine ⟨58624285021820892580560077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39082856681213928387040051 58624285021820892580560077)
            ·
              refine ⟨21984106883182834717710029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58624285021820892580560077 21984106883182834717710029)
              ·
                refine ⟨8244040081193563019141261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21984106883182834717710029 8244040081193563019141261)
                ·
                  refine ⟨3091515030447586132177973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8244040081193563019141261 3091515030447586132177973)
                  ·
                    refine ⟨289829534104461199891685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3091515030447586132177973 289829534104461199891685)
                    ·
                      rfl

theorem cell23_1693323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 5].length) (baseStart_1693323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693323 prefixEnd_1693323 := by exact prefixLift 1693323
  have htrace : WordTrace (prefixWord ++ tailWord_1693323) baseStart_1693323 baseEnd_1693323 := by
    simpa [prefixWord, tailWord_1693323, baseEnd_1693323] using wordTrace_append hprefix tailTrace_1693323
  have hstable : (prefixWord ++ tailWord_1693323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693323).length < 2 ^ (prefixWord ++ tailWord_1693323).sum := by decide
  have hdescent : baseEnd_1693323 < baseStart_1693323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693370 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_1693370 : Nat := 118140960795 + 1693370 * 2 ^ 59
def prefixEnd_1693370 : Nat := 4983230072969 + 3 ^ 40 * 1693370 * 2
def baseEnd_1693370 : Nat := 289837578634714971929113

theorem tailTrace_1693370 : CollatzResearch.WordTrace tailWord_1693370 prefixEnd_1693370 289837578634714971929113 := by
  unfold tailWord_1693370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15440569468804292354089391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41174851916811446277571709 15440569468804292354089391)
  ·
    refine ⟨23160854203206438531134087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15440569468804292354089391 23160854203206438531134087)
    ·
      refine ⟨34741281304809657796701131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23160854203206438531134087 34741281304809657796701131)
      ·
        refine ⟨52111921957214486695051697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34741281304809657796701131 52111921957214486695051697)
        ·
          refine ⟨39083941467910865021288773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52111921957214486695051697 39083941467910865021288773)
          ·
            refine ⟨7328239025233287191491645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39083941467910865021288773 7328239025233287191491645)
            ·
              refine ⟨2748089634462482696809367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7328239025233287191491645 2748089634462482696809367)
              ·
                refine ⟨4122134451693724045214051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748089634462482696809367 4122134451693724045214051)
                ·
                  refine ⟨6183201677540586067821077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122134451693724045214051 6183201677540586067821077)
                  ·
                    refine ⟨289837578634714971929113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6183201677540586067821077 289837578634714971929113)
                    ·
                      rfl

theorem cell23_1693370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_1693370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693370 prefixEnd_1693370 := by exact prefixLift 1693370
  have htrace : WordTrace (prefixWord ++ tailWord_1693370) baseStart_1693370 baseEnd_1693370 := by
    simpa [prefixWord, tailWord_1693370, baseEnd_1693370] using wordTrace_append hprefix tailTrace_1693370
  have hstable : (prefixWord ++ tailWord_1693370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693370).length < 2 ^ (prefixWord ++ tailWord_1693370).sum := by decide
  have hdescent : baseEnd_1693370 < baseStart_1693370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693380 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1693380 : Nat := 118140960795 + 1693380 * 2 ^ 59
def prefixEnd_1693380 : Nat := 4983230072969 + 3 ^ 40 * 1693380 * 2
def baseEnd_1693380 : Nat := 869517870710689876662293

theorem tailTrace_1693380 : CollatzResearch.WordTrace tailWord_1693380 prefixEnd_1693380 869517870710689876662293 := by
  unfold tailWord_1693380
  simp only [CollatzResearch.WordTrace]
  refine ⟨30881321302590470562110797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41175095070120627416147729 30881321302590470562110797)
  ·
    refine ⟨11580495488471426460791549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30881321302590470562110797 11580495488471426460791549)
    ·
      refine ⟨4342685808176784922796831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11580495488471426460791549 4342685808176784922796831)
      ·
        refine ⟨6514028712265177384195247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4342685808176784922796831 6514028712265177384195247)
        ·
          refine ⟨9771043068397766076292871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6514028712265177384195247 9771043068397766076292871)
          ·
            refine ⟨14656564602596649114439307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9771043068397766076292871 14656564602596649114439307)
            ·
              refine ⟨21984846903894973671658961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14656564602596649114439307 21984846903894973671658961)
              ·
                refine ⟨16488635177921230253744221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21984846903894973671658961 16488635177921230253744221)
                ·
                  refine ⟨6183238191720461345154083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16488635177921230253744221 6183238191720461345154083)
                  ·
                    refine ⟨9274857287580692017731125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6183238191720461345154083 9274857287580692017731125)
                    ·
                      refine ⟨869517870710689876662293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9274857287580692017731125 869517870710689876662293)
                      ·
                        rfl

theorem cell23_1693380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1693380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693380 prefixEnd_1693380 := by exact prefixLift 1693380
  have htrace : WordTrace (prefixWord ++ tailWord_1693380) baseStart_1693380 baseEnd_1693380 := by
    simpa [prefixWord, tailWord_1693380, baseEnd_1693380] using wordTrace_append hprefix tailTrace_1693380
  have hstable : (prefixWord ++ tailWord_1693380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693380).length < 2 ^ (prefixWord ++ tailWord_1693380).sum := by decide
  have hdescent : baseEnd_1693380 < baseStart_1693380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693383 : List Nat := [1, 1, 4, 1, 1, 1, 5, 9]
def baseStart_1693383 : Nat := 118140960795 + 1693383 * 2 ^ 59
def prefixEnd_1693383 : Nat := 4983230072969 + 3 ^ 40 * 1693383 * 2
def baseEnd_1693383 : Nat := 32204422635283457960177

theorem tailTrace_1693383 : CollatzResearch.WordTrace tailWord_1693383 prefixEnd_1693383 32204422635283457960177 := by
  unfold tailWord_1693383
  simp only [CollatzResearch.WordTrace]
  refine ⟨61762752024170072636580803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41175168016113381757720535 61762752024170072636580803)
  ·
    refine ⟨92644128036255108954871205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61762752024170072636580803 92644128036255108954871205)
    ·
      refine ⟨17370774006797832929038351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92644128036255108954871205 17370774006797832929038351)
      ·
        refine ⟨26056161010196749393557527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17370774006797832929038351 26056161010196749393557527)
        ·
          refine ⟨39084241515295124090336291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26056161010196749393557527 39084241515295124090336291)
          ·
            refine ⟨58626362272942686135504437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39084241515295124090336291 58626362272942686135504437)
            ·
              refine ⟨5496221463088376825203541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58626362272942686135504437 5496221463088376825203541)
              ·
                refine ⟨32204422635283457960177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5496221463088376825203541 32204422635283457960177)
                ·
                  rfl

theorem cell23_1693383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 9].length) (baseStart_1693383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693383 prefixEnd_1693383 := by exact prefixLift 1693383
  have htrace : WordTrace (prefixWord ++ tailWord_1693383) baseStart_1693383 baseEnd_1693383 := by
    simpa [prefixWord, tailWord_1693383, baseEnd_1693383] using wordTrace_append hprefix tailTrace_1693383
  have hstable : (prefixWord ++ tailWord_1693383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693383).length < 2 ^ (prefixWord ++ tailWord_1693383).sum := by decide
  have hdescent : baseEnd_1693383 < baseStart_1693383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693388 : List Nat := [2, 2, 1, 5, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1693388 : Nat := 118140960795 + 1693388 * 2 ^ 59
def prefixEnd_1693388 : Nat := 4983230072969 + 3 ^ 40 * 1693388 * 2
def baseEnd_1693388 : Nat := 869521978555925845362257

theorem tailTrace_1693388 : CollatzResearch.WordTrace tailWord_1693388 prefixEnd_1693388 869521978555925845362257 := by
  unfold tailWord_1693388
  simp only [CollatzResearch.WordTrace]
  refine ⟨30881467194575979245256409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41175289592767972327008545 30881467194575979245256409)
  ·
    refine ⟨23161100395931984433942307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30881467194575979245256409 23161100395931984433942307)
    ·
      refine ⟨34741650593897976650913461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23161100395931984433942307 34741650593897976650913461)
      ·
        refine ⟨3257029743177935311023137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34741650593897976650913461 3257029743177935311023137)
        ·
          refine ⟨2442772307383451483267353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3257029743177935311023137 2442772307383451483267353)
          ·
            refine ⟨1832079230537588612450515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2442772307383451483267353 1832079230537588612450515)
            ·
              refine ⟨2748118845806382918675773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832079230537588612450515 2748118845806382918675773)
              ·
                refine ⟨1030544567177393594503415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2748118845806382918675773 1030544567177393594503415)
                ·
                  refine ⟨1545816850766090391755123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030544567177393594503415 1545816850766090391755123)
                  ·
                    refine ⟨2318725276149135587632685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1545816850766090391755123 2318725276149135587632685)
                    ·
                      refine ⟨869521978555925845362257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2318725276149135587632685 869521978555925845362257)
                      ·
                        rfl

theorem cell23_1693388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1693388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693388 prefixEnd_1693388 := by exact prefixLift 1693388
  have htrace : WordTrace (prefixWord ++ tailWord_1693388) baseStart_1693388 baseEnd_1693388 := by
    simpa [prefixWord, tailWord_1693388, baseEnd_1693388] using wordTrace_append hprefix tailTrace_1693388
  have hstable : (prefixWord ++ tailWord_1693388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693388).length < 2 ^ (prefixWord ++ tailWord_1693388).sum := by decide
  have hdescent : baseEnd_1693388 < baseStart_1693388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693390 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1693390 : Nat := 118140960795 + 1693390 * 2 ^ 59
def prefixEnd_1693390 : Nat := 4983230072969 + 3 ^ 40 * 1693390 * 2
def baseEnd_1693390 : Nat := 869523005517234837537247

theorem tailTrace_1693390 : CollatzResearch.WordTrace tailWord_1693390 prefixEnd_1693390 869523005517234837537247 := by
  unfold tailWord_1693390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7720375916893089104010703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41175338223429808554723749 7720375916893089104010703)
  ·
    refine ⟨11580563875339633656016055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7720375916893089104010703 11580563875339633656016055)
    ·
      refine ⟨17370845813009450484024083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11580563875339633656016055 17370845813009450484024083)
      ·
        refine ⟨26056268719514175726036125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17370845813009450484024083 26056268719514175726036125)
        ·
          refine ⟨9771100769817815897263547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26056268719514175726036125 9771100769817815897263547)
          ·
            refine ⟨14656651154726723845895321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9771100769817815897263547 14656651154726723845895321)
            ·
              refine ⟨10992488366045042884421491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14656651154726723845895321 10992488366045042884421491)
              ·
                refine ⟨16488732549067564326632237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10992488366045042884421491 16488732549067564326632237)
                ·
                  refine ⟨6183274705900336622487089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16488732549067564326632237 6183274705900336622487089)
                  ·
                    refine ⟨4637456029425252466865317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6183274705900336622487089 4637456029425252466865317)
                    ·
                      refine ⟨869523005517234837537247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4637456029425252466865317 869523005517234837537247)
                      ·
                        rfl

theorem cell23_1693390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1693390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693390 prefixEnd_1693390 := by exact prefixLift 1693390
  have htrace : WordTrace (prefixWord ++ tailWord_1693390) baseStart_1693390 baseEnd_1693390 := by
    simpa [prefixWord, tailWord_1693390, baseEnd_1693390] using wordTrace_append hprefix tailTrace_1693390
  have hstable : (prefixWord ++ tailWord_1693390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693390).length < 2 ^ (prefixWord ++ tailWord_1693390).sum := by decide
  have hdescent : baseEnd_1693390 < baseStart_1693390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693398 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1693398 : Nat := 118140960795 + 1693398 * 2 ^ 59
def prefixEnd_1693398 : Nat := 4983230072969 + 3 ^ 40 * 1693398 * 2
def baseEnd_1693398 : Nat := 869527113362470806237211

theorem tailTrace_1693398 : CollatzResearch.WordTrace tailWord_1693398 prefixEnd_1693398 869527113362470806237211 := by
  unfold tailWord_1693398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860206194944733137398553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41175532746077153465584565 3860206194944733137398553)
  ·
    refine ⟨2895154646208549853048915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3860206194944733137398553 2895154646208549853048915)
    ·
      refine ⟨4342731969312824779573373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2895154646208549853048915 4342731969312824779573373)
      ·
        refine ⟨1628524488492309292340015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4342731969312824779573373 1628524488492309292340015)
        ·
          refine ⟨2442786732738463938510023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628524488492309292340015 2442786732738463938510023)
          ·
            refine ⟨3664180099107695907765035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442786732738463938510023 3664180099107695907765035)
            ·
              refine ⟨5496270148661543861647553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664180099107695907765035 5496270148661543861647553)
              ·
                refine ⟨4122202611496157896235665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5496270148661543861647553 4122202611496157896235665)
                ·
                  refine ⟨3091651958622118422176749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4122202611496157896235665 3091651958622118422176749)
                  ·
                    refine ⟨1159369484483294408316281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3091651958622118422176749 1159369484483294408316281)
                    ·
                      refine ⟨869527113362470806237211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159369484483294408316281 869527113362470806237211)
                      ·
                        rfl

theorem cell23_1693398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1693398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693398 prefixEnd_1693398 := by exact prefixLift 1693398
  have htrace : WordTrace (prefixWord ++ tailWord_1693398) baseStart_1693398 baseEnd_1693398 := by
    simpa [prefixWord, tailWord_1693398, baseEnd_1693398] using wordTrace_append hprefix tailTrace_1693398
  have hstable : (prefixWord ++ tailWord_1693398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693398).length < 2 ^ (prefixWord ++ tailWord_1693398).sum := by decide
  have hdescent : baseEnd_1693398 < baseStart_1693398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693405 : List Nat := [1, 4, 3, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1693405 : Nat := 118140960795 + 1693405 * 2 ^ 59
def prefixEnd_1693405 : Nat := 4983230072969 + 3 ^ 40 * 1693405 * 2
def baseEnd_1693405 : Nat := 869530707727052278849679

theorem tailTrace_1693405 : CollatzResearch.WordTrace tailWord_1693405 prefixEnd_1693405 869530707727052278849679 := by
  unfold tailWord_1693405
  simp only [CollatzResearch.WordTrace]
  refine ⟨61763554430090370393881669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41175702953393580262587779 61763554430090370393881669)
  ·
    refine ⟨11580666455641944448852813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61763554430090370393881669 11580666455641944448852813)
    ·
      refine ⟨4342749920865729168319805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11580666455641944448852813 4342749920865729168319805)
      ·
        refine ⟨1628531220324648438119927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4342749920865729168319805 1628531220324648438119927)
        ·
          refine ⟨2442796830486972657179891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628531220324648438119927 2442796830486972657179891)
          ·
            refine ⟨3664195245730458985769837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442796830486972657179891 3664195245730458985769837)
            ·
              refine ⟨1374073217148922119663689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3664195245730458985769837 1374073217148922119663689)
              ·
                refine ⟨1030554912861691589747767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374073217148922119663689 1030554912861691589747767)
                ·
                  refine ⟨1545832369292537384621651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030554912861691589747767 1545832369292537384621651)
                  ·
                    refine ⟨2318748553938806076932477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1545832369292537384621651 2318748553938806076932477)
                    ·
                      refine ⟨869530707727052278849679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2318748553938806076932477 869530707727052278849679)
                      ·
                        rfl

theorem cell23_1693405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1693405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693405 prefixEnd_1693405 := by exact prefixLift 1693405
  have htrace : WordTrace (prefixWord ++ tailWord_1693405) baseStart_1693405 baseEnd_1693405 := by
    simpa [prefixWord, tailWord_1693405, baseEnd_1693405] using wordTrace_append hprefix tailTrace_1693405
  have hstable : (prefixWord ++ tailWord_1693405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693405).length < 2 ^ (prefixWord ++ tailWord_1693405).sum := by decide
  have hdescent : baseEnd_1693405 < baseStart_1693405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693421 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_1693421 : Nat := 118140960795 + 1693421 * 2 ^ 59
def prefixEnd_1693421 : Nat := 4983230072969 + 3 ^ 40 * 1693421 * 2
def baseEnd_1693421 : Nat := 289846307805841405416535

theorem tailTrace_1693421 : CollatzResearch.WordTrace tailWord_1693421 prefixEnd_1693421 289846307805841405416535 := by
  unfold tailWord_1693421
  simp only [CollatzResearch.WordTrace]
  refine ⟨61764137998032405126464117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41176091998688270084309411 61764137998032405126464117)
  ·
    refine ⟨5790387937315537980606011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61764137998032405126464117 5790387937315537980606011)
    ·
      refine ⟨8685581905973306970909017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5790387937315537980606011 8685581905973306970909017)
      ·
        refine ⟨6514186429479980228181763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8685581905973306970909017 6514186429479980228181763)
        ·
          refine ⟨9771279644219970342272645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6514186429479980228181763 9771279644219970342272645)
          ·
            refine ⟨1832114933291244439176121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9771279644219970342272645 1832114933291244439176121)
            ·
              refine ⟨1374086199968433329382091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832114933291244439176121 1374086199968433329382091)
              ·
                refine ⟨2061129299952649994073137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374086199968433329382091 2061129299952649994073137)
                ·
                  refine ⟨1545846974964487495554853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2061129299952649994073137 1545846974964487495554853)
                  ·
                    refine ⟨289846307805841405416535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1545846974964487495554853 289846307805841405416535)
                    ·
                      rfl

theorem cell23_1693421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_1693421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693421 prefixEnd_1693421 := by exact prefixLift 1693421
  have htrace : WordTrace (prefixWord ++ tailWord_1693421) baseStart_1693421 baseEnd_1693421 := by
    simpa [prefixWord, tailWord_1693421, baseEnd_1693421] using wordTrace_append hprefix tailTrace_1693421
  have hstable : (prefixWord ++ tailWord_1693421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693421).length < 2 ^ (prefixWord ++ tailWord_1693421).sum := by decide
  have hdescent : baseEnd_1693421 < baseStart_1693421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693428 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1693428 : Nat := 118140960795 + 1693428 * 2 ^ 59
def prefixEnd_1693428 : Nat := 4983230072969 + 3 ^ 40 * 1693428 * 2
def baseEnd_1693428 : Nat := 869542517782105688862073

theorem tailTrace_1693428 : CollatzResearch.WordTrace tailWord_1693428 prefixEnd_1693428 869542517782105688862073 := by
  unfold tailWord_1693428
  simp only [CollatzResearch.WordTrace]
  refine ⟨30882196654503522660984469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41176262206004696881312625 30882196654503522660984469)
  ·
    refine ⟨1447602968179852624733647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30882196654503522660984469 1447602968179852624733647)
    ·
      refine ⟨2171404452269778937100471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1447602968179852624733647 2171404452269778937100471)
      ·
        refine ⟨3257106678404668405650707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2171404452269778937100471 3257106678404668405650707)
        ·
          refine ⟨4885660017607002608476061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3257106678404668405650707 4885660017607002608476061)
          ·
            refine ⟨1832122506602625978178523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4885660017607002608476061 1832122506602625978178523)
            ·
              refine ⟨2748183759903938967267785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832122506602625978178523 2748183759903938967267785)
              ·
                refine ⟨2061137819927954225450839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2748183759903938967267785 2061137819927954225450839)
                ·
                  refine ⟨3091706729891931338176259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061137819927954225450839 3091706729891931338176259)
                  ·
                    refine ⟨4637560094837897007264389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3091706729891931338176259 4637560094837897007264389)
                    ·
                      refine ⟨869542517782105688862073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4637560094837897007264389 869542517782105688862073)
                      ·
                        rfl

theorem cell23_1693428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1693428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693428 prefixEnd_1693428 := by exact prefixLift 1693428
  have htrace : WordTrace (prefixWord ++ tailWord_1693428) baseStart_1693428 baseEnd_1693428 := by
    simpa [prefixWord, tailWord_1693428, baseEnd_1693428] using wordTrace_append hprefix tailTrace_1693428
  have hstable : (prefixWord ++ tailWord_1693428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693428).length < 2 ^ (prefixWord ++ tailWord_1693428).sum := by decide
  have hdescent : baseEnd_1693428 < baseStart_1693428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693433 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1693433 : Nat := 118140960795 + 1693433 * 2 ^ 59
def prefixEnd_1693433 : Nat := 4983230072969 + 3 ^ 40 * 1693433 * 2
def baseEnd_1693433 : Nat := 869545085185378169299549

theorem tailTrace_1693433 : CollatzResearch.WordTrace tailWord_1693433 prefixEnd_1693433 869545085185378169299549 := by
  unfold tailWord_1693433
  simp only [CollatzResearch.WordTrace]
  refine ⟨61764575673988931175900953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41176383782659287450600635 61764575673988931175900953)
  ·
    refine ⟨46323431755491698381925715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61764575673988931175900953 46323431755491698381925715)
    ·
      refine ⟨69485147633237547572888573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46323431755491698381925715 69485147633237547572888573)
      ·
        refine ⟨26056930362464080339833215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69485147633237547572888573 26056930362464080339833215)
        ·
          refine ⟨39085395543696120509749823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26056930362464080339833215 39085395543696120509749823)
          ·
            refine ⟨58628093315544180764624735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39085395543696120509749823 58628093315544180764624735)
            ·
              refine ⟨87942139973316271146937103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58628093315544180764624735 87942139973316271146937103)
              ·
                refine ⟨131913209959974406720405655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87942139973316271146937103 131913209959974406720405655)
                ·
                  refine ⟨197869814939961610080608483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131913209959974406720405655 197869814939961610080608483)
                  ·
                    refine ⟨296804722409942415120912725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 197869814939961610080608483 296804722409942415120912725)
                    ·
                      refine ⟨869545085185378169299549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 296804722409942415120912725 869545085185378169299549)
                      ·
                        rfl

theorem cell23_1693433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1693433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693433 prefixEnd_1693433 := by exact prefixLift 1693433
  have htrace : WordTrace (prefixWord ++ tailWord_1693433) baseStart_1693433 baseEnd_1693433 := by
    simpa [prefixWord, tailWord_1693433, baseEnd_1693433] using wordTrace_append hprefix tailTrace_1693433
  have hstable : (prefixWord ++ tailWord_1693433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693433).length < 2 ^ (prefixWord ++ tailWord_1693433).sum := by decide
  have hdescent : baseEnd_1693433 < baseStart_1693433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693454 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_1693454 : Nat := 118140960795 + 1693454 * 2 ^ 59
def prefixEnd_1693454 : Nat := 4983230072969 + 3 ^ 40 * 1693454 * 2
def baseEnd_1693454 : Nat := 869555868279122587136953

theorem tailTrace_1693454 : CollatzResearch.WordTrace tailWord_1693454 prefixEnd_1693454 869555868279122587136953 := by
  unfold tailWord_1693454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7720667700864106470301927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41176894404608567841610277 7720667700864106470301927)
  ·
    refine ⟨11581001551296159705452891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7720667700864106470301927 11581001551296159705452891)
    ·
      refine ⟨17371502326944239558179337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11581001551296159705452891 17371502326944239558179337)
      ·
        refine ⟨13028626745208179668634503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17371502326944239558179337 13028626745208179668634503)
        ·
          refine ⟨19542940117812269502951755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13028626745208179668634503 19542940117812269502951755)
          ·
            refine ⟨29314410176718404254427633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19542940117812269502951755 29314410176718404254427633)
            ·
              refine ⟨21985807632538803190820725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29314410176718404254427633 21985807632538803190820725)
              ·
                refine ⟨2061169465550512799139443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21985807632538803190820725 2061169465550512799139443)
                ·
                  refine ⟨3091754198325769198709165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061169465550512799139443 3091754198325769198709165)
                  ·
                    refine ⟨1159407824372163449515937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3091754198325769198709165 1159407824372163449515937)
                    ·
                      refine ⟨869555868279122587136953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159407824372163449515937 869555868279122587136953)
                      ·
                        rfl

theorem cell23_1693454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_1693454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693454 prefixEnd_1693454 := by exact prefixLift 1693454
  have htrace : WordTrace (prefixWord ++ tailWord_1693454) baseStart_1693454 baseEnd_1693454 := by
    simpa [prefixWord, tailWord_1693454, baseEnd_1693454] using wordTrace_append hprefix tailTrace_1693454
  have hstable : (prefixWord ++ tailWord_1693454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693454).length < 2 ^ (prefixWord ++ tailWord_1693454).sum := by decide
  have hdescent : baseEnd_1693454 < baseStart_1693454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693484 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 1, 4, 2]
def baseStart_1693484 : Nat := 118140960795 + 1693484 * 2 ^ 59
def prefixEnd_1693484 : Nat := 4983230072969 + 3 ^ 40 * 1693484 * 2
def baseEnd_1693484 : Nat := 869571272698757469761815

theorem tailTrace_1693484 : CollatzResearch.WordTrace tailWord_1693484 prefixEnd_1693484 869571272698757469761815 := by
  unfold tailWord_1693484
  simp only [CollatzResearch.WordTrace]
  refine ⟨30883217898402083443003753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41177623864536111257338337 30883217898402083443003753)
  ·
    refine ⟨23162413423801562582252815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30883217898402083443003753 23162413423801562582252815)
    ·
      refine ⟨34743620135702343873379223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23162413423801562582252815 34743620135702343873379223)
      ·
        refine ⟨52115430203553515810068835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34743620135702343873379223 52115430203553515810068835)
        ·
          refine ⟨78173145305330273715103253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52115430203553515810068835 78173145305330273715103253)
          ·
            refine ⟨3664366186187356580395465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78173145305330273715103253 3664366186187356580395465)
            ·
              refine ⟨2748274639640517435296599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3664366186187356580395465 2748274639640517435296599)
              ·
                refine ⟨4122411959460776152944899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748274639640517435296599 4122411959460776152944899)
                ·
                  refine ⟨6183617939191164229417349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122411959460776152944899 6183617939191164229417349)
                  ·
                    refine ⟨1159428363598343293015753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6183617939191164229417349 1159428363598343293015753)
                    ·
                      refine ⟨869571272698757469761815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159428363598343293015753 869571272698757469761815)
                      ·
                        rfl

theorem cell23_1693484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_1693484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693484 prefixEnd_1693484 := by exact prefixLift 1693484
  have htrace : WordTrace (prefixWord ++ tailWord_1693484) baseStart_1693484 baseEnd_1693484 := by
    simpa [prefixWord, tailWord_1693484, baseEnd_1693484] using wordTrace_append hprefix tailTrace_1693484
  have hstable : (prefixWord ++ tailWord_1693484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693484).length < 2 ^ (prefixWord ++ tailWord_1693484).sum := by decide
  have hdescent : baseEnd_1693484 < baseStart_1693484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693490 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 9]
def baseStart_1693490 : Nat := 118140960795 + 1693490 * 2 ^ 59
def prefixEnd_1693490 : Nat := 4983230072969 + 3 ^ 40 * 1693490 * 2
def baseEnd_1693490 : Nat := 96619372620298271809643

theorem tailTrace_1693490 : CollatzResearch.WordTrace tailWord_1693490 prefixEnd_1693490 96619372620298271809643 := by
  unfold tailWord_1693490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15441663658695607477681481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41177769756521619940483949 15441663658695607477681481)
  ·
    refine ⟨11581247744021705608261111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15441663658695607477681481 11581247744021705608261111)
    ·
      refine ⟨17371871616032558412391667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11581247744021705608261111 17371871616032558412391667)
      ·
        refine ⟨26057807424048837618587501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17371871616032558412391667 26057807424048837618587501)
        ·
          refine ⟨9771677784018314106970313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26057807424048837618587501 9771677784018314106970313)
          ·
            refine ⟨7328758338013735580227735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9771677784018314106970313 7328758338013735580227735)
            ·
              refine ⟨10993137507020603370341603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7328758338013735580227735 10993137507020603370341603)
              ·
                refine ⟨16489706260530905055512405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10993137507020603370341603 16489706260530905055512405)
                ·
                  refine ⟨96619372620298271809643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16489706260530905055512405 96619372620298271809643)
                  ·
                    rfl

theorem cell23_1693490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_1693490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693490 prefixEnd_1693490 := by exact prefixLift 1693490
  have htrace : WordTrace (prefixWord ++ tailWord_1693490) baseStart_1693490 baseEnd_1693490 := by
    simpa [prefixWord, tailWord_1693490, baseEnd_1693490] using wordTrace_append hprefix tailTrace_1693490
  have hstable : (prefixWord ++ tailWord_1693490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693490).length < 2 ^ (prefixWord ++ tailWord_1693490).sum := by decide
  have hdescent : baseEnd_1693490 < baseStart_1693490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693507 : List Nat := [1, 1, 1, 3, 1, 5, 1, 5, 5]
def baseStart_1693507 : Nat := 118140960795 + 1693507 * 2 ^ 59
def prefixEnd_1693507 : Nat := 4983230072969 + 3 ^ 40 * 1693507 * 2
def baseEnd_1693507 : Nat := 96620342528201208863801

theorem tailTrace_1693507 : CollatzResearch.WordTrace tailWord_1693507 prefixEnd_1693507 96620342528201208863801 := by
  unfold tailWord_1693507
  simp only [CollatzResearch.WordTrace]
  refine ⟨61767274675720841814094775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41178183117147227876063183 61767274675720841814094775)
  ·
    refine ⟨92650912013581262721142163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61767274675720841814094775 92650912013581262721142163)
    ·
      refine ⟨138976368020371894081713245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92650912013581262721142163 138976368020371894081713245)
      ·
        refine ⟨52116138007639460280642467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138976368020371894081713245 52116138007639460280642467)
        ·
          refine ⟨78174207011459190420963701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52116138007639460280642467 78174207011459190420963701)
          ·
            refine ⟨7328831907324299101965347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78174207011459190420963701 7328831907324299101965347)
            ·
              refine ⟨10993247860986448652948021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7328831907324299101965347 10993247860986448652948021)
              ·
                refine ⟨1030616986967479561213877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10993247860986448652948021 1030616986967479561213877)
                ·
                  refine ⟨96620342528201208863801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1030616986967479561213877 96620342528201208863801)
                  ·
                    rfl

theorem cell23_1693507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 5].length) (baseStart_1693507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693507 prefixEnd_1693507 := by exact prefixLift 1693507
  have htrace : WordTrace (prefixWord ++ tailWord_1693507) baseStart_1693507 baseEnd_1693507 := by
    simpa [prefixWord, tailWord_1693507, baseEnd_1693507] using wordTrace_append hprefix tailTrace_1693507
  have hstable : (prefixWord ++ tailWord_1693507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693507).length < 2 ^ (prefixWord ++ tailWord_1693507).sum := by decide
  have hdescent : baseEnd_1693507 < baseStart_1693507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693520 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 4, 5]
def baseStart_1693520 : Nat := 118140960795 + 1693520 * 2 ^ 59
def prefixEnd_1693520 : Nat := 4983230072969 + 3 ^ 40 * 1693520 * 2
def baseEnd_1693520 : Nat := 289863252667439776303883

theorem tailTrace_1693520 : CollatzResearch.WordTrace tailWord_1693520 prefixEnd_1693520 289863252667439776303883 := by
  unfold tailWord_1693520
  simp only [CollatzResearch.WordTrace]
  refine ⟨30883874412336872517159007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41178499216449163356212009 30883874412336872517159007)
  ·
    refine ⟨46325811618505308775738511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30883874412336872517159007 46325811618505308775738511)
    ·
      refine ⟨69488717427757963163607767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46325811618505308775738511 69488717427757963163607767)
      ·
        refine ⟨104233076141636944745411651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69488717427757963163607767 104233076141636944745411651)
        ·
          refine ⟨156349614212455417118117477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104233076141636944745411651 156349614212455417118117477)
          ·
            refine ⟨29315552664835390709647027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156349614212455417118117477 29315552664835390709647027)
            ·
              refine ⟨43973328997253086064470541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29315552664835390709647027 43973328997253086064470541)
              ·
                refine ⟨16489998373969907274176453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43973328997253086064470541 16489998373969907274176453)
                ·
                  refine ⟨3091874695119357613908085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16489998373969907274176453 3091874695119357613908085)
                  ·
                    refine ⟨289863252667439776303883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3091874695119357613908085 289863252667439776303883)
                    ·
                      rfl

theorem cell23_1693520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_1693520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693520 prefixEnd_1693520 := by exact prefixLift 1693520
  have htrace : WordTrace (prefixWord ++ tailWord_1693520) baseStart_1693520 baseEnd_1693520 := by
    simpa [prefixWord, tailWord_1693520, baseEnd_1693520] using wordTrace_append hprefix tailTrace_1693520
  have hstable : (prefixWord ++ tailWord_1693520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693520).length < 2 ^ (prefixWord ++ tailWord_1693520).sum := by decide
  have hdescent : baseEnd_1693520 < baseStart_1693520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693524 : List Nat := [2, 4, 1, 1, 3, 1, 2, 4, 5]
def baseStart_1693524 : Nat := 118140960795 + 1693524 * 2 ^ 59
def prefixEnd_1693524 : Nat := 4983230072969 + 3 ^ 40 * 1693524 * 2
def baseEnd_1693524 : Nat := 96621312436104145917959

theorem tailTrace_1693524 : CollatzResearch.WordTrace tailWord_1693524 prefixEnd_1693524 96621312436104145917959 := by
  unfold tailWord_1693524
  simp only [CollatzResearch.WordTrace]
  refine ⟨30883947358329626858731813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41178596477772835811642417 30883947358329626858731813)
  ·
    refine ⟨5790740129686805036012215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30883947358329626858731813 5790740129686805036012215)
    ·
      refine ⟨8686110194530207554018323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5790740129686805036012215 8686110194530207554018323)
      ·
        refine ⟨13029165291795311331027485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8686110194530207554018323 13029165291795311331027485)
        ·
          refine ⟨4885936984423241749135307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13029165291795311331027485 4885936984423241749135307)
          ·
            refine ⟨7328905476634862623702961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885936984423241749135307 7328905476634862623702961)
            ·
              refine ⟨5496679107476146967777221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7328905476634862623702961 5496679107476146967777221)
              ·
                refine ⟨1030627332651777556458229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5496679107476146967777221 1030627332651777556458229)
                ·
                  refine ⟨96621312436104145917959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1030627332651777556458229 96621312436104145917959)
                  ·
                    rfl

theorem cell23_1693524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_1693524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693524 prefixEnd_1693524 := by exact prefixLift 1693524
  have htrace : WordTrace (prefixWord ++ tailWord_1693524) baseStart_1693524 baseEnd_1693524 := by
    simpa [prefixWord, tailWord_1693524, baseEnd_1693524] using wordTrace_append hprefix tailTrace_1693524
  have hstable : (prefixWord ++ tailWord_1693524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693524).length < 2 ^ (prefixWord ++ tailWord_1693524).sum := by decide
  have hdescent : baseEnd_1693524 < baseStart_1693524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693530 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1693530 : Nat := 118140960795 + 1693530 * 2 ^ 59
def prefixEnd_1693530 : Nat := 4983230072969 + 3 ^ 40 * 1693530 * 2
def baseEnd_1693530 : Nat := 869594892808864289786603

theorem tailTrace_1693530 : CollatzResearch.WordTrace tailWord_1693530 prefixEnd_1693530 869594892808864289786603 := by
  unfold tailWord_1693530
  simp only [CollatzResearch.WordTrace]
  refine ⟨15442028388659379185545511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41178742369758344494788029 15442028388659379185545511)
  ·
    refine ⟨23163042582989068778318267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15442028388659379185545511 23163042582989068778318267)
    ·
      refine ⟨34744563874483603167477401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23163042582989068778318267 34744563874483603167477401)
      ·
        refine ⟨26058422905862702375608051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34744563874483603167477401 26058422905862702375608051)
        ·
          refine ⟨39087634358794053563412077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26058422905862702375608051 39087634358794053563412077)
          ·
            refine ⟨14657862884547770086279529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39087634358794053563412077 14657862884547770086279529)
            ·
              refine ⟨10993397163410827564709647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14657862884547770086279529 10993397163410827564709647)
              ·
                refine ⟨16490095745116241347064471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10993397163410827564709647 16490095745116241347064471)
                ·
                  refine ⟨24735143617674362020596707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16490095745116241347064471 24735143617674362020596707)
                  ·
                    refine ⟨37102715426511543030895061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24735143617674362020596707 37102715426511543030895061)
                    ·
                      refine ⟨869594892808864289786603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37102715426511543030895061 869594892808864289786603)
                      ·
                        rfl

theorem cell23_1693530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1693530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693530 prefixEnd_1693530 := by exact prefixLift 1693530
  have htrace : WordTrace (prefixWord ++ tailWord_1693530) baseStart_1693530 baseEnd_1693530 := by
    simpa [prefixWord, tailWord_1693530, baseEnd_1693530] using wordTrace_append hprefix tailTrace_1693530
  have hstable : (prefixWord ++ tailWord_1693530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693530).length < 2 ^ (prefixWord ++ tailWord_1693530).sum := by decide
  have hdescent : baseEnd_1693530 < baseStart_1693530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693557 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1693557 : Nat := 118140960795 + 1693557 * 2 ^ 59
def prefixEnd_1693557 : Nat := 4983230072969 + 3 ^ 40 * 1693557 * 2
def baseEnd_1693557 : Nat := 869608756786535684148979

theorem tailTrace_1693557 : CollatzResearch.WordTrace tailWord_1693557 prefixEnd_1693557 869608756786535684148979 := by
  unfold tailWord_1693557
  simp only [CollatzResearch.WordTrace]
  refine ⟨61769098325539700353414925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41179398883693133568943283 61769098325539700353414925)
  ·
    refine ⟨23163411872077387632530597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61769098325539700353414925 23163411872077387632530597)
    ·
      refine ⟨4343139726014510181099487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23163411872077387632530597 4343139726014510181099487)
      ·
        refine ⟨6514709589021765271649231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343139726014510181099487 6514709589021765271649231)
        ·
          refine ⟨9772064383532647907473847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6514709589021765271649231 9772064383532647907473847)
          ·
            refine ⟨14658096575298971861210771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9772064383532647907473847 14658096575298971861210771)
            ·
              refine ⟨21987144862948457791816157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14658096575298971861210771 21987144862948457791816157)
              ·
                refine ⟨8245179323605671671931059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21987144862948457791816157 8245179323605671671931059)
                ·
                  refine ⟨12367768985408507507896589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8245179323605671671931059 12367768985408507507896589)
                  ·
                    refine ⟨4637913369528190315461221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12367768985408507507896589 4637913369528190315461221)
                    ·
                      refine ⟨869608756786535684148979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4637913369528190315461221 869608756786535684148979)
                      ·
                        rfl

theorem cell23_1693557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1693557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693557 prefixEnd_1693557 := by exact prefixLift 1693557
  have htrace : WordTrace (prefixWord ++ tailWord_1693557) baseStart_1693557 baseEnd_1693557 := by
    simpa [prefixWord, tailWord_1693557, baseEnd_1693557] using wordTrace_append hprefix tailTrace_1693557
  have hstable : (prefixWord ++ tailWord_1693557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693557).length < 2 ^ (prefixWord ++ tailWord_1693557).sum := by decide
  have hdescent : baseEnd_1693557 < baseStart_1693557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693558 : List Nat := [5, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_1693558 : Nat := 118140960795 + 1693558 * 2 ^ 59
def prefixEnd_1693558 : Nat := 4983230072969 + 3 ^ 40 * 1693558 * 2
def baseEnd_1693558 : Nat := 96623252251910020026275

theorem tailTrace_1693558 : CollatzResearch.WordTrace tailWord_1693558 prefixEnd_1693558 96623252251910020026275 := by
  unfold tailWord_1693558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860570924908504845262583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41179423199024051682800885 3860570924908504845262583)
  ·
    refine ⟨5790856387362757267893875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3860570924908504845262583 5790856387362757267893875)
    ·
      refine ⟨8686284581044135901840813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5790856387362757267893875 8686284581044135901840813)
      ·
        refine ⟨3257356717891550963190305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8686284581044135901840813 3257356717891550963190305)
        ·
          refine ⟨2443017538418663222392729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3257356717891550963190305 2443017538418663222392729)
          ·
            refine ⟨1832263153813997416794547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2443017538418663222392729 1832263153813997416794547)
            ·
              refine ⟨2748394730720996125191821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832263153813997416794547 2748394730720996125191821)
              ·
                refine ⟨1030648024020373546946933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2748394730720996125191821 1030648024020373546946933)
                ·
                  refine ⟨96623252251910020026275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1030648024020373546946933 96623252251910020026275)
                  ·
                    rfl

theorem cell23_1693558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_1693558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693558 prefixEnd_1693558 := by exact prefixLift 1693558
  have htrace : WordTrace (prefixWord ++ tailWord_1693558) baseStart_1693558 baseEnd_1693558 := by
    simpa [prefixWord, tailWord_1693558, baseEnd_1693558] using wordTrace_append hprefix tailTrace_1693558
  have hstable : (prefixWord ++ tailWord_1693558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693558).length < 2 ^ (prefixWord ++ tailWord_1693558).sum := by decide
  have hdescent : baseEnd_1693558 < baseStart_1693558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693608 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1693608 : Nat := 118140960795 + 1693608 * 2 ^ 59
def prefixEnd_1693608 : Nat := 4983230072969 + 3 ^ 40 * 1693608 * 2
def baseEnd_1693608 : Nat := 869634944299914984611245

theorem tailTrace_1693608 : CollatzResearch.WordTrace tailWord_1693608 prefixEnd_1693608 869634944299914984611245 := by
  unfold tailWord_1693608
  simp only [CollatzResearch.WordTrace]
  refine ⟨30885479224177468031760739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41180638965569957375680985 30885479224177468031760739)
  ·
    refine ⟨46328218836266202047641109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30885479224177468031760739 46328218836266202047641109)
    ·
      refine ⟨2171635257949978220983177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46328218836266202047641109 2171635257949978220983177)
      ·
        refine ⟨1628726443462483665737383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2171635257949978220983177 1628726443462483665737383)
        ·
          refine ⟨2443089665193725498606075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628726443462483665737383 2443089665193725498606075)
          ·
            refine ⟨3664634497790588247909113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443089665193725498606075 3664634497790588247909113)
            ·
              refine ⟨2748475873342941185931835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3664634497790588247909113 2748475873342941185931835)
              ·
                refine ⟨4122713810014411778897753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748475873342941185931835 4122713810014411778897753)
                ·
                  refine ⟨3092035357510808834173315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4122713810014411778897753 3092035357510808834173315)
                  ·
                    refine ⟨4638053036266213251259973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3092035357510808834173315 4638053036266213251259973)
                    ·
                      refine ⟨869634944299914984611245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4638053036266213251259973 869634944299914984611245)
                      ·
                        rfl

theorem cell23_1693608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1693608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693608 prefixEnd_1693608 := by exact prefixLift 1693608
  have htrace : WordTrace (prefixWord ++ tailWord_1693608) baseStart_1693608 baseEnd_1693608 := by
    simpa [prefixWord, tailWord_1693608, baseEnd_1693608] using wordTrace_append hprefix tailTrace_1693608
  have hstable : (prefixWord ++ tailWord_1693608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693608).length < 2 ^ (prefixWord ++ tailWord_1693608).sum := by decide
  have hdescent : baseEnd_1693608 < baseStart_1693608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693641 : List Nat := [1, 2, 1, 1, 2, 1, 2, 8, 1, 1, 3]
def baseStart_1693641 : Nat := 118140960795 + 1693641 * 2 ^ 59
def prefixEnd_1693641 : Nat := 4983230072969 + 3 ^ 40 * 1693641 * 2
def baseEnd_1693641 : Nat := 869651889161513355498593

theorem tailTrace_1693641 : CollatzResearch.WordTrace tailWord_1693641 prefixEnd_1693641 869651889161513355498593 := by
  unfold tailWord_1693641
  simp only [CollatzResearch.WordTrace]
  refine ⟨61772162057235382699472777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41181441371490255132981851 61772162057235382699472777)
  ·
    refine ⟨46329121542926537024604583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61772162057235382699472777 46329121542926537024604583)
    ·
      refine ⟨69493682314389805536906875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46329121542926537024604583 69493682314389805536906875)
      ·
        refine ⟨104240523471584708305360313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69493682314389805536906875 104240523471584708305360313)
        ·
          refine ⟨78180392603688531229020235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104240523471584708305360313 78180392603688531229020235)
          ·
            refine ⟨117270588905532796843530353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78180392603688531229020235 117270588905532796843530353)
            ·
              refine ⟨87952941679149597632647765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117270588905532796843530353 87952941679149597632647765)
              ·
                refine ⟨1030698535302534347257591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 87952941679149597632647765 1030698535302534347257591)
                ·
                  refine ⟨1546047802953801520886387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030698535302534347257591 1546047802953801520886387)
                  ·
                    refine ⟨2319071704430702281329581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1546047802953801520886387 2319071704430702281329581)
                    ·
                      refine ⟨869651889161513355498593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2319071704430702281329581 869651889161513355498593)
                      ·
                        rfl

theorem cell23_1693641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 1, 3].length) (baseStart_1693641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693641 prefixEnd_1693641 := by exact prefixLift 1693641
  have htrace : WordTrace (prefixWord ++ tailWord_1693641) baseStart_1693641 baseEnd_1693641 := by
    simpa [prefixWord, tailWord_1693641, baseEnd_1693641] using wordTrace_append hprefix tailTrace_1693641
  have hstable : (prefixWord ++ tailWord_1693641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693641).length < 2 ^ (prefixWord ++ tailWord_1693641).sum := by decide
  have hdescent : baseEnd_1693641 < baseStart_1693641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693647 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_1693647 : Nat := 118140960795 + 1693647 * 2 ^ 59
def prefixEnd_1693647 : Nat := 4983230072969 + 3 ^ 40 * 1693647 * 2
def baseEnd_1693647 : Nat := 869654970045440332023565

theorem tailTrace_1693647 : CollatzResearch.WordTrace tailWord_1693647 prefixEnd_1693647 869654970045440332023565 := by
  unfold tailWord_1693647
  simp only [CollatzResearch.WordTrace]
  refine ⟨61772380895213645724191195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41181587263475763816127463 61772380895213645724191195)
  ·
    refine ⟨92658571342820468586286793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61772380895213645724191195 92658571342820468586286793)
    ·
      refine ⟨69493928507115351439715095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92658571342820468586286793 69493928507115351439715095)
      ·
        refine ⟨104240892760673027159572643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69493928507115351439715095 104240892760673027159572643)
        ·
          refine ⟨156361339141009540739358965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104240892760673027159572643 156361339141009540739358965)
          ·
            refine ⟨14658875544469644444314903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156361339141009540739358965 14658875544469644444314903)
            ·
              refine ⟨21988313316704466666472355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14658875544469644444314903 21988313316704466666472355)
              ·
                refine ⟨32982469975056699999708533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21988313316704466666472355 32982469975056699999708533)
                ·
                  refine ⟨3092106560161565624972675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32982469975056699999708533 3092106560161565624972675)
                  ·
                    refine ⟨4638159840242348437459013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3092106560161565624972675 4638159840242348437459013)
                    ·
                      refine ⟨869654970045440332023565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4638159840242348437459013 869654970045440332023565)
                      ·
                        rfl

theorem cell23_1693647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_1693647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693647 prefixEnd_1693647 := by exact prefixLift 1693647
  have htrace : WordTrace (prefixWord ++ tailWord_1693647) baseStart_1693647 baseEnd_1693647 := by
    simpa [prefixWord, tailWord_1693647, baseEnd_1693647] using wordTrace_append hprefix tailTrace_1693647
  have hstable : (prefixWord ++ tailWord_1693647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693647).length < 2 ^ (prefixWord ++ tailWord_1693647).sum := by decide
  have hdescent : baseEnd_1693647 < baseStart_1693647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693674 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1693674 : Nat := 118140960795 + 1693674 * 2 ^ 59
def prefixEnd_1693674 : Nat := 4983230072969 + 3 ^ 40 * 1693674 * 2
def baseEnd_1693674 : Nat := 289889611341037242128647

theorem tailTrace_1693674 : CollatzResearch.WordTrace tailWord_1693674 prefixEnd_1693674 289889611341037242128647 := by
  unfold tailWord_1693674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15443341416528957333856019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41182243777410552890282717 15443341416528957333856019)
  ·
    refine ⟨23165012124793436000784029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15443341416528957333856019 23165012124793436000784029)
    ·
      refine ⟨8686879546797538500294011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23165012124793436000784029 8686879546797538500294011)
      ·
        refine ⟨13030319320196307750441017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8686879546797538500294011 13030319320196307750441017)
        ·
          refine ⟨9772739490147230812830763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13030319320196307750441017 9772739490147230812830763)
          ·
            refine ⟨14659109235220846219246145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9772739490147230812830763 14659109235220846219246145)
            ·
              refine ⟨10994331926415634664434609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14659109235220846219246145 10994331926415634664434609)
              ·
                refine ⟨8245748944811725998325957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10994331926415634664434609 8245748944811725998325957)
                ·
                  refine ⟨1546077927152198624686117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8245748944811725998325957 1546077927152198624686117)
                  ·
                    refine ⟨289889611341037242128647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1546077927152198624686117 289889611341037242128647)
                    ·
                      rfl

theorem cell23_1693674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1693674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693674 prefixEnd_1693674 := by exact prefixLift 1693674
  have htrace : WordTrace (prefixWord ++ tailWord_1693674) baseStart_1693674 baseEnd_1693674 := by
    simpa [prefixWord, tailWord_1693674, baseEnd_1693674] using wordTrace_append hprefix tailTrace_1693674
  have hstable : (prefixWord ++ tailWord_1693674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693674).length < 2 ^ (prefixWord ++ tailWord_1693674).sum := by decide
  have hdescent : baseEnd_1693674 < baseStart_1693674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693678 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1693678 : Nat := 118140960795 + 1693678 * 2 ^ 59
def prefixEnd_1693678 : Nat := 4983230072969 + 3 ^ 40 * 1693678 * 2
def baseEnd_1693678 : Nat := 289890295981909903578641

theorem tailTrace_1693678 : CollatzResearch.WordTrace tailWord_1693678 prefixEnd_1693678 289890295981909903578641 := by
  unfold tailWord_1693678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721688944762667252321211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41182341038734225345713125 7721688944762667252321211)
  ·
    refine ⟨11582533417144000878481817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7721688944762667252321211 11582533417144000878481817)
    ·
      refine ⟨8686900062858000658861363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11582533417144000878481817 8686900062858000658861363)
      ·
        refine ⟨13030350094287000988292045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8686900062858000658861363 13030350094287000988292045)
        ·
          refine ⟨4886381285357625370609517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13030350094287000988292045 4886381285357625370609517)
          ·
            refine ⟨1832392982009109513978569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4886381285357625370609517 1832392982009109513978569)
            ·
              refine ⟨1374294736506832135483927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832392982009109513978569 1374294736506832135483927)
              ·
                refine ⟨2061442104760248203225891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374294736506832135483927 2061442104760248203225891)
                ·
                  refine ⟨3092163157140372304838837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061442104760248203225891 3092163157140372304838837)
                  ·
                    refine ⟨289890295981909903578641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3092163157140372304838837 289890295981909903578641)
                    ·
                      rfl

theorem cell23_1693678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1693678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693678 prefixEnd_1693678 := by exact prefixLift 1693678
  have htrace : WordTrace (prefixWord ++ tailWord_1693678) baseStart_1693678 baseEnd_1693678 := by
    simpa [prefixWord, tailWord_1693678, baseEnd_1693678] using wordTrace_append hprefix tailTrace_1693678
  have hstable : (prefixWord ++ tailWord_1693678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693678).length < 2 ^ (prefixWord ++ tailWord_1693678).sum := by decide
  have hdescent : baseEnd_1693678 < baseStart_1693678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693681 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 4]
def baseStart_1693681 : Nat := 118140960795 + 1693681 * 2 ^ 59
def prefixEnd_1693681 : Nat := 4983230072969 + 3 ^ 40 * 1693681 * 2
def baseEnd_1693681 : Nat := 869672428387693198998409

theorem tailTrace_1693681 : CollatzResearch.WordTrace tailWord_1693681 prefixEnd_1693681 869672428387693198998409 := by
  unfold tailWord_1693681
  simp only [CollatzResearch.WordTrace]
  refine ⟨61773620977090469530928897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41182413984726979687285931 61773620977090469530928897)
  ·
    refine ⟨46330215732817852148196673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61773620977090469530928897 46330215732817852148196673)
    ·
      refine ⟨34747661799613389111147505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46330215732817852148196673 34747661799613389111147505)
      ·
        refine ⟨26060746349710041833360629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34747661799613389111147505 26060746349710041833360629)
        ·
          refine ⟨2443194970285316421877559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26060746349710041833360629 2443194970285316421877559)
          ·
            refine ⟨3664792455427974632816339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443194970285316421877559 3664792455427974632816339)
            ·
              refine ⟨5497188683141961949224509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664792455427974632816339 5497188683141961949224509)
              ·
                refine ⟨2061445756178235730959191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5497188683141961949224509 2061445756178235730959191)
                ·
                  refine ⟨3092168634267353596438787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061445756178235730959191 3092168634267353596438787)
                  ·
                    refine ⟨4638252951401030394658181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3092168634267353596438787 4638252951401030394658181)
                    ·
                      refine ⟨869672428387693198998409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4638252951401030394658181 869672428387693198998409)
                      ·
                        rfl

theorem cell23_1693681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_1693681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693681 prefixEnd_1693681 := by exact prefixLift 1693681
  have htrace : WordTrace (prefixWord ++ tailWord_1693681) baseStart_1693681 baseEnd_1693681 := by
    simpa [prefixWord, tailWord_1693681, baseEnd_1693681] using wordTrace_append hprefix tailTrace_1693681
  have hstable : (prefixWord ++ tailWord_1693681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693681).length < 2 ^ (prefixWord ++ tailWord_1693681).sum := by decide
  have hdescent : baseEnd_1693681 < baseStart_1693681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693727 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1693727 : Nat := 118140960795 + 1693727 * 2 ^ 59
def prefixEnd_1693727 : Nat := 4983230072969 + 3 ^ 40 * 1693727 * 2
def baseEnd_1693727 : Nat := 869696048497800019023197

theorem tailTrace_1693727 : CollatzResearch.WordTrace tailWord_1693727 prefixEnd_1693727 869696048497800019023197 := by
  unfold tailWord_1693727
  simp only [CollatzResearch.WordTrace]
  refine ⟨61775298734923819387103435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41183532489949212924735623 61775298734923819387103435)
  ·
    refine ⟨92662948102385729080655153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61775298734923819387103435 92662948102385729080655153)
    ·
      refine ⟨69497211076789296810491365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92662948102385729080655153 69497211076789296810491365)
      ·
        refine ⟨13030727076897993151967131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69497211076789296810491365 13030727076897993151967131)
        ·
          refine ⟨19546090615346989727950697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13030727076897993151967131 19546090615346989727950697)
          ·
            refine ⟨14659567961510242295963023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19546090615346989727950697 14659567961510242295963023)
            ·
              refine ⟨21989351942265363443944535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14659567961510242295963023 21989351942265363443944535)
              ·
                refine ⟨32984027913398045165916803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21989351942265363443944535 32984027913398045165916803)
                ·
                  refine ⟨49476041870097067748875205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32984027913398045165916803 49476041870097067748875205)
                  ·
                    refine ⟨9276757850643200202914101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49476041870097067748875205 9276757850643200202914101)
                    ·
                      refine ⟨869696048497800019023197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9276757850643200202914101 869696048497800019023197)
                      ·
                        rfl

theorem cell23_1693727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1693727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693727 prefixEnd_1693727 := by exact prefixLift 1693727
  have htrace : WordTrace (prefixWord ++ tailWord_1693727) baseStart_1693727 baseEnd_1693727 := by
    simpa [prefixWord, tailWord_1693727, baseEnd_1693727] using wordTrace_append hprefix tailTrace_1693727
  have hstable : (prefixWord ++ tailWord_1693727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693727).length < 2 ^ (prefixWord ++ tailWord_1693727).sum := by decide
  have hdescent : baseEnd_1693727 < baseStart_1693727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693747 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 4, 6]
def baseStart_1693747 : Nat := 118140960795 + 1693747 * 2 ^ 59
def prefixEnd_1693747 : Nat := 4983230072969 + 3 ^ 40 * 1693747 * 2
def baseEnd_1693747 : Nat := 289902106036963313591035

theorem tailTrace_1693747 : CollatzResearch.WordTrace tailWord_1693747 prefixEnd_1693747 289902106036963313591035 := by
  unfold tailWord_1693747
  simp only [CollatzResearch.WordTrace]
  refine ⟨61776028194851362802831495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41184018796567575201887663 61776028194851362802831495)
  ·
    refine ⟨92664042292277044204247243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61776028194851362802831495 92664042292277044204247243)
    ·
      refine ⟨138996063438415566306370865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92664042292277044204247243 138996063438415566306370865)
      ·
        refine ⟨104247047578811674729778149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138996063438415566306370865 104247047578811674729778149)
        ·
          refine ⟨19546321421027189011833403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104247047578811674729778149 19546321421027189011833403)
          ·
            refine ⟨29319482131540783517750105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19546321421027189011833403 29319482131540783517750105)
            ·
              refine ⟨21989611598655587638312579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29319482131540783517750105 21989611598655587638312579)
              ·
                refine ⟨32984417397983381457468869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21989611598655587638312579 32984417397983381457468869)
                ·
                  refine ⟨6184578262121884023275413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32984417397983381457468869 6184578262121884023275413)
                  ·
                    refine ⟨289902106036963313591035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6184578262121884023275413 289902106036963313591035)
                    ·
                      rfl

theorem cell23_1693747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 6].length) (baseStart_1693747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693747 prefixEnd_1693747 := by exact prefixLift 1693747
  have htrace : WordTrace (prefixWord ++ tailWord_1693747) baseStart_1693747 baseEnd_1693747 := by
    simpa [prefixWord, tailWord_1693747, baseEnd_1693747] using wordTrace_append hprefix tailTrace_1693747
  have hstable : (prefixWord ++ tailWord_1693747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693747).length < 2 ^ (prefixWord ++ tailWord_1693747).sum := by decide
  have hdescent : baseEnd_1693747 < baseStart_1693747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693774 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1693774 : Nat := 118140960795 + 1693774 * 2 ^ 59
def prefixEnd_1693774 : Nat := 4983230072969 + 3 ^ 40 * 1693774 * 2
def baseEnd_1693774 : Nat := 869720182088561335135481

theorem tailTrace_1693774 : CollatzResearch.WordTrace tailWord_1693774 prefixEnd_1693774 869720182088561335135481 := by
  unfold tailWord_1693774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7722126620719193301758047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41184675310502364276042917 7722126620719193301758047)
  ·
    refine ⟨11583189931078789952637071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7722126620719193301758047 11583189931078789952637071)
    ·
      refine ⟨17374784896618184928955607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11583189931078789952637071 17374784896618184928955607)
      ·
        refine ⟨26062177344927277393433411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17374784896618184928955607 26062177344927277393433411)
        ·
          refine ⟨39093266017390916090150117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26062177344927277393433411 39093266017390916090150117)
          ·
            refine ⟨7329987378260796766903147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39093266017390916090150117 7329987378260796766903147)
            ·
              refine ⟨10994981067391195150354721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7329987378260796766903147 10994981067391195150354721)
              ·
                refine ⟨8246235800543396362766041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10994981067391195150354721 8246235800543396362766041)
                ·
                  refine ⟨6184676850407547272074531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8246235800543396362766041 6184676850407547272074531)
                  ·
                    refine ⟨9277015275611320908111797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6184676850407547272074531 9277015275611320908111797)
                    ·
                      refine ⟨869720182088561335135481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9277015275611320908111797 869720182088561335135481)
                      ·
                        rfl

theorem cell23_1693774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1693774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693774 prefixEnd_1693774 := by exact prefixLift 1693774
  have htrace : WordTrace (prefixWord ++ tailWord_1693774) baseStart_1693774 baseEnd_1693774 := by
    simpa [prefixWord, tailWord_1693774, baseEnd_1693774] using wordTrace_append hprefix tailTrace_1693774
  have hstable : (prefixWord ++ tailWord_1693774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693774).length < 2 ^ (prefixWord ++ tailWord_1693774).sum := by decide
  have hdescent : baseEnd_1693774 < baseStart_1693774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693777 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 9]
def baseStart_1693777 : Nat := 118140960795 + 1693777 * 2 ^ 59
def prefixEnd_1693777 : Nat := 4983230072969 + 3 ^ 40 * 1693777 * 2
def baseEnd_1693777 : Nat := 96635746947836091488663

theorem tailTrace_1693777 : CollatzResearch.WordTrace tailWord_1693777 prefixEnd_1693777 96635746947836091488663 := by
  unfold tailWord_1693777
  simp only [CollatzResearch.WordTrace]
  refine ⟨61777122384742677926423585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41184748256495118617615723 61777122384742677926423585)
  ·
    refine ⟨46332841788557008444817689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61777122384742677926423585 46332841788557008444817689)
    ·
      refine ⟨34749631341417756333613267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46332841788557008444817689 34749631341417756333613267)
      ·
        refine ⟨52124447012126634500419901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34749631341417756333613267 52124447012126634500419901)
        ·
          refine ⟨19546667629547487937657463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52124447012126634500419901 19546667629547487937657463)
          ·
            refine ⟨29320001444321231906486195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19546667629547487937657463 29320001444321231906486195)
            ·
              refine ⟨43980002166481847859729293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29320001444321231906486195 43980002166481847859729293)
              ·
                refine ⟨16492500812430692947398485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43980002166481847859729293 16492500812430692947398485)
                ·
                  refine ⟨96635746947836091488663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16492500812430692947398485 96635746947836091488663)
                  ·
                    rfl

theorem cell23_1693777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 9].length) (baseStart_1693777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693777 prefixEnd_1693777 := by exact prefixLift 1693777
  have htrace : WordTrace (prefixWord ++ tailWord_1693777) baseStart_1693777 baseEnd_1693777 := by
    simpa [prefixWord, tailWord_1693777, baseEnd_1693777] using wordTrace_append hprefix tailTrace_1693777
  have hstable : (prefixWord ++ tailWord_1693777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693777).length < 2 ^ (prefixWord ++ tailWord_1693777).sum := by decide
  have hdescent : baseEnd_1693777 < baseStart_1693777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693788 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_1693788 : Nat := 118140960795 + 1693788 * 2 ^ 59
def prefixEnd_1693788 : Nat := 4983230072969 + 3 ^ 40 * 1693788 * 2
def baseEnd_1693788 : Nat := 869727370817724280360417

theorem tailTrace_1693788 : CollatzResearch.WordTrace tailWord_1693788 prefixEnd_1693788 869727370817724280360417 := by
  unfold tailWord_1693788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30888761793851413402537009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41185015725135217870049345 30888761793851413402537009)
  ·
    refine ⟨23166571345388560051902757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30888761793851413402537009 23166571345388560051902757)
    ·
      refine ⟨4343732127260355009731767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23166571345388560051902757 4343732127260355009731767)
      ·
        refine ⟨6515598190890532514597651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343732127260355009731767 6515598190890532514597651)
        ·
          refine ⟨9773397286335798771896477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515598190890532514597651 9773397286335798771896477)
          ·
            refine ⟨3665023982375924539461179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9773397286335798771896477 3665023982375924539461179)
            ·
              refine ⟨5497535973563886809191769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665023982375924539461179 5497535973563886809191769)
              ·
                refine ⟨4123151980172915106893827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5497535973563886809191769 4123151980172915106893827)
                ·
                  refine ⟨6184727970259372660340741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123151980172915106893827 6184727970259372660340741)
                  ·
                    refine ⟨1159636494423632373813889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184727970259372660340741 1159636494423632373813889)
                    ·
                      refine ⟨869727370817724280360417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159636494423632373813889 869727370817724280360417)
                      ·
                        rfl

theorem cell23_1693788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_1693788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693788 prefixEnd_1693788 := by exact prefixLift 1693788
  have htrace : WordTrace (prefixWord ++ tailWord_1693788) baseStart_1693788 baseEnd_1693788 := by
    simpa [prefixWord, tailWord_1693788, baseEnd_1693788] using wordTrace_append hprefix tailTrace_1693788
  have hstable : (prefixWord ++ tailWord_1693788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693788).length < 2 ^ (prefixWord ++ tailWord_1693788).sum := by decide
  have hdescent : baseEnd_1693788 < baseStart_1693788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693805 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_1693805 : Nat := 118140960795 + 1693805 * 2 ^ 59
def prefixEnd_1693805 : Nat := 4983230072969 + 3 ^ 40 * 1693805 * 2
def baseEnd_1693805 : Nat := 869736099988850713847839

theorem tailTrace_1693805 : CollatzResearch.WordTrace tailWord_1693805 prefixEnd_1693805 869736099988850713847839 := by
  unfold tailWord_1693805
  simp only [CollatzResearch.WordTrace]
  refine ⟨61778143628641238708442869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41185429085760825805628579 61778143628641238708442869)
  ·
    refine ⟨5791700965185116128916519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61778143628641238708442869 5791700965185116128916519)
    ·
      refine ⟨8687551447777674193374779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5791700965185116128916519 8687551447777674193374779)
      ·
        refine ⟨13031327171666511290062169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8687551447777674193374779 13031327171666511290062169)
        ·
          refine ⟨9773495378749883467546627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13031327171666511290062169 9773495378749883467546627)
          ·
            refine ⟨14660243068124825201319941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9773495378749883467546627 14660243068124825201319941)
            ·
              refine ⟨2748795575273404725247489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14660243068124825201319941 2748795575273404725247489)
              ·
                refine ⟨2061596681455053543935617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2748795575273404725247489 2061596681455053543935617)
                ·
                  refine ⟨1546197511091290157951713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2061596681455053543935617 1546197511091290157951713)
                  ·
                    refine ⟨1159648133318467618463785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1546197511091290157951713 1159648133318467618463785)
                    ·
                      refine ⟨869736099988850713847839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159648133318467618463785 869736099988850713847839)
                      ·
                        rfl

theorem cell23_1693805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_1693805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693805 prefixEnd_1693805 := by exact prefixLift 1693805
  have htrace : WordTrace (prefixWord ++ tailWord_1693805) baseStart_1693805 baseEnd_1693805 := by
    simpa [prefixWord, tailWord_1693805, baseEnd_1693805] using wordTrace_append hprefix tailTrace_1693805
  have hstable : (prefixWord ++ tailWord_1693805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693805).length < 2 ^ (prefixWord ++ tailWord_1693805).sum := by decide
  have hdescent : baseEnd_1693805 < baseStart_1693805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693821 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_1693821 : Nat := 118140960795 + 1693821 * 2 ^ 59
def prefixEnd_1693821 : Nat := 4983230072969 + 3 ^ 40 * 1693821 * 2
def baseEnd_1693821 : Nat := 869744315679322651247765

theorem tailTrace_1693821 : CollatzResearch.WordTrace tailWord_1693821 prefixEnd_1693821 869744315679322651247765 := by
  unfold tailWord_1693821
  simp only [CollatzResearch.WordTrace]
  refine ⟨61778727196583273441025317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41185818131055515627350211 61778727196583273441025317)
  ·
    refine ⟨11583511349359363770192247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61778727196583273441025317 11583511349359363770192247)
    ·
      refine ⟨17375267024039045655288371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11583511349359363770192247 17375267024039045655288371)
      ·
        refine ⟨26062900536058568482932557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17375267024039045655288371 26062900536058568482932557)
        ·
          refine ⟨9773587701021963181099709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26062900536058568482932557 9773587701021963181099709)
          ·
            refine ⟨3665095387883236192912391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9773587701021963181099709 3665095387883236192912391)
            ·
              refine ⟨5497643081824854289368587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665095387883236192912391 5497643081824854289368587)
              ·
                refine ⟨8246464622737281434052881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5497643081824854289368587 8246464622737281434052881)
                ·
                  refine ⟨6184848467052961075539661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8246464622737281434052881 6184848467052961075539661)
                  ·
                    refine ⟨2319318175144860403327373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6184848467052961075539661 2319318175144860403327373)
                    ·
                      refine ⟨869744315679322651247765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2319318175144860403327373 869744315679322651247765)
                      ·
                        rfl

theorem cell23_1693821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_1693821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693821 prefixEnd_1693821 := by exact prefixLift 1693821
  have htrace : WordTrace (prefixWord ++ tailWord_1693821) baseStart_1693821 baseEnd_1693821 := by
    simpa [prefixWord, tailWord_1693821, baseEnd_1693821] using wordTrace_append hprefix tailTrace_1693821
  have hstable : (prefixWord ++ tailWord_1693821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693821).length < 2 ^ (prefixWord ++ tailWord_1693821).sum := by decide
  have hdescent : baseEnd_1693821 < baseStart_1693821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693861 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 4, 4, 2]
def baseStart_1693861 : Nat := 118140960795 + 1693861 * 2 ^ 59
def prefixEnd_1693861 : Nat := 4983230072969 + 3 ^ 40 * 1693861 * 2
def baseEnd_1693861 : Nat := 869764854905502494747581

theorem tailTrace_1693861 : CollatzResearch.WordTrace tailWord_1693861 prefixEnd_1693861 869764854905502494747581 := by
  unfold tailWord_1693861
  simp only [CollatzResearch.WordTrace]
  refine ⟨61780186116438360272481437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41186790744292240181654291 61780186116438360272481437)
  ·
    refine ⟨23167569793664385102180539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61780186116438360272481437 23167569793664385102180539)
    ·
      refine ⟨34751354690496577653270809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23167569793664385102180539 34751354690496577653270809)
      ·
        refine ⟨26063516017872433239953107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34751354690496577653270809 26063516017872433239953107)
        ·
          refine ⟨39095274026808649859929661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26063516017872433239953107 39095274026808649859929661)
          ·
            refine ⟨14660727760053243697473623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39095274026808649859929661 14660727760053243697473623)
            ·
              refine ⟨21991091640079865546210435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14660727760053243697473623 21991091640079865546210435)
              ·
                refine ⟨32986637460119798319315653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21991091640079865546210435 32986637460119798319315653)
                ·
                  refine ⟨6184994523772462184871685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32986637460119798319315653 6184994523772462184871685)
                  ·
                    refine ⟨1159686473207336659663441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184994523772462184871685 1159686473207336659663441)
                    ·
                      refine ⟨869764854905502494747581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159686473207336659663441 869764854905502494747581)
                      ·
                        rfl

theorem cell23_1693861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_1693861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693861 prefixEnd_1693861 := by exact prefixLift 1693861
  have htrace : WordTrace (prefixWord ++ tailWord_1693861) baseStart_1693861 baseEnd_1693861 := by
    simpa [prefixWord, tailWord_1693861, baseEnd_1693861] using wordTrace_append hprefix tailTrace_1693861
  have hstable : (prefixWord ++ tailWord_1693861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693861).length < 2 ^ (prefixWord ++ tailWord_1693861).sum := by decide
  have hdescent : baseEnd_1693861 < baseStart_1693861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693874 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1693874 : Nat := 118140960795 + 1693874 * 2 ^ 59
def prefixEnd_1693874 : Nat := 4983230072969 + 3 ^ 40 * 1693874 * 2
def baseEnd_1693874 : Nat := 869771530154010943885021

theorem tailTrace_1693874 : CollatzResearch.WordTrace tailWord_1693874 prefixEnd_1693874 869771530154010943885021 := by
  unfold tailWord_1693874
  simp only [CollatzResearch.WordTrace]
  refine ⟨15445165066347815873176169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41187106843594175661803117 15445165066347815873176169)
  ·
    refine ⟨11583873799760861904882127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15445165066347815873176169 11583873799760861904882127)
    ·
      refine ⟨17375810699641292857323191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11583873799760861904882127 17375810699641292857323191)
      ·
        refine ⟨26063716049461939285984787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17375810699641292857323191 26063716049461939285984787)
        ·
          refine ⟨39095574074192908928977181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26063716049461939285984787 39095574074192908928977181)
          ·
            refine ⟨14660840277822340848366443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39095574074192908928977181 14660840277822340848366443)
            ·
              refine ⟨21991260416733511272549665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14660840277822340848366443 21991260416733511272549665)
              ·
                refine ⟨16493445312550133454412249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21991260416733511272549665 16493445312550133454412249)
                ·
                  refine ⟨12370083984412600090809187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16493445312550133454412249 12370083984412600090809187)
                  ·
                    refine ⟨18555125976618900136213781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12370083984412600090809187 18555125976618900136213781)
                    ·
                      refine ⟨869771530154010943885021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18555125976618900136213781 869771530154010943885021)
                      ·
                        rfl

theorem cell23_1693874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1693874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693874 prefixEnd_1693874 := by exact prefixLift 1693874
  have htrace : WordTrace (prefixWord ++ tailWord_1693874) baseStart_1693874 baseEnd_1693874 := by
    simpa [prefixWord, tailWord_1693874, baseEnd_1693874] using wordTrace_append hprefix tailTrace_1693874
  have hstable : (prefixWord ++ tailWord_1693874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693874).length < 2 ^ (prefixWord ++ tailWord_1693874).sum := by decide
  have hdescent : baseEnd_1693874 < baseStart_1693874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693924 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1693924 : Nat := 118140960795 + 1693924 * 2 ^ 59
def prefixEnd_1693924 : Nat := 4983230072969 + 3 ^ 40 * 1693924 * 2
def baseEnd_1693924 : Nat := 869797204186735748259791

theorem tailTrace_1693924 : CollatzResearch.WordTrace tailWord_1693924 prefixEnd_1693924 869797204186735748259791 := by
  unfold tailWord_1693924
  simp only [CollatzResearch.WordTrace]
  refine ⟨30891241957605061016012413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41188322610140081354683217 30891241957605061016012413)
  ·
    refine ⟨11584215734101897881004655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30891241957605061016012413 11584215734101897881004655)
    ·
      refine ⟨17376323601152846821506983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11584215734101897881004655 17376323601152846821506983)
      ·
        refine ⟨26064485401729270232260475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17376323601152846821506983 26064485401729270232260475)
        ·
          refine ⟨39096728102593905348390713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26064485401729270232260475 39096728102593905348390713)
          ·
            refine ⟨29322546076945429011293035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39096728102593905348390713 29322546076945429011293035)
            ·
              refine ⟨43983819115418143516939553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29322546076945429011293035 43983819115418143516939553)
              ·
                refine ⟨32987864336563607637704665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43983819115418143516939553 32987864336563607637704665)
                ·
                  refine ⟨24740898252422705728278499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32987864336563607637704665 24740898252422705728278499)
                  ·
                    refine ⟨37111347378634058592417749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24740898252422705728278499 37111347378634058592417749)
                    ·
                      refine ⟨869797204186735748259791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37111347378634058592417749 869797204186735748259791)
                      ·
                        rfl

theorem cell23_1693924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1693924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693924 prefixEnd_1693924 := by exact prefixLift 1693924
  have htrace : WordTrace (prefixWord ++ tailWord_1693924) baseStart_1693924 baseEnd_1693924 := by
    simpa [prefixWord, tailWord_1693924, baseEnd_1693924] using wordTrace_append hprefix tailTrace_1693924
  have hstable : (prefixWord ++ tailWord_1693924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693924).length < 2 ^ (prefixWord ++ tailWord_1693924).sum := by decide
  have hdescent : baseEnd_1693924 < baseStart_1693924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693944 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 5, 6]
def baseStart_1693944 : Nat := 118140960795 + 1693944 * 2 ^ 59
def prefixEnd_1693944 : Nat := 4983230072969 + 3 ^ 40 * 1693944 * 2
def baseEnd_1693944 : Nat := 289935824599941890003233

theorem tailTrace_1693944 : CollatzResearch.WordTrace tailWord_1693944 prefixEnd_1693944 289935824599941890003233 := by
  unfold tailWord_1693944
  simp only [CollatzResearch.WordTrace]
  refine ⟨30891606687568832723876443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41188808916758443631835257 30891606687568832723876443)
  ·
    refine ⟨46337410031353249085814665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30891606687568832723876443 46337410031353249085814665)
    ·
      refine ⟨34753057523514936814360999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46337410031353249085814665 34753057523514936814360999)
      ·
        refine ⟨52129586285272405221541499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34753057523514936814360999 52129586285272405221541499)
        ·
          refine ⟨78194379427908607832312249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52129586285272405221541499 78194379427908607832312249)
          ·
            refine ⟨58645784570931455874234187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78194379427908607832312249 58645784570931455874234187)
            ·
              refine ⟨87968676856397183811351281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58645784570931455874234187 87968676856397183811351281)
              ·
                refine ⟨65976507642297887858513461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87968676856397183811351281 65976507642297887858513461)
                ·
                  refine ⟨6185297591465426986735637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65976507642297887858513461 6185297591465426986735637)
                  ·
                    refine ⟨289935824599941890003233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6185297591465426986735637 289935824599941890003233)
                    ·
                      rfl

theorem cell23_1693944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_1693944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693944 prefixEnd_1693944 := by exact prefixLift 1693944
  have htrace : WordTrace (prefixWord ++ tailWord_1693944) baseStart_1693944 baseEnd_1693944 := by
    simpa [prefixWord, tailWord_1693944, baseEnd_1693944] using wordTrace_append hprefix tailTrace_1693944
  have hstable : (prefixWord ++ tailWord_1693944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693944).length < 2 ^ (prefixWord ++ tailWord_1693944).sum := by decide
  have hdescent : baseEnd_1693944 < baseStart_1693944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693948 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_1693948 : Nat := 118140960795 + 1693948 * 2 ^ 59
def prefixEnd_1693948 : Nat := 4983230072969 + 3 ^ 40 * 1693948 * 2
def baseEnd_1693948 : Nat := 289936509240814551453227

theorem tailTrace_1693948 : CollatzResearch.WordTrace tailWord_1693948 prefixEnd_1693948 289936509240814551453227 := by
  unfold tailWord_1693948
  simp only [CollatzResearch.WordTrace]
  refine ⟨30891679633561587065449249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41188906178082116087265665 30891679633561587065449249)
  ·
    refine ⟨23168759725171190299086937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30891679633561587065449249 23168759725171190299086937)
    ·
      refine ⟨17376569793878392724315203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23168759725171190299086937 17376569793878392724315203)
      ·
        refine ⟨26064854690817589086472805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17376569793878392724315203 26064854690817589086472805)
        ·
          refine ⟨4887160254528297953713651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26064854690817589086472805 4887160254528297953713651)
          ·
            refine ⟨7330740381792446930570477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887160254528297953713651 7330740381792446930570477)
            ·
              refine ⟨2749027643172167598963929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7330740381792446930570477 2749027643172167598963929)
              ·
                refine ⟨2061770732379125699222947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2749027643172167598963929 2061770732379125699222947)
                ·
                  refine ⟨3092656098568688548834421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061770732379125699222947 3092656098568688548834421)
                  ·
                    refine ⟨289936509240814551453227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3092656098568688548834421 289936509240814551453227)
                    ·
                      rfl

theorem cell23_1693948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_1693948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693948 prefixEnd_1693948 := by exact prefixLift 1693948
  have htrace : WordTrace (prefixWord ++ tailWord_1693948) baseStart_1693948 baseEnd_1693948 := by
    simpa [prefixWord, tailWord_1693948, baseEnd_1693948] using wordTrace_append hprefix tailTrace_1693948
  have hstable : (prefixWord ++ tailWord_1693948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693948).length < 2 ^ (prefixWord ++ tailWord_1693948).sum := by decide
  have hdescent : baseEnd_1693948 < baseStart_1693948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693951 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_1693951 : Nat := 118140960795 + 1693951 * 2 ^ 59
def prefixEnd_1693951 : Nat := 4983230072969 + 3 ^ 40 * 1693951 * 2
def baseEnd_1693951 : Nat := 869811068164407142622167

theorem tailTrace_1693951 : CollatzResearch.WordTrace tailWord_1693951 prefixEnd_1693951 869811068164407142622167 := by
  unfold tailWord_1693951
  simp only [CollatzResearch.WordTrace]
  refine ⟨61783468686112305643257707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41188979124074870428838471 61783468686112305643257707)
  ·
    refine ⟨92675203029168458464886561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61783468686112305643257707 92675203029168458464886561)
    ·
      refine ⟨69506402271876343848664921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92675203029168458464886561 69506402271876343848664921)
      ·
        refine ⟨52129801703907257886498691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69506402271876343848664921 52129801703907257886498691)
        ·
          refine ⟨78194702555860886829748037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52129801703907257886498691 78194702555860886829748037)
          ·
            refine ⟨14661506729223916280577757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78194702555860886829748037 14661506729223916280577757)
            ·
              refine ⟨5498065023458968605216659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14661506729223916280577757 5498065023458968605216659)
              ·
                refine ⟨8247097535188452907824989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498065023458968605216659 8247097535188452907824989)
                ·
                  refine ⟨3092661575695669840434371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8247097535188452907824989 3092661575695669840434371)
                  ·
                    refine ⟨4638992363543504760651557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3092661575695669840434371 4638992363543504760651557)
                    ·
                      refine ⟨869811068164407142622167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4638992363543504760651557 869811068164407142622167)
                      ·
                        rfl

theorem cell23_1693951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_1693951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693951 prefixEnd_1693951 := by exact prefixLift 1693951
  have htrace : WordTrace (prefixWord ++ tailWord_1693951) baseStart_1693951 baseEnd_1693951 := by
    simpa [prefixWord, tailWord_1693951, baseEnd_1693951] using wordTrace_append hprefix tailTrace_1693951
  have hstable : (prefixWord ++ tailWord_1693951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693951).length < 2 ^ (prefixWord ++ tailWord_1693951).sum := by decide
  have hdescent : baseEnd_1693951 < baseStart_1693951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693961 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 1, 6]
def baseStart_1693961 : Nat := 118140960795 + 1693961 * 2 ^ 59
def prefixEnd_1693961 : Nat := 4983230072969 + 3 ^ 40 * 1693961 * 2
def baseEnd_1693961 : Nat := 289938734323650701165707

theorem tailTrace_1693961 : CollatzResearch.WordTrace tailWord_1693961 prefixEnd_1693961 289938734323650701165707 := by
  unfold tailWord_1693961
  simp only [CollatzResearch.WordTrace]
  refine ⟨61783833416076077351121737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41189222277384051567414491 61783833416076077351121737)
  ·
    refine ⟨46337875062057058013341303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61783833416076077351121737 46337875062057058013341303)
    ·
      refine ⟨69506812593085587020011955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46337875062057058013341303 69506812593085587020011955)
      ·
        refine ⟨104260218889628380530017933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69506812593085587020011955 104260218889628380530017933)
        ·
          refine ⟨39097582083610642698756725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104260218889628380530017933 39097582083610642698756725)
          ·
            refine ⟨3665398320338497753008443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39097582083610642698756725 3665398320338497753008443)
            ·
              refine ⟨5498097480507746629512665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665398320338497753008443 5498097480507746629512665)
              ·
                refine ⟨4123573110380809972134499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498097480507746629512665 4123573110380809972134499)
                ·
                  refine ⟨6185359665571214958201749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123573110380809972134499 6185359665571214958201749)
                  ·
                    refine ⟨289938734323650701165707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6185359665571214958201749 289938734323650701165707)
                    ·
                      rfl

theorem cell23_1693961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_1693961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693961 prefixEnd_1693961 := by exact prefixLift 1693961
  have htrace : WordTrace (prefixWord ++ tailWord_1693961) baseStart_1693961 baseEnd_1693961 := by
    simpa [prefixWord, tailWord_1693961, baseEnd_1693961] using wordTrace_append hprefix tailTrace_1693961
  have hstable : (prefixWord ++ tailWord_1693961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693961).length < 2 ^ (prefixWord ++ tailWord_1693961).sum := by decide
  have hdescent : baseEnd_1693961 < baseStart_1693961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693988 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1693988 : Nat := 118140960795 + 1693988 * 2 ^ 59
def prefixEnd_1693988 : Nat := 4983230072969 + 3 ^ 40 * 1693988 * 2
def baseEnd_1693988 : Nat := 869830066948623497859497

theorem tailTrace_1693988 : CollatzResearch.WordTrace tailWord_1693988 prefixEnd_1693988 869830066948623497859497 := by
  unfold tailWord_1693988
  simp only [CollatzResearch.WordTrace]
  refine ⟨30892409093489130481177309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41189878791318840641569745 30892409093489130481177309)
  ·
    refine ⟨11584653410058423930441491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30892409093489130481177309 11584653410058423930441491)
    ·
      refine ⟨17376980115087635895662237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11584653410058423930441491 17376980115087635895662237)
      ·
        refine ⟨6516367543157863460873339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17376980115087635895662237 6516367543157863460873339)
        ·
          refine ⟨9774551314736795191310009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6516367543157863460873339 9774551314736795191310009)
          ·
            refine ⟨7330913486052596393482507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9774551314736795191310009 7330913486052596393482507)
            ·
              refine ⟨10996370229078894590223761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330913486052596393482507 10996370229078894590223761)
              ·
                refine ⟨8247277671809170942667821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10996370229078894590223761 8247277671809170942667821)
                ·
                  refine ⟨3092729126928439103500433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8247277671809170942667821 3092729126928439103500433)
                  ·
                    refine ⟨2319546845196329327625325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3092729126928439103500433 2319546845196329327625325)
                    ·
                      refine ⟨869830066948623497859497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2319546845196329327625325 869830066948623497859497)
                      ·
                        rfl

theorem cell23_1693988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1693988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1693988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1693988 prefixEnd_1693988 := by exact prefixLift 1693988
  have htrace : WordTrace (prefixWord ++ tailWord_1693988) baseStart_1693988 baseEnd_1693988 := by
    simpa [prefixWord, tailWord_1693988, baseEnd_1693988] using wordTrace_append hprefix tailTrace_1693988
  have hstable : (prefixWord ++ tailWord_1693988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693988).length < 2 ^ (prefixWord ++ tailWord_1693988).sum := by decide
  have hdescent : baseEnd_1693988 < baseStart_1693988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694002 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_1694002 : Nat := 118140960795 + 1694002 * 2 ^ 59
def prefixEnd_1694002 : Nat := 4983230072969 + 3 ^ 40 * 1694002 * 2
def baseEnd_1694002 : Nat := 869837255677786443084433

theorem tailTrace_1694002 : CollatzResearch.WordTrace tailWord_1694002 prefixEnd_1694002 869837255677786443084433 := by
  unfold tailWord_1694002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15446332202231885338341065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41190219205951694235576173 15446332202231885338341065)
  ·
    refine ⟨11584749151673914003755799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15446332202231885338341065 11584749151673914003755799)
    ·
      refine ⟨17377123727510871005633699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11584749151673914003755799 17377123727510871005633699)
      ·
        refine ⟨26065685591266306508450549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17377123727510871005633699 26065685591266306508450549)
        ·
          refine ⟨2443658024181216235167239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26065685591266306508450549 2443658024181216235167239)
          ·
            refine ⟨3665487036271824352750859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443658024181216235167239 3665487036271824352750859)
            ·
              refine ⟨5498230554407736529126289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665487036271824352750859 5498230554407736529126289)
              ·
                refine ⟨4123672915805802396844717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498230554407736529126289 4123672915805802396844717)
                ·
                  refine ⟨1546377343427175898816769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4123672915805802396844717 1546377343427175898816769)
                  ·
                    refine ⟨1159783007570381924112577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1546377343427175898816769 1159783007570381924112577)
                    ·
                      refine ⟨869837255677786443084433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159783007570381924112577 869837255677786443084433)
                      ·
                        rfl

theorem cell23_1694002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_1694002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694002 prefixEnd_1694002 := by exact prefixLift 1694002
  have htrace : WordTrace (prefixWord ++ tailWord_1694002) baseStart_1694002 baseEnd_1694002 := by
    simpa [prefixWord, tailWord_1694002, baseEnd_1694002] using wordTrace_append hprefix tailTrace_1694002
  have hstable : (prefixWord ++ tailWord_1694002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694002).length < 2 ^ (prefixWord ++ tailWord_1694002).sum := by decide
  have hdescent : baseEnd_1694002 < baseStart_1694002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694046 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1694046 : Nat := 118140960795 + 1694046 * 2 ^ 59
def prefixEnd_1694046 : Nat := 4983230072969 + 3 ^ 40 * 1694046 * 2
def baseEnd_1694046 : Nat := 289953282942194756978077

theorem tailTrace_1694046 : CollatzResearch.WordTrace tailWord_1694046 prefixEnd_1694046 289953282942194756978077 := by
  unfold tailWord_1694046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7723366702596017108495749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41191289080512091245310661 7723366702596017108495749)
  ·
    refine ⟨1448131256736753207842953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7723366702596017108495749 1448131256736753207842953)
    ·
      refine ⟨1086098442552564905882215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1448131256736753207842953 1086098442552564905882215)
      ·
        refine ⟨1629147663828847358823323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086098442552564905882215 1629147663828847358823323)
        ·
          refine ⟨2443721495743271038234985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629147663828847358823323 2443721495743271038234985)
          ·
            refine ⟨1832791121807453278676239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2443721495743271038234985 1832791121807453278676239)
            ·
              refine ⟨2749186682711179918014359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832791121807453278676239 2749186682711179918014359)
              ·
                refine ⟨4123780024066769877021539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749186682711179918014359 4123780024066769877021539)
                ·
                  refine ⟨6185670036100154815532309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123780024066769877021539 6185670036100154815532309)
                  ·
                    refine ⟨289953282942194756978077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6185670036100154815532309 289953282942194756978077)
                    ·
                      rfl

theorem cell23_1694046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1694046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694046 prefixEnd_1694046 := by exact prefixLift 1694046
  have htrace : WordTrace (prefixWord ++ tailWord_1694046) baseStart_1694046 baseEnd_1694046 := by
    simpa [prefixWord, tailWord_1694046, baseEnd_1694046] using wordTrace_append hprefix tailTrace_1694046
  have hstable : (prefixWord ++ tailWord_1694046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694046).length < 2 ^ (prefixWord ++ tailWord_1694046).sum := by decide
  have hdescent : baseEnd_1694046 < baseStart_1694046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694051 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 2, 6]
def baseStart_1694051 : Nat := 118140960795 + 1694051 * 2 ^ 59
def prefixEnd_1694051 : Nat := 4983230072969 + 3 ^ 40 * 1694051 * 2
def baseEnd_1694051 : Nat := 289954138743285583790569

theorem tailTrace_1694051 : CollatzResearch.WordTrace tailWord_1694051 prefixEnd_1694051 289954138743285583790569 := by
  unfold tailWord_1694051
  simp only [CollatzResearch.WordTrace]
  refine ⟨61787115985750022721898007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41191410657166681814598671 61787115985750022721898007)
  ·
    refine ⟨92680673978625034082847011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61787115985750022721898007 92680673978625034082847011)
    ·
      refine ⟨139021010967937551124270517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92680673978625034082847011 139021010967937551124270517)
      ·
        refine ⟨13033219778244145417900361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139021010967937551124270517 13033219778244145417900361)
        ·
          refine ⟨9774914833683109063425271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13033219778244145417900361 9774914833683109063425271)
          ·
            refine ⟨14662372250524663595137907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9774914833683109063425271 14662372250524663595137907)
            ·
              refine ⟨21993558375786995392706861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14662372250524663595137907 21993558375786995392706861)
              ·
                refine ⟨8247584390920123272265073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21993558375786995392706861 8247584390920123272265073)
                ·
                  refine ⟨6185688293190092454198805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8247584390920123272265073 6185688293190092454198805)
                  ·
                    refine ⟨289954138743285583790569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6185688293190092454198805 289954138743285583790569)
                    ·
                      rfl

theorem cell23_1694051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 6].length) (baseStart_1694051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694051 prefixEnd_1694051 := by exact prefixLift 1694051
  have htrace : WordTrace (prefixWord ++ tailWord_1694051) baseStart_1694051 baseEnd_1694051 := by
    simpa [prefixWord, tailWord_1694051, baseEnd_1694051] using wordTrace_append hprefix tailTrace_1694051
  have hstable : (prefixWord ++ tailWord_1694051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694051).length < 2 ^ (prefixWord ++ tailWord_1694051).sum := by decide
  have hdescent : baseEnd_1694051 < baseStart_1694051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694052 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_1694052 : Nat := 118140960795 + 1694052 * 2 ^ 59
def prefixEnd_1694052 : Nat := 4983230072969 + 3 ^ 40 * 1694052 * 2
def baseEnd_1694052 : Nat := 869862929710511247459203

theorem tailTrace_1694052 : CollatzResearch.WordTrace tailWord_1694052 prefixEnd_1694052 869862929710511247459203 := by
  unfold tailWord_1694052
  simp only [CollatzResearch.WordTrace]
  refine ⟨30893576229373199946342205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41191434972497599928456273 30893576229373199946342205)
  ·
    refine ⟨11585091086014949979878327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30893576229373199946342205 11585091086014949979878327)
    ·
      refine ⟨17377636629022424969817491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11585091086014949979878327 17377636629022424969817491)
      ·
        refine ⟨26066454943533637454726237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17377636629022424969817491 26066454943533637454726237)
        ·
          refine ⟨9774920603825114045522339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26066454943533637454726237 9774920603825114045522339)
          ·
            refine ⟨14662380905737671068283509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9774920603825114045522339 14662380905737671068283509)
            ·
              refine ⟨1374598209912906662651579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14662380905737671068283509 1374598209912906662651579)
              ·
                refine ⟨2061897314869359993977369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374598209912906662651579 2061897314869359993977369)
                ·
                  refine ⟨1546422986152019995483027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2061897314869359993977369 1546422986152019995483027)
                  ·
                    refine ⟨2319634479228029993224541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1546422986152019995483027 2319634479228029993224541)
                    ·
                      refine ⟨869862929710511247459203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2319634479228029993224541 869862929710511247459203)
                      ·
                        rfl

theorem cell23_1694052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_1694052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694052 prefixEnd_1694052 := by exact prefixLift 1694052
  have htrace : WordTrace (prefixWord ++ tailWord_1694052) baseStart_1694052 baseEnd_1694052 := by
    simpa [prefixWord, tailWord_1694052, baseEnd_1694052] using wordTrace_append hprefix tailTrace_1694052
  have hstable : (prefixWord ++ tailWord_1694052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694052).length < 2 ^ (prefixWord ++ tailWord_1694052).sum := by decide
  have hdescent : baseEnd_1694052 < baseStart_1694052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694070 : List Nat := [5, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1694070 : Nat := 118140960795 + 1694070 * 2 ^ 59
def prefixEnd_1694070 : Nat := 4983230072969 + 3 ^ 40 * 1694070 * 2
def baseEnd_1694070 : Nat := 869872172362292177034121

theorem tailTrace_1694070 : CollatzResearch.WordTrace tailWord_1694070 prefixEnd_1694070 869872172362292177034121 := by
  unfold tailWord_1694070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3861738060792574310427479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41191872648454125977893109 3861738060792574310427479)
  ·
    refine ⟨5792607091188861465641219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3861738060792574310427479 5792607091188861465641219)
    ·
      refine ⟨8688910636783292198461829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5792607091188861465641219 8688910636783292198461829)
      ·
        refine ⟨1629170744396867287211593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8688910636783292198461829 1629170744396867287211593)
        ·
          refine ⟨1221878058297650465408695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1629170744396867287211593 1221878058297650465408695)
          ·
            refine ⟨1832817087446475698113043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221878058297650465408695 1832817087446475698113043)
            ·
              refine ⟨2749225631169713547169565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832817087446475698113043 2749225631169713547169565)
              ·
                refine ⟨1030959611688642580188587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2749225631169713547169565 1030959611688642580188587)
                ·
                  refine ⟨1546439417532963870282881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030959611688642580188587 1546439417532963870282881)
                  ·
                    refine ⟨1159829563149722902712161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1546439417532963870282881 1159829563149722902712161)
                    ·
                      refine ⟨869872172362292177034121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159829563149722902712161 869872172362292177034121)
                      ·
                        rfl

theorem cell23_1694070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1694070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694070 prefixEnd_1694070 := by exact prefixLift 1694070
  have htrace : WordTrace (prefixWord ++ tailWord_1694070) baseStart_1694070 baseEnd_1694070 := by
    simpa [prefixWord, tailWord_1694070, baseEnd_1694070] using wordTrace_append hprefix tailTrace_1694070
  have hstable : (prefixWord ++ tailWord_1694070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694070).length < 2 ^ (prefixWord ++ tailWord_1694070).sum := by decide
  have hdescent : baseEnd_1694070 < baseStart_1694070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694071 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_1694071 : Nat := 118140960795 + 1694071 * 2 ^ 59
def prefixEnd_1694071 : Nat := 4983230072969 + 3 ^ 40 * 1694071 * 2
def baseEnd_1694071 : Nat := 869872685842946673121615

theorem tailTrace_1694071 : CollatzResearch.WordTrace tailWord_1694071 prefixEnd_1694071 869872685842946673121615 := by
  unfold tailWord_1694071
  simp only [CollatzResearch.WordTrace]
  refine ⟨61787845445677566137626067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41191896963785044091750711 61787845445677566137626067)
  ·
    refine ⟨92681768168516349206439101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61787845445677566137626067 92681768168516349206439101)
    ·
      refine ⟨34755663063193630952414663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92681768168516349206439101 34755663063193630952414663)
      ·
        refine ⟨52133494594790446428621995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34755663063193630952414663 52133494594790446428621995)
        ·
          refine ⟨78200241892185669642932993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52133494594790446428621995 78200241892185669642932993)
          ·
            refine ⟨58650181419139252232199745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78200241892185669642932993 58650181419139252232199745)
            ·
              refine ⟨43987636064354439174149809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58650181419139252232199745 43987636064354439174149809)
              ·
                refine ⟨32990727048265829380612357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43987636064354439174149809 32990727048265829380612357)
                ·
                  refine ⟨6185761321549843008864817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32990727048265829380612357 6185761321549843008864817)
                  ·
                    refine ⟨4639320991162382256648613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6185761321549843008864817 4639320991162382256648613)
                    ·
                      refine ⟨869872685842946673121615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4639320991162382256648613 869872685842946673121615)
                      ·
                        rfl

theorem cell23_1694071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_1694071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694071 prefixEnd_1694071 := by exact prefixLift 1694071
  have htrace : WordTrace (prefixWord ++ tailWord_1694071) baseStart_1694071 baseEnd_1694071 := by
    simpa [prefixWord, tailWord_1694071, baseEnd_1694071] using wordTrace_append hprefix tailTrace_1694071
  have hstable : (prefixWord ++ tailWord_1694071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694071).length < 2 ^ (prefixWord ++ tailWord_1694071).sum := by decide
  have hdescent : baseEnd_1694071 < baseStart_1694071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694075 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 4, 2, 2]
def baseStart_1694075 : Nat := 118140960795 + 1694075 * 2 ^ 59
def prefixEnd_1694075 : Nat := 4983230072969 + 3 ^ 40 * 1694075 * 2
def baseEnd_1694075 : Nat := 869874739765564657471597

theorem tailTrace_1694075 : CollatzResearch.WordTrace tailWord_1694075 prefixEnd_1694075 869874739765564657471597 := by
  unfold tailWord_1694075
  simp only [CollatzResearch.WordTrace]
  refine ⟨61787991337663074820771679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41191994225108716547181119 61787991337663074820771679)
  ·
    refine ⟨92681987006494612231157519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61787991337663074820771679 92681987006494612231157519)
    ·
      refine ⟨139022980509741918346736279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92681987006494612231157519 139022980509741918346736279)
      ·
        refine ⟨208534470764612877520104419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139022980509741918346736279 208534470764612877520104419)
        ·
          refine ⟨312801706146919316280156629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208534470764612877520104419 312801706146919316280156629)
          ·
            refine ⟨7331289987818421475316171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 312801706146919316280156629 7331289987818421475316171)
            ·
              refine ⟨10996934981727632212974257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331289987818421475316171 10996934981727632212974257)
              ·
                refine ⟨8247701236295724159730693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10996934981727632212974257 8247701236295724159730693)
                ·
                  refine ⟨1546443981805448279949505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8247701236295724159730693 1546443981805448279949505)
                  ·
                    refine ⟨1159832986354086209962129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1546443981805448279949505 1159832986354086209962129)
                    ·
                      refine ⟨869874739765564657471597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159832986354086209962129 869874739765564657471597)
                      ·
                        rfl

theorem cell23_1694075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 2, 2].length) (baseStart_1694075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694075 prefixEnd_1694075 := by exact prefixLift 1694075
  have htrace : WordTrace (prefixWord ++ tailWord_1694075) baseStart_1694075 baseEnd_1694075 := by
    simpa [prefixWord, tailWord_1694075, baseEnd_1694075] using wordTrace_append hprefix tailTrace_1694075
  have hstable : (prefixWord ++ tailWord_1694075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694075).length < 2 ^ (prefixWord ++ tailWord_1694075).sum := by decide
  have hdescent : baseEnd_1694075 < baseStart_1694075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694109 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_1694109 : Nat := 118140960795 + 1694109 * 2 ^ 59
def prefixEnd_1694109 : Nat := 4983230072969 + 3 ^ 40 * 1694109 * 2
def baseEnd_1694109 : Nat := 869892198107817524446441

theorem tailTrace_1694109 : CollatzResearch.WordTrace tailWord_1694109 prefixEnd_1694109 869892198107817524446441 := by
  unfold tailWord_1694109
  simp only [CollatzResearch.WordTrace]
  refine ⟨61789231419539898627509381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41192820946359932418339587 61789231419539898627509381)
  ·
    refine ⟨11585480891163730992658009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61789231419539898627509381 11585480891163730992658009)
    ·
      refine ⟨8689110668372798244493507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11585480891163730992658009 8689110668372798244493507)
      ·
        refine ⟨13033666002559197366740261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8689110668372798244493507 13033666002559197366740261)
        ·
          refine ⟨2443812375479849506263799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13033666002559197366740261 2443812375479849506263799)
          ·
            refine ⟨3665718563219774259395699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443812375479849506263799 3665718563219774259395699)
            ·
              refine ⟨5498577844829661389093549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665718563219774259395699 5498577844829661389093549)
              ·
                refine ⟨2061966691811123020910081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5498577844829661389093549 2061966691811123020910081)
                ·
                  refine ⟨1546475018858342265682561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2061966691811123020910081 1546475018858342265682561)
                  ·
                    refine ⟨1159856264143756699261921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1546475018858342265682561 1159856264143756699261921)
                    ·
                      refine ⟨869892198107817524446441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159856264143756699261921 869892198107817524446441)
                      ·
                        rfl

theorem cell23_1694109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_1694109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694109 prefixEnd_1694109 := by exact prefixLift 1694109
  have htrace : WordTrace (prefixWord ++ tailWord_1694109) baseStart_1694109 baseEnd_1694109 := by
    simpa [prefixWord, tailWord_1694109, baseEnd_1694109] using wordTrace_append hprefix tailTrace_1694109
  have hstable : (prefixWord ++ tailWord_1694109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694109).length < 2 ^ (prefixWord ++ tailWord_1694109).sum := by decide
  have hdescent : baseEnd_1694109 < baseStart_1694109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694165 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_1694165 : Nat := 118140960795 + 1694165 * 2 ^ 59
def prefixEnd_1694165 : Nat := 4983230072969 + 3 ^ 40 * 1694165 * 2
def baseEnd_1694165 : Nat := 869920953024469305346183

theorem tailTrace_1694165 : CollatzResearch.WordTrace tailWord_1694165 prefixEnd_1694165 869920953024469305346183 := by
  unfold tailWord_1694165
  simp only [CollatzResearch.WordTrace]
  refine ⟨61791273907337020191547949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41194182604891346794365299 61791273907337020191547949)
  ·
    refine ⟨23171727715251382571830481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61791273907337020191547949 23171727715251382571830481)
    ·
      refine ⟨17378795786438536928872861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23171727715251382571830481 17378795786438536928872861)
      ·
        refine ⟨6517048419914451348327323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17378795786438536928872861 6517048419914451348327323)
        ·
          refine ⟨9775572629871677022490985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6517048419914451348327323 9775572629871677022490985)
          ·
            refine ⟨7331679472403757766868239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9775572629871677022490985 7331679472403757766868239)
            ·
              refine ⟨10997519208605636650302359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331679472403757766868239 10997519208605636650302359)
              ·
                refine ⟨16496278812908454975453539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10997519208605636650302359 16496278812908454975453539)
                ·
                  refine ⟨24744418219362682463180309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16496278812908454975453539 24744418219362682463180309)
                  ·
                    refine ⟨1159894604032625740461577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24744418219362682463180309 1159894604032625740461577)
                    ·
                      refine ⟨869920953024469305346183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159894604032625740461577 869920953024469305346183)
                      ·
                        rfl

theorem cell23_1694165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_1694165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694165 prefixEnd_1694165 := by exact prefixLift 1694165
  have htrace : WordTrace (prefixWord ++ tailWord_1694165) baseStart_1694165 baseEnd_1694165 := by
    simpa [prefixWord, tailWord_1694165, baseEnd_1694165] using wordTrace_append hprefix tailTrace_1694165
  have hstable : (prefixWord ++ tailWord_1694165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694165).length < 2 ^ (prefixWord ++ tailWord_1694165).sum := by decide
  have hdescent : baseEnd_1694165 < baseStart_1694165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694168 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_1694168 : Nat := 118140960795 + 1694168 * 2 ^ 59
def prefixEnd_1694168 : Nat := 4983230072969 + 3 ^ 40 * 1694168 * 2
def baseEnd_1694168 : Nat := 869922493466432793608669

theorem tailTrace_1694168 : CollatzResearch.WordTrace tailWord_1694168 prefixEnd_1694168 869922493466432793608669 := by
  unfold tailWord_1694168
  simp only [CollatzResearch.WordTrace]
  refine ⟨30895691663163075851953579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41194255550884101135938105 30895691663163075851953579)
  ·
    refine ⟨46343537494744613777930369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30895691663163075851953579 46343537494744613777930369)
    ·
      refine ⟨34757653121058460333447777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46343537494744613777930369 34757653121058460333447777)
      ·
        refine ⟨26068239840793845250085833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34757653121058460333447777 26068239840793845250085833)
        ·
          refine ⟨19551179880595383937564375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26068239840793845250085833 19551179880595383937564375)
          ·
            refine ⟨29326769820893075906346563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19551179880595383937564375 29326769820893075906346563)
            ·
              refine ⟨43990154731339613859519845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29326769820893075906346563 43990154731339613859519845)
              ·
                refine ⟨8248154012126177598659971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43990154731339613859519845 8248154012126177598659971)
                ·
                  refine ⟨12372231018189266397989957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8248154012126177598659971 12372231018189266397989957)
                  ·
                    refine ⟨2319793315910487449623117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12372231018189266397989957 2319793315910487449623117)
                    ·
                      refine ⟨869922493466432793608669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2319793315910487449623117 869922493466432793608669)
                      ·
                        rfl

theorem cell23_1694168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1694168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694168 prefixEnd_1694168 := by exact prefixLift 1694168
  have htrace : WordTrace (prefixWord ++ tailWord_1694168) baseStart_1694168 baseEnd_1694168 := by
    simpa [prefixWord, tailWord_1694168, baseEnd_1694168] using wordTrace_append hprefix tailTrace_1694168
  have hstable : (prefixWord ++ tailWord_1694168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694168).length < 2 ^ (prefixWord ++ tailWord_1694168).sum := by decide
  have hdescent : baseEnd_1694168 < baseStart_1694168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694175 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 3, 4]
def baseStart_1694175 : Nat := 118140960795 + 1694175 * 2 ^ 59
def prefixEnd_1694175 : Nat := 4983230072969 + 3 ^ 40 * 1694175 * 2
def baseEnd_1694175 : Nat := 289975362610338088740379

theorem tailTrace_1694175 : CollatzResearch.WordTrace tailWord_1694175 prefixEnd_1694175 289975362610338088740379 := by
  unfold tailWord_1694175
  simp only [CollatzResearch.WordTrace]
  refine ⟨61791638637300791899411979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41194425758200527932941319 61791638637300791899411979)
  ·
    refine ⟨92687457955951187849117969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61791638637300791899411979 92687457955951187849117969)
    ·
      refine ⟨69515593466963390886838477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92687457955951187849117969 69515593466963390886838477)
      ·
        refine ⟨26068347550111271582564429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69515593466963390886838477 26068347550111271582564429)
        ·
          refine ⟨9775630331291726843461661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26068347550111271582564429 9775630331291726843461661)
          ·
            refine ⟨3665861374234397566298123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9775630331291726843461661 3665861374234397566298123)
            ·
              refine ⟨5498792061351596349447185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665861374234397566298123 5498792061351596349447185)
              ·
                refine ⟨4124094046013697262085389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498792061351596349447185 4124094046013697262085389)
                ·
                  refine ⟨1546535267255136473282021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4124094046013697262085389 1546535267255136473282021)
                  ·
                    refine ⟨289975362610338088740379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1546535267255136473282021 289975362610338088740379)
                    ·
                      rfl

theorem cell23_1694175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 4].length) (baseStart_1694175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694175 prefixEnd_1694175 := by exact prefixLift 1694175
  have htrace : WordTrace (prefixWord ++ tailWord_1694175) baseStart_1694175 baseEnd_1694175 := by
    simpa [prefixWord, tailWord_1694175, baseEnd_1694175] using wordTrace_append hprefix tailTrace_1694175
  have hstable : (prefixWord ++ tailWord_1694175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694175).length < 2 ^ (prefixWord ++ tailWord_1694175).sum := by decide
  have hdescent : baseEnd_1694175 < baseStart_1694175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694192 : List Nat := [2, 1, 1, 1, 3, 3, 4, 3, 1, 4]
def baseStart_1694192 : Nat := 118140960795 + 1694192 * 2 ^ 59
def prefixEnd_1694192 : Nat := 4983230072969 + 3 ^ 40 * 1694192 * 2
def baseEnd_1694192 : Nat := 289978272334046899902853

theorem tailTrace_1694192 : CollatzResearch.WordTrace tailWord_1694192 prefixEnd_1694192 289978272334046899902853 := by
  unfold tailWord_1694192
  simp only [CollatzResearch.WordTrace]
  refine ⟨30896129339119601901390415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41194839118826135868520553 30896129339119601901390415)
  ·
    refine ⟨46344194008679402852085623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30896129339119601901390415 46344194008679402852085623)
    ·
      refine ⟨69516291013019104278128435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46344194008679402852085623 69516291013019104278128435)
      ·
        refine ⟨104274436519528656417192653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69516291013019104278128435 104274436519528656417192653)
        ·
          refine ⟨39102913694823246156447245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104274436519528656417192653 39102913694823246156447245)
          ·
            refine ⟨14663592635558717308667717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39102913694823246156447245 14663592635558717308667717)
            ·
              refine ⟨2749423619167259495375197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14663592635558717308667717 2749423619167259495375197)
              ·
                refine ⟨1031033857187722310765699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2749423619167259495375197 1031033857187722310765699)
                ·
                  refine ⟨1546550785781583466148549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031033857187722310765699 1546550785781583466148549)
                  ·
                    refine ⟨289978272334046899902853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1546550785781583466148549 289978272334046899902853)
                    ·
                      rfl

theorem cell23_1694192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 4].length) (baseStart_1694192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694192 prefixEnd_1694192 := by exact prefixLift 1694192
  have htrace : WordTrace (prefixWord ++ tailWord_1694192) baseStart_1694192 baseEnd_1694192 := by
    simpa [prefixWord, tailWord_1694192, baseEnd_1694192] using wordTrace_append hprefix tailTrace_1694192
  have hstable : (prefixWord ++ tailWord_1694192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694192).length < 2 ^ (prefixWord ++ tailWord_1694192).sum := by decide
  have hdescent : baseEnd_1694192 < baseStart_1694192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694222 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_1694222 : Nat := 118140960795 + 1694222 * 2 ^ 59
def prefixEnd_1694222 : Nat := 4983230072969 + 3 ^ 40 * 1694222 * 2
def baseEnd_1694222 : Nat := 96661135713530620259269

theorem tailTrace_1694222 : CollatzResearch.WordTrace tailWord_1694222 prefixEnd_1694222 96661135713530620259269 := by
  unfold tailWord_1694222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7724169108516314865796615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41195568578753679284248613 7724169108516314865796615)
  ·
    refine ⟨11586253662774472298694923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7724169108516314865796615 11586253662774472298694923)
    ·
      refine ⟨17379380494161708448042385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11586253662774472298694923 17379380494161708448042385)
      ·
        refine ⟨13034535370621281336031789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17379380494161708448042385 13034535370621281336031789)
        ·
          refine ⟨4887950763982980501011921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13034535370621281336031789 4887950763982980501011921)
          ·
            refine ⟨3665963072987235375758941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4887950763982980501011921 3665963072987235375758941)
            ·
              refine ⟨1374736152370213265909603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3665963072987235375758941 1374736152370213265909603)
              ·
                refine ⟨2062104228555319898864405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374736152370213265909603 2062104228555319898864405)
                ·
                  refine ⟨96661135713530620259269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2062104228555319898864405 96661135713530620259269)
                  ·
                    rfl

theorem cell23_1694222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_1694222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694222 prefixEnd_1694222 := by exact prefixLift 1694222
  have htrace : WordTrace (prefixWord ++ tailWord_1694222) baseStart_1694222 baseEnd_1694222 := by
    simpa [prefixWord, tailWord_1694222, baseEnd_1694222] using wordTrace_append hprefix tailTrace_1694222
  have hstable : (prefixWord ++ tailWord_1694222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694222).length < 2 ^ (prefixWord ++ tailWord_1694222).sum := by decide
  have hdescent : baseEnd_1694222 < baseStart_1694222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694225 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 6, 3, 2]
def baseStart_1694225 : Nat := 118140960795 + 1694225 * 2 ^ 59
def prefixEnd_1694225 : Nat := 4983230072969 + 3 ^ 40 * 1694225 * 2
def baseEnd_1694225 : Nat := 869951761863739070595907

theorem tailTrace_1694225 : CollatzResearch.WordTrace tailWord_1694225 prefixEnd_1694225 869951761863739070595907 := by
  unfold tailWord_1694225
  simp only [CollatzResearch.WordTrace]
  refine ⟨61793462287119650438732129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41195641524746433625821419 61793462287119650438732129)
  ·
    refine ⟨46345096715339737829049097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61793462287119650438732129 46345096715339737829049097)
    ·
      refine ⟨34758822536504803371786823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46345096715339737829049097 34758822536504803371786823)
      ·
        refine ⟨52138233804757205057680235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34758822536504803371786823 52138233804757205057680235)
        ·
          refine ⟨78207350707135807586520353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52138233804757205057680235 78207350707135807586520353)
          ·
            refine ⟨58655513030351855689890265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78207350707135807586520353 58655513030351855689890265)
            ·
              refine ⟨43991634772763891767417699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58655513030351855689890265 43991634772763891767417699)
              ·
                refine ⟨65987452159145837651126549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43991634772763891767417699 65987452159145837651126549)
                ·
                  refine ⟨3093161819959961139896557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65987452159145837651126549 3093161819959961139896557)
                  ·
                    refine ⟨1159935682484985427461209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3093161819959961139896557 1159935682484985427461209)
                    ·
                      refine ⟨869951761863739070595907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159935682484985427461209 869951761863739070595907)
                      ·
                        rfl

theorem cell23_1694225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_1694225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694225 prefixEnd_1694225 := by exact prefixLift 1694225
  have htrace : WordTrace (prefixWord ++ tailWord_1694225) baseStart_1694225 baseEnd_1694225 := by
    simpa [prefixWord, tailWord_1694225, baseEnd_1694225] using wordTrace_append hprefix tailTrace_1694225
  have hstable : (prefixWord ++ tailWord_1694225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694225).length < 2 ^ (prefixWord ++ tailWord_1694225).sum := by decide
  have hdescent : baseEnd_1694225 < baseStart_1694225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694232 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1694232 : Nat := 118140960795 + 1694232 * 2 ^ 59
def prefixEnd_1694232 : Nat := 4983230072969 + 3 ^ 40 * 1694232 * 2
def baseEnd_1694232 : Nat := 869955356228320543208375

theorem tailTrace_1694232 : CollatzResearch.WordTrace tailWord_1694232 prefixEnd_1694232 869955356228320543208375 := by
  unfold tailWord_1694232
  simp only [CollatzResearch.WordTrace]
  refine ⟨30896858799047145317118475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41195811732062860422824633 30896858799047145317118475)
  ·
    refine ⟨46345288198570717975677713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30896858799047145317118475 46345288198570717975677713)
    ·
      refine ⟨34758966148928038481758285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46345288198570717975677713 34758966148928038481758285)
      ·
        refine ⟨13034612305848014430659357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34758966148928038481758285 13034612305848014430659357)
        ·
          refine ⟨4887979614693005411497259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13034612305848014430659357 4887979614693005411497259)
          ·
            refine ⟨7331969422039508117245889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887979614693005411497259 7331969422039508117245889)
            ·
              refine ⟨5498977066529631087934417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7331969422039508117245889 5498977066529631087934417)
              ·
                refine ⟨4124232799897223315950813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498977066529631087934417 4124232799897223315950813)
                ·
                  refine ⟨1546587299961458743481555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4124232799897223315950813 1546587299961458743481555)
                  ·
                    refine ⟨2319880949942188115222333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1546587299961458743481555 2319880949942188115222333)
                    ·
                      refine ⟨869955356228320543208375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2319880949942188115222333 869955356228320543208375)
                      ·
                        rfl

theorem cell23_1694232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1694232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694232 prefixEnd_1694232 := by exact prefixLift 1694232
  have htrace : WordTrace (prefixWord ++ tailWord_1694232) baseStart_1694232 baseEnd_1694232 := by
    simpa [prefixWord, tailWord_1694232, baseEnd_1694232] using wordTrace_append hprefix tailTrace_1694232
  have hstable : (prefixWord ++ tailWord_1694232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694232).length < 2 ^ (prefixWord ++ tailWord_1694232).sum := by decide
  have hdescent : baseEnd_1694232 < baseStart_1694232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694242 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_1694242 : Nat := 118140960795 + 1694242 * 2 ^ 59
def prefixEnd_1694242 : Nat := 4983230072969 + 3 ^ 40 * 1694242 * 2
def baseEnd_1694242 : Nat := 869960491034865504083329

theorem tailTrace_1694242 : CollatzResearch.WordTrace tailWord_1694242 prefixEnd_1694242 869960491034865504083329 := by
  unfold tailWord_1694242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15448520582014515585525245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41196054885372041561400653 15448520582014515585525245)
  ·
    refine ⟨5793195218255443344571967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15448520582014515585525245 5793195218255443344571967)
    ·
      refine ⟨8689792827383165016857951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5793195218255443344571967 8689792827383165016857951)
      ·
        refine ⟨13034689241074747525286927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8689792827383165016857951 13034689241074747525286927)
        ·
          refine ⟨19552033861612121287930391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13034689241074747525286927 19552033861612121287930391)
          ·
            refine ⟨29328050792418181931895587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19552033861612121287930391 29328050792418181931895587)
            ·
              refine ⟨43992076188627272897843381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29328050792418181931895587 43992076188627272897843381)
              ·
                refine ⟨4124257142683806834172817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43992076188627272897843381 4124257142683806834172817)
                ·
                  refine ⟨3093192857012855125629613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4124257142683806834172817 3093192857012855125629613)
                  ·
                    refine ⟨1159947321379820672111105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3093192857012855125629613 1159947321379820672111105)
                    ·
                      refine ⟨869960491034865504083329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1159947321379820672111105 869960491034865504083329)
                      ·
                        rfl

theorem cell23_1694242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_1694242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694242 prefixEnd_1694242 := by exact prefixLift 1694242
  have htrace : WordTrace (prefixWord ++ tailWord_1694242) baseStart_1694242 baseEnd_1694242 := by
    simpa [prefixWord, tailWord_1694242, baseEnd_1694242] using wordTrace_append hprefix tailTrace_1694242
  have hstable : (prefixWord ++ tailWord_1694242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694242).length < 2 ^ (prefixWord ++ tailWord_1694242).sum := by decide
  have hdescent : baseEnd_1694242 < baseStart_1694242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694265 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 4, 4]
def baseStart_1694265 : Nat := 118140960795 + 1694265 * 2 ^ 59
def prefixEnd_1694265 : Nat := 4983230072969 + 3 ^ 40 * 1694265 * 2
def baseEnd_1694265 : Nat := 289990767029972971365241

theorem tailTrace_1694265 : CollatzResearch.WordTrace tailWord_1694265 prefixEnd_1694265 289990767029972971365241 := by
  unfold tailWord_1694265
  simp only [CollatzResearch.WordTrace]
  refine ⟨61794921206974737270188249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41196614137983158180125499 61794921206974737270188249)
  ·
    refine ⟨46346190905231052952641187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61794921206974737270188249 46346190905231052952641187)
    ·
      refine ⟨69519286357846579428961781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46346190905231052952641187 69519286357846579428961781)
      ·
        refine ⟨6517433096048116821465167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69519286357846579428961781 6517433096048116821465167)
        ·
          refine ⟨9776149644072175232197751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6517433096048116821465167 9776149644072175232197751)
          ·
            refine ⟨14664224466108262848296627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9776149644072175232197751 14664224466108262848296627)
            ·
              refine ⟨21996336699162394272444941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14664224466108262848296627 21996336699162394272444941)
              ·
                refine ⟨8248626262185897852166853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21996336699162394272444941 8248626262185897852166853)
                ·
                  refine ⟨1546617424159855847281285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8248626262185897852166853 1546617424159855847281285)
                  ·
                    refine ⟨289990767029972971365241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1546617424159855847281285 289990767029972971365241)
                    ·
                      rfl

theorem cell23_1694265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 4].length) (baseStart_1694265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694265 prefixEnd_1694265 := by exact prefixLift 1694265
  have htrace : WordTrace (prefixWord ++ tailWord_1694265) baseStart_1694265 baseEnd_1694265 := by
    simpa [prefixWord, tailWord_1694265, baseEnd_1694265] using wordTrace_append hprefix tailTrace_1694265
  have hstable : (prefixWord ++ tailWord_1694265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694265).length < 2 ^ (prefixWord ++ tailWord_1694265).sum := by decide
  have hdescent : baseEnd_1694265 < baseStart_1694265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694266 : List Nat := [3, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3]
def baseStart_1694266 : Nat := 118140960795 + 1694266 * 2 ^ 59
def prefixEnd_1694266 : Nat := 4983230072969 + 3 ^ 40 * 1694266 * 2
def baseEnd_1694266 : Nat := 869972814570573410183219

theorem tailTrace_1694266 : CollatzResearch.WordTrace tailWord_1694266 prefixEnd_1694266 869972814570573410183219 := by
  unfold tailWord_1694266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15448739419992778610243663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41196638453314076293983101 15448739419992778610243663)
  ·
    refine ⟨23173109129989167915365495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15448739419992778610243663 23173109129989167915365495)
    ·
      refine ⟨34759663694983751873048243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23173109129989167915365495 34759663694983751873048243)
      ·
        refine ⟨52139495542475627809572365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34759663694983751873048243 52139495542475627809572365)
        ·
          refine ⟨19552310828428360428589637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52139495542475627809572365 19552310828428360428589637)
          ·
            refine ⟨3666058280330317580360557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19552310828428360428589637 3666058280330317580360557)
            ·
              refine ⟨1374771855123869092635209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3666058280330317580360557 1374771855123869092635209)
              ·
                refine ⟨1031078891342901819476407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374771855123869092635209 1031078891342901819476407)
                ·
                  refine ⟨1546618337014352729214611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031078891342901819476407 1546618337014352729214611)
                  ·
                    refine ⟨2319927505521529093821917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1546618337014352729214611 2319927505521529093821917)
                    ·
                      refine ⟨869972814570573410183219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2319927505521529093821917 869972814570573410183219)
                      ·
                        rfl

theorem cell23_1694266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3].length) (baseStart_1694266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694266 prefixEnd_1694266 := by exact prefixLift 1694266
  have htrace : WordTrace (prefixWord ++ tailWord_1694266) baseStart_1694266 baseEnd_1694266 := by
    simpa [prefixWord, tailWord_1694266, baseEnd_1694266] using wordTrace_append hprefix tailTrace_1694266
  have hstable : (prefixWord ++ tailWord_1694266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694266).length < 2 ^ (prefixWord ++ tailWord_1694266).sum := by decide
  have hdescent : baseEnd_1694266 < baseStart_1694266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694282 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_1694282 : Nat := 118140960795 + 1694282 * 2 ^ 59
def prefixEnd_1694282 : Nat := 4983230072969 + 3 ^ 40 * 1694282 * 2
def baseEnd_1694282 : Nat := 289993676753681782527715

theorem tailTrace_1694282 : CollatzResearch.WordTrace tailWord_1694282 prefixEnd_1694282 289993676753681782527715 := by
  unfold tailWord_1694282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15448885311978287293389275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41197027498608766115704733 15448885311978287293389275)
  ·
    refine ⟨23173327967967430940083913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15448885311978287293389275 23173327967967430940083913)
    ·
      refine ⟨17379995975975573205062935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23173327967967430940083913 17379995975975573205062935)
      ·
        refine ⟨26069993963963359807594403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17379995975975573205062935 26069993963963359807594403)
        ·
          refine ⟨39104990945945039711391605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26069993963963359807594403 39104990945945039711391605)
          ·
            refine ⟨3666092901182347472942963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39104990945945039711391605 3666092901182347472942963)
            ·
              refine ⟨5499139351773521209414445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666092901182347472942963 5499139351773521209414445)
              ·
                refine ⟨2062177256915070453530417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5499139351773521209414445 2062177256915070453530417)
                ·
                  refine ⟨1546632942686302840147813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2062177256915070453530417 1546632942686302840147813)
                  ·
                    refine ⟨289993676753681782527715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1546632942686302840147813 289993676753681782527715)
                    ·
                      rfl

theorem cell23_1694282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_1694282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694282 prefixEnd_1694282 := by exact prefixLift 1694282
  have htrace : WordTrace (prefixWord ++ tailWord_1694282) baseStart_1694282 baseEnd_1694282 := by
    simpa [prefixWord, tailWord_1694282, baseEnd_1694282] using wordTrace_append hprefix tailTrace_1694282
  have hstable : (prefixWord ++ tailWord_1694282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694282).length < 2 ^ (prefixWord ++ tailWord_1694282).sum := by decide
  have hdescent : baseEnd_1694282 < baseStart_1694282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694292 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1694292 : Nat := 118140960795 + 1694292 * 2 ^ 59
def prefixEnd_1694292 : Nat := 4983230072969 + 3 ^ 40 * 1694292 * 2
def baseEnd_1694292 : Nat := 869986165067590308458099

theorem tailTrace_1694292 : CollatzResearch.WordTrace tailWord_1694292 prefixEnd_1694292 869986165067590308458099 := by
  unfold tailWord_1694292
  simp only [CollatzResearch.WordTrace]
  refine ⟨30897952988938460440710565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41197270651917947254280753 30897952988938460440710565)
  ·
    refine ⟨5793366185425961332633231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30897952988938460440710565 5793366185425961332633231)
    ·
      refine ⟨8690049278138941998949847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5793366185425961332633231 8690049278138941998949847)
      ·
        refine ⟨13035073917208412998424771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8690049278138941998949847 13035073917208412998424771)
        ·
          refine ⟨19552610875812619497637157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13035073917208412998424771 19552610875812619497637157)
          ·
            refine ⟨3666114539214866155806967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19552610875812619497637157 3666114539214866155806967)
            ·
              refine ⟨5499171808822299233710451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666114539214866155806967 5499171808822299233710451)
              ·
                refine ⟨8248757713233448850565677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5499171808822299233710451 8248757713233448850565677)
                ·
                  refine ⟨3093284142462543318962129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8248757713233448850565677 3093284142462543318962129)
                  ·
                    refine ⟨2319963106846907489221597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3093284142462543318962129 2319963106846907489221597)
                    ·
                      refine ⟨869986165067590308458099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2319963106846907489221597 869986165067590308458099)
                      ·
                        rfl

theorem cell23_1694292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1694292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694292 prefixEnd_1694292 := by exact prefixLift 1694292
  have htrace : WordTrace (prefixWord ++ tailWord_1694292) baseStart_1694292 baseEnd_1694292 := by
    simpa [prefixWord, tailWord_1694292, baseEnd_1694292] using wordTrace_append hprefix tailTrace_1694292
  have hstable : (prefixWord ++ tailWord_1694292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694292).length < 2 ^ (prefixWord ++ tailWord_1694292).sum := by decide
  have hdescent : baseEnd_1694292 < baseStart_1694292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694305 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_1694305 : Nat := 118140960795 + 1694305 * 2 ^ 59
def prefixEnd_1694305 : Nat := 4983230072969 + 3 ^ 40 * 1694305 * 2
def baseEnd_1694305 : Nat := 869992840316098757595539

theorem tailTrace_1694305 : CollatzResearch.WordTrace tailWord_1694305 prefixEnd_1694305 869992840316098757595539 := by
  unfold tailWord_1694305
  simp only [CollatzResearch.WordTrace]
  refine ⟨61796380126829824101644369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41197586751219882734429579 61796380126829824101644369)
  ·
    refine ⟨46347285095122368076233277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61796380126829824101644369 46347285095122368076233277)
    ·
      refine ⟨17380231910670888028587479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46347285095122368076233277 17380231910670888028587479)
      ·
        refine ⟨26070347866006332042881219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17380231910670888028587479 26070347866006332042881219)
        ·
          refine ⟨39105521799009498064321829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26070347866006332042881219 39105521799009498064321829)
          ·
            refine ⟨7332285337314280887060343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39105521799009498064321829 7332285337314280887060343)
            ·
              refine ⟨10998428005971421330590515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7332285337314280887060343 10998428005971421330590515)
              ·
                refine ⟨16497642008957131995885773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10998428005971421330590515 16497642008957131995885773)
                ·
                  refine ⟨6186615753358924498457165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16497642008957131995885773 6186615753358924498457165)
                  ·
                    refine ⟨2319980907509596686921437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6186615753358924498457165 2319980907509596686921437)
                    ·
                      refine ⟨869992840316098757595539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2319980907509596686921437 869992840316098757595539)
                      ·
                        rfl

theorem cell23_1694305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_1694305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694305 prefixEnd_1694305 := by exact prefixLift 1694305
  have htrace : WordTrace (prefixWord ++ tailWord_1694305) baseStart_1694305 baseEnd_1694305 := by
    simpa [prefixWord, tailWord_1694305, baseEnd_1694305] using wordTrace_append hprefix tailTrace_1694305
  have hstable : (prefixWord ++ tailWord_1694305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694305).length < 2 ^ (prefixWord ++ tailWord_1694305).sum := by decide
  have hdescent : baseEnd_1694305 < baseStart_1694305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694309 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 1, 1, 5]
def baseStart_1694309 : Nat := 118140960795 + 1694309 * 2 ^ 59
def prefixEnd_1694309 : Nat := 4983230072969 + 3 ^ 40 * 1694309 * 2
def baseEnd_1694309 : Nat := 869994894238716741945521

theorem tailTrace_1694309 : CollatzResearch.WordTrace tailWord_1694309 prefixEnd_1694309 869994894238716741945521 := by
  unfold tailWord_1694309
  simp only [CollatzResearch.WordTrace]
  refine ⟨61796526018815332784789981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41197684012543555189859987 61796526018815332784789981)
  ·
    refine ⟨23173697257055749794296243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61796526018815332784789981 23173697257055749794296243)
    ·
      refine ⟨34760545885583624691444365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23173697257055749794296243 34760545885583624691444365)
      ·
        refine ⟨13035204707093859259291637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34760545885583624691444365 13035204707093859259291637)
        ·
          refine ⟨1222050441290049305558591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13035204707093859259291637 1222050441290049305558591)
          ·
            refine ⟨1833075661935073958337887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222050441290049305558591 1833075661935073958337887)
            ·
              refine ⟨2749613492902610937506831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833075661935073958337887 2749613492902610937506831)
              ·
                refine ⟨4124420239353916406260247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749613492902610937506831 4124420239353916406260247)
                ·
                  refine ⟨6186630359030874609390371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124420239353916406260247 6186630359030874609390371)
                  ·
                    refine ⟨9279945538546311914085557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6186630359030874609390371 9279945538546311914085557)
                    ·
                      refine ⟨869994894238716741945521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9279945538546311914085557 869994894238716741945521)
                      ·
                        rfl

theorem cell23_1694309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_1694309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694309 prefixEnd_1694309 := by exact prefixLift 1694309
  have htrace : WordTrace (prefixWord ++ tailWord_1694309) baseStart_1694309 baseEnd_1694309 := by
    simpa [prefixWord, tailWord_1694309, baseEnd_1694309] using wordTrace_append hprefix tailTrace_1694309
  have hstable : (prefixWord ++ tailWord_1694309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694309).length < 2 ^ (prefixWord ++ tailWord_1694309).sum := by decide
  have hdescent : baseEnd_1694309 < baseStart_1694309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694332 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_1694332 : Nat := 118140960795 + 1694332 * 2 ^ 59
def prefixEnd_1694332 : Nat := 4983230072969 + 3 ^ 40 * 1694332 * 2
def baseEnd_1694332 : Nat := 870006704293770151957915

theorem tailTrace_1694332 : CollatzResearch.WordTrace tailWord_1694332 prefixEnd_1694332 870006704293770151957915 := by
  unfold tailWord_1694332
  simp only [CollatzResearch.WordTrace]
  refine ⟨30898682448866003856438625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41198243265154671808584833 30898682448866003856438625)
  ·
    refine ⟨23174011836649502892328969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30898682448866003856438625 23174011836649502892328969)
    ·
      refine ⟨17380508877487127169246727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23174011836649502892328969 17380508877487127169246727)
      ·
        refine ⟨26070763316230690753870091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17380508877487127169246727 26070763316230690753870091)
        ·
          refine ⟨39106144974346036130805137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26070763316230690753870091 39106144974346036130805137)
          ·
            refine ⟨29329608730759527098103853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39106144974346036130805137 29329608730759527098103853)
            ·
              refine ⟨10998603274034822661788945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29329608730759527098103853 10998603274034822661788945)
              ·
                refine ⟨8248952455526116996341709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10998603274034822661788945 8248952455526116996341709)
                ·
                  refine ⟨3093357170822293873628141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8248952455526116996341709 3093357170822293873628141)
                  ·
                    refine ⟨1160008939058360202610553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3093357170822293873628141 1160008939058360202610553)
                    ·
                      refine ⟨870006704293770151957915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160008939058360202610553 870006704293770151957915)
                      ·
                        rfl

theorem cell23_1694332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_1694332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694332 prefixEnd_1694332 := by exact prefixLift 1694332
  have htrace : WordTrace (prefixWord ++ tailWord_1694332) baseStart_1694332 baseEnd_1694332 := by
    simpa [prefixWord, tailWord_1694332, baseEnd_1694332] using wordTrace_append hprefix tailTrace_1694332
  have hstable : (prefixWord ++ tailWord_1694332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694332).length < 2 ^ (prefixWord ++ tailWord_1694332).sum := by decide
  have hdescent : baseEnd_1694332 < baseStart_1694332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694365 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1694365 : Nat := 118140960795 + 1694365 * 2 ^ 59
def prefixEnd_1694365 : Nat := 4983230072969 + 3 ^ 40 * 1694365 * 2
def baseEnd_1694365 : Nat := 870023649155368522845263

theorem tailTrace_1694365 : CollatzResearch.WordTrace tailWord_1694365 prefixEnd_1694365 870023649155368522845263 := by
  unfold tailWord_1694365
  simp only [CollatzResearch.WordTrace]
  refine ⟨61798568506612454348828549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41199045671074969565885699 61798568506612454348828549)
  ·
    refine ⟨11587231594989835190405353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61798568506612454348828549 11587231594989835190405353)
    ·
      refine ⟨8690423696242376392804015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11587231594989835190405353 8690423696242376392804015)
      ·
        refine ⟨13035635544363564589206023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8690423696242376392804015 13035635544363564589206023)
        ·
          refine ⟨19553453316545346883809035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13035635544363564589206023 19553453316545346883809035)
          ·
            refine ⟨29330179974818020325713553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19553453316545346883809035 29330179974818020325713553)
            ·
              refine ⟨21997634981113515244285165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29330179974818020325713553 21997634981113515244285165)
              ·
                refine ⟨8249113117917568216606937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21997634981113515244285165 8249113117917568216606937)
                ·
                  refine ⟨6186834838438176162455203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8249113117917568216606937 6186834838438176162455203)
                  ·
                    refine ⟨9280252257657264243682805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6186834838438176162455203 9280252257657264243682805)
                    ·
                      refine ⟨870023649155368522845263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9280252257657264243682805 870023649155368522845263)
                      ·
                        rfl

theorem cell23_1694365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1694365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694365 prefixEnd_1694365 := by exact prefixLift 1694365
  have htrace : WordTrace (prefixWord ++ tailWord_1694365) baseStart_1694365 baseEnd_1694365 := by
    simpa [prefixWord, tailWord_1694365, baseEnd_1694365] using wordTrace_append hprefix tailTrace_1694365
  have hstable : (prefixWord ++ tailWord_1694365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694365).length < 2 ^ (prefixWord ++ tailWord_1694365).sum := by decide
  have hdescent : baseEnd_1694365 < baseStart_1694365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694366 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_1694366 : Nat := 118140960795 + 1694366 * 2 ^ 59
def prefixEnd_1694366 : Nat := 4983230072969 + 3 ^ 40 * 1694366 * 2
def baseEnd_1694366 : Nat := 870024162636023018932759

theorem tailTrace_1694366 : CollatzResearch.WordTrace tailWord_1694366 prefixEnd_1694366 870024162636023018932759 := by
  unfold tailWord_1694366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7724825622451103939951869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41199069986405887679743301 7724825622451103939951869)
  ·
    refine ⟨2896809608419163977481951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7724825622451103939951869 2896809608419163977481951)
    ·
      refine ⟨4345214412628745966222927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2896809608419163977481951 4345214412628745966222927)
      ·
        refine ⟨6517821618943118949334391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4345214412628745966222927 6517821618943118949334391)
        ·
          refine ⟨9776732428414678424001587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6517821618943118949334391 9776732428414678424001587)
          ·
            refine ⟨14665098642622017636002381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9776732428414678424001587 14665098642622017636002381)
            ·
              refine ⟨5499411990983256613500893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14665098642622017636002381 5499411990983256613500893)
              ·
                refine ⟨2062279496618721230062835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5499411990983256613500893 2062279496618721230062835)
                ·
                  refine ⟨3093419244928081845094253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062279496618721230062835 3093419244928081845094253)
                  ·
                    refine ⟨1160032216848030691910345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3093419244928081845094253 1160032216848030691910345)
                    ·
                      refine ⟨870024162636023018932759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160032216848030691910345 870024162636023018932759)
                      ·
                        rfl

theorem cell23_1694366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_1694366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694366 prefixEnd_1694366 := by exact prefixLift 1694366
  have htrace : WordTrace (prefixWord ++ tailWord_1694366) baseStart_1694366 baseEnd_1694366 := by
    simpa [prefixWord, tailWord_1694366, baseEnd_1694366] using wordTrace_append hprefix tailTrace_1694366
  have hstable : (prefixWord ++ tailWord_1694366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694366).length < 2 ^ (prefixWord ++ tailWord_1694366).sum := by decide
  have hdescent : baseEnd_1694366 < baseStart_1694366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694390 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_1694390 : Nat := 118140960795 + 1694390 * 2 ^ 59
def prefixEnd_1694390 : Nat := 4983230072969 + 3 ^ 40 * 1694390 * 2
def baseEnd_1694390 : Nat := 870036486171730925032649

theorem tailTrace_1694390 : CollatzResearch.WordTrace tailWord_1694390 prefixEnd_1694390 870036486171730925032649 := by
  unfold tailWord_1694390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3862467520720117726155539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41199653554347922412325749 3862467520720117726155539)
  ·
    refine ⟨5793701281080176589233309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3862467520720117726155539 5793701281080176589233309)
    ·
      refine ⟨2172637980405066220962491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5793701281080176589233309 2172637980405066220962491)
      ·
        refine ⟨3258956970607599331443737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2172637980405066220962491 3258956970607599331443737)
        ·
          refine ⟨2444217727955699498582803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3258956970607599331443737 2444217727955699498582803)
          ·
            refine ⟨3666326591933549247874205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444217727955699498582803 3666326591933549247874205)
            ·
              refine ⟨1374872471975080967952827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3666326591933549247874205 1374872471975080967952827)
              ·
                refine ⟨2062308707962621451929241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374872471975080967952827 2062308707962621451929241)
                ·
                  refine ⟨1546731530971966088946931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2062308707962621451929241 1546731530971966088946931)
                  ·
                    refine ⟨2320097296457949133420397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1546731530971966088946931 2320097296457949133420397)
                    ·
                      refine ⟨870036486171730925032649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2320097296457949133420397 870036486171730925032649)
                      ·
                        rfl

theorem cell23_1694390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_1694390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694390 prefixEnd_1694390 := by exact prefixLift 1694390
  have htrace : WordTrace (prefixWord ++ tailWord_1694390) baseStart_1694390 baseEnd_1694390 := by
    simpa [prefixWord, tailWord_1694390, baseEnd_1694390] using wordTrace_append hprefix tailTrace_1694390
  have hstable : (prefixWord ++ tailWord_1694390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694390).length < 2 ^ (prefixWord ++ tailWord_1694390).sum := by decide
  have hdescent : baseEnd_1694390 < baseStart_1694390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694425 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_1694425 : Nat := 118140960795 + 1694425 * 2 ^ 59
def prefixEnd_1694425 : Nat := 4983230072969 + 3 ^ 40 * 1694425 * 2
def baseEnd_1694425 : Nat := 870054457994638288094987

theorem tailTrace_1694425 : CollatzResearch.WordTrace tailWord_1694425 prefixEnd_1694425 870054457994638288094987 := by
  unfold tailWord_1694425
  simp only [CollatzResearch.WordTrace]
  refine ⟨61800756886395084596012729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41200504590930056397341819 61800756886395084596012729)
  ·
    refine ⟨46350567664796313447009547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61800756886395084596012729 46350567664796313447009547)
    ·
      refine ⟨69525851497194470170514321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46350567664796313447009547 69525851497194470170514321)
      ·
        refine ⟨52144388622895852627885741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69525851497194470170514321 52144388622895852627885741)
        ·
          refine ⟨19554145733585944735457153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52144388622895852627885741 19554145733585944735457153)
          ·
            refine ⟨14665609300189458551592865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19554145733585944735457153 14665609300189458551592865)
            ·
              refine ⟨10999206975142093913694649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14665609300189458551592865 10999206975142093913694649)
              ·
                refine ⟨8249405231356570435270987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10999206975142093913694649 8249405231356570435270987)
                ·
                  refine ⟨12374107847034855652906481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8249405231356570435270987 12374107847034855652906481)
                  ·
                    refine ⟨9280580885276141739679861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12374107847034855652906481 9280580885276141739679861)
                    ·
                      refine ⟨870054457994638288094987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9280580885276141739679861 870054457994638288094987)
                      ·
                        rfl

theorem cell23_1694425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_1694425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694425 prefixEnd_1694425 := by exact prefixLift 1694425
  have htrace : WordTrace (prefixWord ++ tailWord_1694425) baseStart_1694425 baseEnd_1694425 := by
    simpa [prefixWord, tailWord_1694425, baseEnd_1694425] using wordTrace_append hprefix tailTrace_1694425
  have hstable : (prefixWord ++ tailWord_1694425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694425).length < 2 ^ (prefixWord ++ tailWord_1694425).sum := by decide
  have hdescent : baseEnd_1694425 < baseStart_1694425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694465 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1694465 : Nat := 118140960795 + 1694465 * 2 ^ 59
def prefixEnd_1694465 : Nat := 4983230072969 + 3 ^ 40 * 1694465 * 2
def baseEnd_1694465 : Nat := 870074997220818131594803

theorem tailTrace_1694465 : CollatzResearch.WordTrace tailWord_1694465 prefixEnd_1694465 870074997220818131594803 := by
  unfold tailWord_1694465
  simp only [CollatzResearch.WordTrace]
  refine ⟨61802215806250171427468849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41201477204166780951645899 61802215806250171427468849)
  ·
    refine ⟨46351661854687628570601637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61802215806250171427468849 46351661854687628570601637)
    ·
      refine ⟨8690936597753930356987807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46351661854687628570601637 8690936597753930356987807)
      ·
        refine ⟨13036404896630895535481711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8690936597753930356987807 13036404896630895535481711)
        ·
          refine ⟨19554607344946343303222567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13036404896630895535481711 19554607344946343303222567)
          ·
            refine ⟨29331911017419514954833851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19554607344946343303222567 29331911017419514954833851)
            ·
              refine ⟨43997866526129272432250777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29331911017419514954833851 43997866526129272432250777)
              ·
                refine ⟨32998399894596954324188083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43997866526129272432250777 32998399894596954324188083)
                ·
                  refine ⟨49497599841895431486282125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32998399894596954324188083 49497599841895431486282125)
                  ·
                    refine ⟨18561599940710786807355797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49497599841895431486282125 18561599940710786807355797)
                    ·
                      refine ⟨870074997220818131594803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18561599940710786807355797 870074997220818131594803)
                      ·
                        rfl

theorem cell23_1694465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1694465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694465 prefixEnd_1694465 := by exact prefixLift 1694465
  have htrace : WordTrace (prefixWord ++ tailWord_1694465) baseStart_1694465 baseEnd_1694465 := by
    simpa [prefixWord, tailWord_1694465, baseEnd_1694465] using wordTrace_append hprefix tailTrace_1694465
  have hstable : (prefixWord ++ tailWord_1694465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694465).length < 2 ^ (prefixWord ++ tailWord_1694465).sum := by decide
  have hdescent : baseEnd_1694465 < baseStart_1694465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694479 : List Nat := [1, 1, 2, 1, 1, 1, 6, 5, 1, 4]
def baseStart_1694479 : Nat := 118140960795 + 1694479 * 2 ^ 59
def prefixEnd_1694479 : Nat := 4983230072969 + 3 ^ 40 * 1694479 * 2
def baseEnd_1694479 : Nat := 290027395316660358939913

theorem tailTrace_1694479 : CollatzResearch.WordTrace tailWord_1694479 prefixEnd_1694479 290027395316660358939913 := by
  unfold tailWord_1694479
  simp only [CollatzResearch.WordTrace]
  refine ⟨61802726428199451818478491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41201817618799634545652327 61802726428199451818478491)
  ·
    refine ⟨92704089642299177727717737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61802726428199451818478491 92704089642299177727717737)
    ·
      refine ⟨69528067231724383295788303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92704089642299177727717737 69528067231724383295788303)
      ·
        refine ⟨104292100847586574943682455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69528067231724383295788303 104292100847586574943682455)
        ·
          refine ⟨156438151271379862415523683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104292100847586574943682455 156438151271379862415523683)
          ·
            refine ⟨234657226907069793623285525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156438151271379862415523683 234657226907069793623285525)
            ·
              refine ⟨10999557511268896576091509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234657226907069793623285525 10999557511268896576091509)
              ·
                refine ⟨1031208516681459054008579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10999557511268896576091509 1031208516681459054008579)
                ·
                  refine ⟨1546812775022188581012869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031208516681459054008579 1546812775022188581012869)
                  ·
                    refine ⟨290027395316660358939913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1546812775022188581012869 290027395316660358939913)
                    ·
                      rfl

theorem cell23_1694479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 4].length) (baseStart_1694479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694479 prefixEnd_1694479 := by exact prefixLift 1694479
  have htrace : WordTrace (prefixWord ++ tailWord_1694479) baseStart_1694479 baseEnd_1694479 := by
    simpa [prefixWord, tailWord_1694479, baseEnd_1694479] using wordTrace_append hprefix tailTrace_1694479
  have hstable : (prefixWord ++ tailWord_1694479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694479).length < 2 ^ (prefixWord ++ tailWord_1694479).sum := by decide
  have hdescent : baseEnd_1694479 < baseStart_1694479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694492 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 6]
def baseStart_1694492 : Nat := 118140960795 + 1694492 * 2 ^ 59
def prefixEnd_1694492 : Nat := 4983230072969 + 3 ^ 40 * 1694492 * 2
def baseEnd_1694492 : Nat := 96676540133165502884131

theorem tailTrace_1694492 : CollatzResearch.WordTrace tailWord_1694492 prefixEnd_1694492 96676540133165502884131 := by
  unfold tailWord_1694492
  simp only [CollatzResearch.WordTrace]
  refine ⟨30901600288576177519350865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41202133718101570025801153 30901600288576177519350865)
  ·
    refine ⟨23176200216432133139513149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30901600288576177519350865 23176200216432133139513149)
    ·
      refine ⟨8691075081162049927317431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23176200216432133139513149 8691075081162049927317431)
      ·
        refine ⟨13036612621743074890976147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8691075081162049927317431 13036612621743074890976147)
        ·
          refine ⟨19554918932614612336464221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13036612621743074890976147 19554918932614612336464221)
          ·
            refine ⟨7333094599730479626174083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19554918932614612336464221 7333094599730479626174083)
            ·
              refine ⟨10999641899595719439261125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7333094599730479626174083 10999641899595719439261125)
              ·
                refine ⟨2062432856174197394861461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10999641899595719439261125 2062432856174197394861461)
                ·
                  refine ⟨96676540133165502884131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2062432856174197394861461 96676540133165502884131)
                  ·
                    rfl

theorem cell23_1694492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_1694492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694492 prefixEnd_1694492 := by exact prefixLift 1694492
  have htrace : WordTrace (prefixWord ++ tailWord_1694492) baseStart_1694492 baseEnd_1694492 := by
    simpa [prefixWord, tailWord_1694492, baseEnd_1694492] using wordTrace_append hprefix tailTrace_1694492
  have hstable : (prefixWord ++ tailWord_1694492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694492).length < 2 ^ (prefixWord ++ tailWord_1694492).sum := by decide
  have hdescent : baseEnd_1694492 < baseStart_1694492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694496 : List Nat := [2, 1, 1, 5, 1, 3, 1, 4, 1, 4]
def baseStart_1694496 : Nat := 118140960795 + 1694496 * 2 ^ 59
def prefixEnd_1694496 : Nat := 4983230072969 + 3 ^ 40 * 1694496 * 2
def baseEnd_1694496 : Nat := 290030305040369170102387

theorem tailTrace_1694496 : CollatzResearch.WordTrace tailWord_1694496 prefixEnd_1694496 290030305040369170102387 := by
  unfold tailWord_1694496
  simp only [CollatzResearch.WordTrace]
  refine ⟨30901673234568931860923671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41202230979425242481231561 30901673234568931860923671)
  ·
    refine ⟨46352509851853397791385507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30901673234568931860923671 46352509851853397791385507)
    ·
      refine ⟨69528764777780096687078261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46352509851853397791385507 69528764777780096687078261)
      ·
        refine ⟨6518321697916884064413587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69528764777780096687078261 6518321697916884064413587)
        ·
          refine ⟨9777482546875326096620381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518321697916884064413587 9777482546875326096620381)
          ·
            refine ⟨3666555955078247286232643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9777482546875326096620381 3666555955078247286232643)
            ·
              refine ⟨5499833932617370929348965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666555955078247286232643 5499833932617370929348965)
              ·
                refine ⟨1031218862365757049252931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5499833932617370929348965 1031218862365757049252931)
                ·
                  refine ⟨1546828293548635573879397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031218862365757049252931 1546828293548635573879397)
                  ·
                    refine ⟨290030305040369170102387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1546828293548635573879397 290030305040369170102387)
                    ·
                      rfl

theorem cell23_1694496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 4].length) (baseStart_1694496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694496 prefixEnd_1694496 := by exact prefixLift 1694496
  have htrace : WordTrace (prefixWord ++ tailWord_1694496) baseStart_1694496 baseEnd_1694496 := by
    simpa [prefixWord, tailWord_1694496, baseEnd_1694496] using wordTrace_append hprefix tailTrace_1694496
  have hstable : (prefixWord ++ tailWord_1694496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694496).length < 2 ^ (prefixWord ++ tailWord_1694496).sum := by decide
  have hdescent : baseEnd_1694496 < baseStart_1694496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694519 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 3]
def baseStart_1694519 : Nat := 118140960795 + 1694519 * 2 ^ 59
def prefixEnd_1694519 : Nat := 4983230072969 + 3 ^ 40 * 1694519 * 2
def baseEnd_1694519 : Nat := 870102725176160920319555

theorem tailTrace_1694519 : CollatzResearch.WordTrace tailWord_1694519 prefixEnd_1694519 870102725176160920319555 := by
  unfold tailWord_1694519
  simp only [CollatzResearch.WordTrace]
  refine ⟨61804185348054538649934611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41202790232036359099956407 61804185348054538649934611)
  ·
    refine ⟨92706278022081807974901917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61804185348054538649934611 92706278022081807974901917)
    ·
      refine ⟨34764854258280677990588219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92706278022081807974901917 34764854258280677990588219)
      ·
        refine ⟨52147281387421016985882329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34764854258280677990588219 52147281387421016985882329)
        ·
          refine ⟨39110461040565762739411747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52147281387421016985882329 39110461040565762739411747)
          ·
            refine ⟨58665691560848644109117621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39110461040565762739411747 58665691560848644109117621)
            ·
              refine ⟨5499908583829560385229777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58665691560848644109117621 5499908583829560385229777)
              ·
                refine ⟨4124931437872170288922333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5499908583829560385229777 4124931437872170288922333)
                ·
                  refine ⟨1546849289202063858345875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4124931437872170288922333 1546849289202063858345875)
                  ·
                    refine ⟨2320273933803095787518813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1546849289202063858345875 2320273933803095787518813)
                    ·
                      refine ⟨870102725176160920319555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2320273933803095787518813 870102725176160920319555)
                      ·
                        rfl

theorem cell23_1694519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_1694519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694519 prefixEnd_1694519 := by exact prefixLift 1694519
  have htrace : WordTrace (prefixWord ++ tailWord_1694519) baseStart_1694519 baseEnd_1694519 := by
    simpa [prefixWord, tailWord_1694519, baseEnd_1694519] using wordTrace_append hprefix tailTrace_1694519
  have hstable : (prefixWord ++ tailWord_1694519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694519).length < 2 ^ (prefixWord ++ tailWord_1694519).sum := by decide
  have hdescent : baseEnd_1694519 < baseStart_1694519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694555 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6]
def baseStart_1694555 : Nat := 118140960795 + 1694555 * 2 ^ 59
def prefixEnd_1694555 : Nat := 4983230072969 + 3 ^ 40 * 1694555 * 2
def baseEnd_1694555 : Nat := 870121210479722779469389

theorem tailTrace_1694555 : CollatzResearch.WordTrace tailWord_1694555 prefixEnd_1694555 870121210479722779469389 := by
  unfold tailWord_1694555
  simp only [CollatzResearch.WordTrace]
  refine ⟨61805498375924116798245119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41203665583949411198830079 61805498375924116798245119)
  ·
    refine ⟨92708247563886175197367679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61805498375924116798245119 92708247563886175197367679)
    ·
      refine ⟨139062371345829262796051519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92708247563886175197367679 139062371345829262796051519)
      ·
        refine ⟨208593557018743894194077279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139062371345829262796051519 208593557018743894194077279)
        ·
          refine ⟨312890335528115841291115919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208593557018743894194077279 312890335528115841291115919)
          ·
            refine ⟨469335503292173761936673879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312890335528115841291115919 469335503292173761936673879)
            ·
              refine ⟨704003254938260642905010819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469335503292173761936673879 704003254938260642905010819)
              ·
                refine ⟨1056004882407390964357516229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704003254938260642905010819 1056004882407390964357516229)
                ·
                  refine ⟨198000915451385805817034293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056004882407390964357516229 198000915451385805817034293)
                  ·
                    refine ⟨18562585823567419295346965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 198000915451385805817034293 18562585823567419295346965)
                    ·
                      refine ⟨870121210479722779469389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18562585823567419295346965 870121210479722779469389)
                      ·
                        rfl

theorem cell23_1694555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_1694555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694555 prefixEnd_1694555 := by exact prefixLift 1694555
  have htrace : WordTrace (prefixWord ++ tailWord_1694555) baseStart_1694555 baseEnd_1694555 := by
    simpa [prefixWord, tailWord_1694555, baseEnd_1694555] using wordTrace_append hprefix tailTrace_1694555
  have hstable : (prefixWord ++ tailWord_1694555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694555).length < 2 ^ (prefixWord ++ tailWord_1694555).sum := by decide
  have hdescent : baseEnd_1694555 < baseStart_1694555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694572 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_1694572 : Nat := 118140960795 + 1694572 * 2 ^ 59
def prefixEnd_1694572 : Nat := 4983230072969 + 3 ^ 40 * 1694572 * 2
def baseEnd_1694572 : Nat := 870129939650849212956811

theorem tailTrace_1694572 : CollatzResearch.WordTrace tailWord_1694572 prefixEnd_1694572 870129939650849212956811 := by
  unfold tailWord_1694572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30903059208431264350806985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41204078944575019134409313 30903059208431264350806985)
  ·
    refine ⟨23177294406323448263105239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30903059208431264350806985 23177294406323448263105239)
    ·
      refine ⟨34765941609485172394657859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23177294406323448263105239 34765941609485172394657859)
      ·
        refine ⟨52148912414227758591986789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34765941609485172394657859 52148912414227758591986789)
        ·
          refine ⟨9777921077667704735997523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52148912414227758591986789 9777921077667704735997523)
          ·
            refine ⟨14666881616501557103996285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9777921077667704735997523 14666881616501557103996285)
            ·
              refine ⟨5500080606188083913998607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14666881616501557103996285 5500080606188083913998607)
              ·
                refine ⟨8250120909282125870997911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500080606188083913998607 8250120909282125870997911)
                ·
                  refine ⟨12375181363923188806496867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8250120909282125870997911 12375181363923188806496867)
                  ·
                    refine ⟨18562772045884783209745301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12375181363923188806496867 18562772045884783209745301)
                    ·
                      refine ⟨870129939650849212956811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18562772045884783209745301 870129939650849212956811)
                      ·
                        rfl

theorem cell23_1694572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_1694572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694572 prefixEnd_1694572 := by exact prefixLift 1694572
  have htrace : WordTrace (prefixWord ++ tailWord_1694572) baseStart_1694572 baseEnd_1694572 := by
    simpa [prefixWord, tailWord_1694572, baseEnd_1694572] using wordTrace_append hprefix tailTrace_1694572
  have hstable : (prefixWord ++ tailWord_1694572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694572).length < 2 ^ (prefixWord ++ tailWord_1694572).sum := by decide
  have hdescent : baseEnd_1694572 < baseStart_1694572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694576 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 3, 2, 2]
def baseStart_1694576 : Nat := 118140960795 + 1694576 * 2 ^ 59
def prefixEnd_1694576 : Nat := 4983230072969 + 3 ^ 40 * 1694576 * 2
def baseEnd_1694576 : Nat := 870131993573467197306793

theorem tailTrace_1694576 : CollatzResearch.WordTrace tailWord_1694576 prefixEnd_1694576 870131993573467197306793 := by
  unfold tailWord_1694576
  simp only [CollatzResearch.WordTrace]
  refine ⟨30903132154424018692379791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41204176205898691589839721 30903132154424018692379791)
  ·
    refine ⟨46354698231636028038569687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30903132154424018692379791 46354698231636028038569687)
    ·
      refine ⟨69532047347454042057854531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46354698231636028038569687 69532047347454042057854531)
      ·
        refine ⟨104298071021181063086781797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69532047347454042057854531 104298071021181063086781797)
        ·
          refine ⟨19555888316471449328771587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104298071021181063086781797 19555888316471449328771587)
          ·
            refine ⟨29333832474707173993157381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19555888316471449328771587 29333832474707173993157381)
            ·
              refine ⟨5500093589007595123717009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29333832474707173993157381 5500093589007595123717009)
              ·
                refine ⟨4125070191755696342787757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5500093589007595123717009 4125070191755696342787757)
                ·
                  refine ⟨1546901321908386128545409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4125070191755696342787757 1546901321908386128545409)
                  ·
                    refine ⟨1160175991431289596409057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1546901321908386128545409 1160175991431289596409057)
                    ·
                      refine ⟨870131993573467197306793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160175991431289596409057 870131993573467197306793)
                      ·
                        rfl

theorem cell23_1694576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 2, 2].length) (baseStart_1694576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694576 prefixEnd_1694576 := by exact prefixLift 1694576
  have htrace : WordTrace (prefixWord ++ tailWord_1694576) baseStart_1694576 baseEnd_1694576 := by
    simpa [prefixWord, tailWord_1694576, baseEnd_1694576] using wordTrace_append hprefix tailTrace_1694576
  have hstable : (prefixWord ++ tailWord_1694576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694576).length < 2 ^ (prefixWord ++ tailWord_1694576).sum := by decide
  have hdescent : baseEnd_1694576 < baseStart_1694576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694579 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 3]
def baseStart_1694579 : Nat := 118140960795 + 1694579 * 2 ^ 59
def prefixEnd_1694579 : Nat := 4983230072969 + 3 ^ 40 * 1694579 * 2
def baseEnd_1694579 : Nat := 870133534015430685569279

theorem tailTrace_1694579 : CollatzResearch.WordTrace tailWord_1694579 prefixEnd_1694579 870133534015430685569279 := by
  unfold tailWord_1694579
  simp only [CollatzResearch.WordTrace]
  refine ⟨61806373727837168897118791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41204249151891445931412527 61806373727837168897118791)
  ·
    refine ⟨92709560591755753345678187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61806373727837168897118791 92709560591755753345678187)
    ·
      refine ⟨139064340887633630018517281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92709560591755753345678187 139064340887633630018517281)
      ·
        refine ⟨104298255665725222513887961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139064340887633630018517281 104298255665725222513887961)
        ·
          refine ⟨78223691749293916885415971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104298255665725222513887961 78223691749293916885415971)
          ·
            refine ⟨117335537623940875328123957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78223691749293916885415971 117335537623940875328123957)
            ·
              refine ⟨11000206652244457062011621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117335537623940875328123957 11000206652244457062011621)
              ·
                refine ⟨2062538747295835699127179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11000206652244457062011621 2062538747295835699127179)
                ·
                  refine ⟨3093808120943753548690769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062538747295835699127179 3093808120943753548690769)
                  ·
                    refine ⟨2320356090707815161518077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3093808120943753548690769 2320356090707815161518077)
                    ·
                      refine ⟨870133534015430685569279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2320356090707815161518077 870133534015430685569279)
                      ·
                        rfl

theorem cell23_1694579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 3].length) (baseStart_1694579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694579 prefixEnd_1694579 := by exact prefixLift 1694579
  have htrace : WordTrace (prefixWord ++ tailWord_1694579) baseStart_1694579 baseEnd_1694579 := by
    simpa [prefixWord, tailWord_1694579, baseEnd_1694579] using wordTrace_append hprefix tailTrace_1694579
  have hstable : (prefixWord ++ tailWord_1694579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694579).length < 2 ^ (prefixWord ++ tailWord_1694579).sum := by decide
  have hdescent : baseEnd_1694579 < baseStart_1694579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694620 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_1694620 : Nat := 118140960795 + 1694620 * 2 ^ 59
def prefixEnd_1694620 : Nat := 4983230072969 + 3 ^ 40 * 1694620 * 2
def baseEnd_1694620 : Nat := 290051528907421675052197

theorem tailTrace_1694620 : CollatzResearch.WordTrace tailWord_1694620 prefixEnd_1694620 290051528907421675052197 := by
  unfold tailWord_1694620
  simp only [CollatzResearch.WordTrace]
  refine ⟨30903934560344316449680657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41205246080459088599574209 30903934560344316449680657)
  ·
    refine ⟨23177950920258237337260493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30903934560344316449680657 23177950920258237337260493)
    ·
      refine ⟨8691731595096839001472685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23177950920258237337260493 8691731595096839001472685)
      ·
        refine ⟨3259399348161314625552257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8691731595096839001472685 3259399348161314625552257)
        ·
          refine ⟨2444549511120985969164193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3259399348161314625552257 2444549511120985969164193)
          ·
            refine ⟨1833412133340739476873145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2444549511120985969164193 1833412133340739476873145)
            ·
              refine ⟨1375059100005554607654859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833412133340739476873145 1375059100005554607654859)
              ·
                refine ⟨2062588650008331911482289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375059100005554607654859 2062588650008331911482289)
                ·
                  refine ⟨1546941487506248933611717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2062588650008331911482289 1546941487506248933611717)
                  ·
                    refine ⟨290051528907421675052197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1546941487506248933611717 290051528907421675052197)
                    ·
                      rfl

theorem cell23_1694620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_1694620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694620 prefixEnd_1694620 := by exact prefixLift 1694620
  have htrace : WordTrace (prefixWord ++ tailWord_1694620) baseStart_1694620 baseEnd_1694620 := by
    simpa [prefixWord, tailWord_1694620, baseEnd_1694620] using wordTrace_append hprefix tailTrace_1694620
  have hstable : (prefixWord ++ tailWord_1694620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694620).length < 2 ^ (prefixWord ++ tailWord_1694620).sum := by decide
  have hdescent : baseEnd_1694620 < baseStart_1694620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694642 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_1694642 : Nat := 118140960795 + 1694642 * 2 ^ 59
def prefixEnd_1694642 : Nat := 4983230072969 + 3 ^ 40 * 1694642 * 2
def baseEnd_1694642 : Nat := 290055294432221313027163

theorem tailTrace_1694642 : CollatzResearch.WordTrace tailWord_1694642 prefixEnd_1694642 290055294432221313027163 := by
  unfold tailWord_1694642
  simp only [CollatzResearch.WordTrace]
  refine ⟨15452167881652232664165545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41205781017739287104441453 15452167881652232664165545)
  ·
    refine ⟨11589125911239174498124159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15452167881652232664165545 11589125911239174498124159)
    ·
      refine ⟨17383688866858761747186239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11589125911239174498124159 17383688866858761747186239)
      ·
        refine ⟨26075533300288142620779359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17383688866858761747186239 26075533300288142620779359)
        ·
          refine ⟨39113299950432213931169039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26075533300288142620779359 39113299950432213931169039)
          ·
            refine ⟨58669949925648320896753559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39113299950432213931169039 58669949925648320896753559)
            ·
              refine ⟨88004924888472481345130339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58669949925648320896753559 88004924888472481345130339)
              ·
                refine ⟨132007387332708722017695509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88004924888472481345130339 132007387332708722017695509)
                ·
                  refine ⟨6187846281220721344579477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132007387332708722017695509 6187846281220721344579477)
                  ·
                    refine ⟨290055294432221313027163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6187846281220721344579477 290055294432221313027163)
                    ·
                      rfl

theorem cell23_1694642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_1694642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694642 prefixEnd_1694642 := by exact prefixLift 1694642
  have htrace : WordTrace (prefixWord ++ tailWord_1694642) baseStart_1694642 baseEnd_1694642 := by
    simpa [prefixWord, tailWord_1694642, baseEnd_1694642] using wordTrace_append hprefix tailTrace_1694642
  have hstable : (prefixWord ++ tailWord_1694642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694642).length < 2 ^ (prefixWord ++ tailWord_1694642).sum := by decide
  have hdescent : baseEnd_1694642 < baseStart_1694642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694672 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 7]
def baseStart_1694672 : Nat := 118140960795 + 1694672 * 2 ^ 59
def prefixEnd_1694672 : Nat := 4983230072969 + 3 ^ 40 * 1694672 * 2
def baseEnd_1694672 : Nat := 96686809746255424634039

theorem tailTrace_1694672 : CollatzResearch.WordTrace tailWord_1694672 prefixEnd_1694672 96686809746255424634039 := by
  unfold tailWord_1694672
  simp only [CollatzResearch.WordTrace]
  refine ⟨30904882858250122890127135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41206510477666830520169513 30904882858250122890127135)
  ·
    refine ⟨46357324287375184335190703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30904882858250122890127135 46357324287375184335190703)
    ·
      refine ⟨69535986431062776502786055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46357324287375184335190703 69535986431062776502786055)
      ·
        refine ⟨104303979646594164754179083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69535986431062776502786055 104303979646594164754179083)
        ·
          refine ⟨156455969469891247131268625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104303979646594164754179083 156455969469891247131268625)
          ·
            refine ⟨117341977102418435348451469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156455969469891247131268625 117341977102418435348451469)
            ·
              refine ⟨44003241413406913255669301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117341977102418435348451469 44003241413406913255669301)
              ·
                refine ⟨4125303882506898117718997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44003241413406913255669301 4125303882506898117718997)
                ·
                  refine ⟨96686809746255424634039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4125303882506898117718997 96686809746255424634039)
                  ·
                    rfl

theorem cell23_1694672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 7].length) (baseStart_1694672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694672 prefixEnd_1694672 := by exact prefixLift 1694672
  have htrace : WordTrace (prefixWord ++ tailWord_1694672) baseStart_1694672 baseEnd_1694672 := by
    simpa [prefixWord, tailWord_1694672, baseEnd_1694672] using wordTrace_append hprefix tailTrace_1694672
  have hstable : (prefixWord ++ tailWord_1694672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694672).length < 2 ^ (prefixWord ++ tailWord_1694672).sum := by decide
  have hdescent : baseEnd_1694672 < baseStart_1694672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694756 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1694756 : Nat := 118140960795 + 1694756 * 2 ^ 59
def prefixEnd_1694756 : Nat := 4983230072969 + 3 ^ 40 * 1694756 * 2
def baseEnd_1694756 : Nat := 870224420091276493055965

theorem tailTrace_1694756 : CollatzResearch.WordTrace tailWord_1694756 prefixEnd_1694756 870224420091276493055965 := by
  unfold tailWord_1694756
  simp only [CollatzResearch.WordTrace]
  refine ⟨30906414724097964063156061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41208552965463952084208081 30906414724097964063156061)
  ·
    refine ⟨11589905521536736523683523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30906414724097964063156061 11589905521536736523683523)
    ·
      refine ⟨17384858282305104785525285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11589905521536736523683523 17384858282305104785525285)
      ·
        refine ⟨3259660927932207147285991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17384858282305104785525285 3259660927932207147285991)
        ·
          refine ⟨4889491391898310720928987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259660927932207147285991 4889491391898310720928987)
          ·
            refine ⟨7334237087847466081393481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889491391898310720928987 7334237087847466081393481)
            ·
              refine ⟨5500677815885599561045111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7334237087847466081393481 5500677815885599561045111)
              ·
                refine ⟨8251016723828399341567667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500677815885599561045111 8251016723828399341567667)
                ·
                  refine ⟨12376525085742599012351501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8251016723828399341567667 12376525085742599012351501)
                  ·
                    refine ⟨4641196907153474629631813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12376525085742599012351501 4641196907153474629631813)
                    ·
                      refine ⟨870224420091276493055965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4641196907153474629631813 870224420091276493055965)
                      ·
                        rfl

theorem cell23_1694756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1694756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694756 prefixEnd_1694756 := by exact prefixLift 1694756
  have htrace : WordTrace (prefixWord ++ tailWord_1694756) baseStart_1694756 baseEnd_1694756 := by
    simpa [prefixWord, tailWord_1694756, baseEnd_1694756] using wordTrace_append hprefix tailTrace_1694756
  have hstable : (prefixWord ++ tailWord_1694756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694756).length < 2 ^ (prefixWord ++ tailWord_1694756).sum := by decide
  have hdescent : baseEnd_1694756 < baseStart_1694756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694776 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_1694776 : Nat := 118140960795 + 1694776 * 2 ^ 59
def prefixEnd_1694776 : Nat := 4983230072969 + 3 ^ 40 * 1694776 * 2
def baseEnd_1694776 : Nat := 870234689704366414805873

theorem tailTrace_1694776 : CollatzResearch.WordTrace tailWord_1694776 prefixEnd_1694776 870234689704366414805873 := by
  unfold tailWord_1694776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30906779454061735771020091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41209039272082314361360121 30906779454061735771020091)
  ·
    refine ⟨46360169181092603656530137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30906779454061735771020091 46360169181092603656530137)
    ·
      refine ⟨34770126885819452742397603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46360169181092603656530137 34770126885819452742397603)
      ·
        refine ⟨52155190328729179113596405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34770126885819452742397603 52155190328729179113596405)
        ·
          refine ⟨4889549093318360541899663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52155190328729179113596405 4889549093318360541899663)
          ·
            refine ⟨7334323639977540812849495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889549093318360541899663 7334323639977540812849495)
            ·
              refine ⟨11001485459966311219274243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334323639977540812849495 11001485459966311219274243)
              ·
                refine ⟨16502228189949466828911365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11001485459966311219274243 16502228189949466828911365)
                ·
                  refine ⟨3094167785615525030420881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16502228189949466828911365 3094167785615525030420881)
                  ·
                    refine ⟨2320625839211643772815661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3094167785615525030420881 2320625839211643772815661)
                    ·
                      refine ⟨870234689704366414805873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2320625839211643772815661 870234689704366414805873)
                      ·
                        rfl

theorem cell23_1694776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_1694776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694776 prefixEnd_1694776 := by exact prefixLift 1694776
  have htrace : WordTrace (prefixWord ++ tailWord_1694776) baseStart_1694776 baseEnd_1694776 := by
    simpa [prefixWord, tailWord_1694776, baseEnd_1694776] using wordTrace_append hprefix tailTrace_1694776
  have hstable : (prefixWord ++ tailWord_1694776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694776).length < 2 ^ (prefixWord ++ tailWord_1694776).sum := by decide
  have hdescent : baseEnd_1694776 < baseStart_1694776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694839 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 3, 6]
def baseStart_1694839 : Nat := 118140960795 + 1694839 * 2 ^ 59
def prefixEnd_1694839 : Nat := 4983230072969 + 3 ^ 40 * 1694839 * 2
def baseEnd_1694839 : Nat := 290089012995199889439361

theorem tailTrace_1694839 : CollatzResearch.WordTrace tailWord_1694839 prefixEnd_1694839 290089012995199889439361 := by
  unfold tailWord_1694839
  simp only [CollatzResearch.WordTrace]
  refine ⟨61815856706895233301583571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41210571137930155534389047 61815856706895233301583571)
  ·
    refine ⟨92723785060342849952375357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61815856706895233301583571 92723785060342849952375357)
    ·
      refine ⟨34771419397628568732140759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92723785060342849952375357 34771419397628568732140759)
      ·
        refine ⟨52157129096442853098211139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34771419397628568732140759 52157129096442853098211139)
        ·
          refine ⟨78235693644664279647316709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52157129096442853098211139 78235693644664279647316709)
          ·
            refine ⟨14669192558374552433871883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78235693644664279647316709 14669192558374552433871883)
            ·
              refine ⟨22003788837561828650807825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14669192558374552433871883 22003788837561828650807825)
              ·
                refine ⟨16502841628171371488105869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22003788837561828650807825 16502841628171371488105869)
                ·
                  refine ⟨6188565610564264308039701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16502841628171371488105869 6188565610564264308039701)
                  ·
                    refine ⟨290089012995199889439361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6188565610564264308039701 290089012995199889439361)
                    ·
                      rfl

theorem cell23_1694839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_1694839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694839 prefixEnd_1694839 := by exact prefixLift 1694839
  have htrace : WordTrace (prefixWord ++ tailWord_1694839) baseStart_1694839 baseEnd_1694839 := by
    simpa [prefixWord, tailWord_1694839, baseEnd_1694839] using wordTrace_append hprefix tailTrace_1694839
  have hstable : (prefixWord ++ tailWord_1694839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694839).length < 2 ^ (prefixWord ++ tailWord_1694839).sum := by decide
  have hdescent : baseEnd_1694839 < baseStart_1694839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694859 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 6]
def baseStart_1694859 : Nat := 118140960795 + 1694859 * 2 ^ 59
def prefixEnd_1694859 : Nat := 4983230072969 + 3 ^ 40 * 1694859 * 2
def baseEnd_1694859 : Nat := 870277308598689590067991

theorem tailTrace_1694859 : CollatzResearch.WordTrace tailWord_1694859 prefixEnd_1694859 870277308598689590067991 := by
  unfold tailWord_1694859
  simp only [CollatzResearch.WordTrace]
  refine ⟨61816586166822776717311631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41211057444548517811541087 61816586166822776717311631)
  ·
    refine ⟨92724879250234165075967447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61816586166822776717311631 92724879250234165075967447)
    ·
      refine ⟨139087318875351247613951171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92724879250234165075967447 139087318875351247613951171)
      ·
        refine ⟨208630978313026871420926757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139087318875351247613951171 208630978313026871420926757)
        ·
          refine ⟨39118308433692538391423767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208630978313026871420926757 39118308433692538391423767)
          ·
            refine ⟨58677462650538807587135651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39118308433692538391423767 58677462650538807587135651)
            ·
              refine ⟨88016193975808211380703477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58677462650538807587135651 88016193975808211380703477)
              ·
                refine ⟨8251518185232019816940951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88016193975808211380703477 8251518185232019816940951)
                ·
                  refine ⟨12377277277848029725411427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8251518185232019816940951 12377277277848029725411427)
                  ·
                    refine ⟨18565915916772044588117141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12377277277848029725411427 18565915916772044588117141)
                    ·
                      refine ⟨870277308598689590067991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18565915916772044588117141 870277308598689590067991)
                      ·
                        rfl

theorem cell23_1694859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_1694859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694859 prefixEnd_1694859 := by exact prefixLift 1694859
  have htrace : WordTrace (prefixWord ++ tailWord_1694859) baseStart_1694859 baseEnd_1694859 := by
    simpa [prefixWord, tailWord_1694859, baseEnd_1694859] using wordTrace_append hprefix tailTrace_1694859
  have hstable : (prefixWord ++ tailWord_1694859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694859).length < 2 ^ (prefixWord ++ tailWord_1694859).sum := by decide
  have hdescent : baseEnd_1694859 < baseStart_1694859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694890 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1694890 : Nat := 118140960795 + 1694890 * 2 ^ 59
def prefixEnd_1694890 : Nat := 4983230072969 + 3 ^ 40 * 1694890 * 2
def baseEnd_1694890 : Nat := 290097742166326322926783

theorem tailTrace_1694890 : CollatzResearch.WordTrace tailWord_1694890 prefixEnd_1694890 290097742166326322926783 := by
  unfold tailWord_1694890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15454429207427617252922531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41211811219806979341126749 15454429207427617252922531)
  ·
    refine ⟨23181643811141425879383797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15454429207427617252922531 23181643811141425879383797)
    ·
      refine ⟨2173279107294508676192231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23181643811141425879383797 2173279107294508676192231)
      ·
        refine ⟨3259918660941763014288347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173279107294508676192231 3259918660941763014288347)
        ·
          refine ⟨4889877991412644521432521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259918660941763014288347 4889877991412644521432521)
          ·
            refine ⟨3667408493559483391074391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4889877991412644521432521 3667408493559483391074391)
            ·
              refine ⟨5501112740339225086611587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667408493559483391074391 5501112740339225086611587)
              ·
                refine ⟨8251669110508837629917381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5501112740339225086611587 8251669110508837629917381)
                ·
                  refine ⟨1547187958220407055609509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8251669110508837629917381 1547187958220407055609509)
                  ·
                    refine ⟨290097742166326322926783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1547187958220407055609509 290097742166326322926783)
                    ·
                      rfl

theorem cell23_1694890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1694890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694890 prefixEnd_1694890 := by exact prefixLift 1694890
  have htrace : WordTrace (prefixWord ++ tailWord_1694890) baseStart_1694890 baseEnd_1694890 := by
    simpa [prefixWord, tailWord_1694890, baseEnd_1694890] using wordTrace_append hprefix tailTrace_1694890
  have hstable : (prefixWord ++ tailWord_1694890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694890).length < 2 ^ (prefixWord ++ tailWord_1694890).sum := by decide
  have hdescent : baseEnd_1694890 < baseStart_1694890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694897 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1694897 : Nat := 118140960795 + 1694897 * 2 ^ 59
def prefixEnd_1694897 : Nat := 4983230072969 + 3 ^ 40 * 1694897 * 2
def baseEnd_1694897 : Nat := 870296820863560441392817

theorem tailTrace_1694897 : CollatzResearch.WordTrace tailWord_1694897 prefixEnd_1694897 870296820863560441392817 := by
  unfold tailWord_1694897
  simp only [CollatzResearch.WordTrace]
  refine ⟨61817972140685109207194945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41211981427123406138129963 61817972140685109207194945)
  ·
    refine ⟨46363479105513831905396209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61817972140685109207194945 46363479105513831905396209)
    ·
      refine ⟨34772609329135373929047157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46363479105513831905396209 34772609329135373929047157)
      ·
        refine ⟨3259932124606441305848171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34772609329135373929047157 3259932124606441305848171)
        ·
          refine ⟨4889898186909661958772257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259932124606441305848171 4889898186909661958772257)
          ·
            refine ⟨3667423640182246469079193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4889898186909661958772257 3667423640182246469079193)
            ·
              refine ⟨2750567730136684851809395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667423640182246469079193 2750567730136684851809395)
              ·
                refine ⟨4125851595205027277714093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750567730136684851809395 4125851595205027277714093)
                ·
                  refine ⟨1547194348201885229142785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4125851595205027277714093 1547194348201885229142785)
                  ·
                    refine ⟨1160395761151413921857089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1547194348201885229142785 1160395761151413921857089)
                    ·
                      refine ⟨870296820863560441392817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160395761151413921857089 870296820863560441392817)
                      ·
                        rfl

theorem cell23_1694897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1694897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694897 prefixEnd_1694897 := by exact prefixLift 1694897
  have htrace : WordTrace (prefixWord ++ tailWord_1694897) baseStart_1694897 baseEnd_1694897 := by
    simpa [prefixWord, tailWord_1694897, baseEnd_1694897] using wordTrace_append hprefix tailTrace_1694897
  have hstable : (prefixWord ++ tailWord_1694897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694897).length < 2 ^ (prefixWord ++ tailWord_1694897).sum := by decide
  have hdescent : baseEnd_1694897 < baseStart_1694897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694899 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 1, 9]
def baseStart_1694899 : Nat := 118140960795 + 1694899 * 2 ^ 59
def prefixEnd_1694899 : Nat := 4983230072969 + 3 ^ 40 * 1694899 * 2
def baseEnd_1694899 : Nat := 290099282608289811189269

theorem tailTrace_1694899 : CollatzResearch.WordTrace tailWord_1694899 prefixEnd_1694899 290099282608289811189269 := by
  unfold tailWord_1694899
  simp only [CollatzResearch.WordTrace]
  refine ⟨61818045086677863548767751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41212030057785242365845167 61818045086677863548767751)
  ·
    refine ⟨92727067630016795323151627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61818045086677863548767751 92727067630016795323151627)
    ·
      refine ⟨139090601445025192984727441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92727067630016795323151627 139090601445025192984727441)
      ·
        refine ⟨104317951083768894738545581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139090601445025192984727441 104317951083768894738545581)
        ·
          refine ⟨39119231656413335526954593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104317951083768894738545581 39119231656413335526954593)
          ·
            refine ⟨29339423742310001645215945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39119231656413335526954593 29339423742310001645215945)
            ·
              refine ⟨22004567806732501233911959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29339423742310001645215945 22004567806732501233911959)
              ·
                refine ⟨33006851710098751850867939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22004567806732501233911959 33006851710098751850867939)
                ·
                  refine ⟨49510277565148127776301909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33006851710098751850867939 49510277565148127776301909)
                  ·
                    refine ⟨290099282608289811189269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 49510277565148127776301909 290099282608289811189269)
                    ·
                      rfl

theorem cell23_1694899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 9].length) (baseStart_1694899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694899 prefixEnd_1694899 := by exact prefixLift 1694899
  have htrace : WordTrace (prefixWord ++ tailWord_1694899) baseStart_1694899 baseEnd_1694899 := by
    simpa [prefixWord, tailWord_1694899, baseEnd_1694899] using wordTrace_append hprefix tailTrace_1694899
  have hstable : (prefixWord ++ tailWord_1694899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694899).length < 2 ^ (prefixWord ++ tailWord_1694899).sum := by decide
  have hdescent : baseEnd_1694899 < baseStart_1694899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694910 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_1694910 : Nat := 118140960795 + 1694910 * 2 ^ 59
def prefixEnd_1694910 : Nat := 4983230072969 + 3 ^ 40 * 1694910 * 2
def baseEnd_1694910 : Nat := 870303496112068890530257

theorem tailTrace_1694910 : CollatzResearch.WordTrace tailWord_1694910 prefixEnd_1694910 870303496112068890530257 := by
  unfold tailWord_1694910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727305786204751553427273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41212297526425341618278789 7727305786204751553427273)
  ·
    refine ⟨5795479339653563665070455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7727305786204751553427273 5795479339653563665070455)
    ·
      refine ⟨8693219009480345497605683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5795479339653563665070455 8693219009480345497605683)
      ·
        refine ⟨13039828514220518246408525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8693219009480345497605683 13039828514220518246408525)
        ·
          refine ⟨4889935692832694342403197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13039828514220518246408525 4889935692832694342403197)
          ·
            refine ⟨1833725884812260378401199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4889935692832694342403197 1833725884812260378401199)
            ·
              refine ⟨2750588827218390567601799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833725884812260378401199 2750588827218390567601799)
              ·
                refine ⟨4125883240827585851402699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750588827218390567601799 4125883240827585851402699)
                ·
                  refine ⟨6188824861241378777104049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125883240827585851402699 6188824861241378777104049)
                  ·
                    refine ⟨4641618645931034082828037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6188824861241378777104049 4641618645931034082828037)
                    ·
                      refine ⟨870303496112068890530257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4641618645931034082828037 870303496112068890530257)
                      ·
                        rfl

theorem cell23_1694910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_1694910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694910 prefixEnd_1694910 := by exact prefixLift 1694910
  have htrace : WordTrace (prefixWord ++ tailWord_1694910) baseStart_1694910 baseEnd_1694910 := by
    simpa [prefixWord, tailWord_1694910, baseEnd_1694910] using wordTrace_append hprefix tailTrace_1694910
  have hstable : (prefixWord ++ tailWord_1694910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694910).length < 2 ^ (prefixWord ++ tailWord_1694910).sum := by decide
  have hdescent : baseEnd_1694910 < baseStart_1694910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694914 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1694914 : Nat := 118140960795 + 1694914 * 2 ^ 59
def prefixEnd_1694914 : Nat := 4983230072969 + 3 ^ 40 * 1694914 * 2
def baseEnd_1694914 : Nat := 870305550034686874880239

theorem tailTrace_1694914 : CollatzResearch.WordTrace tailWord_1694914 prefixEnd_1694914 870305550034686874880239 := by
  unfold tailWord_1694914
  simp only [CollatzResearch.WordTrace]
  refine ⟨15454648045405880277640949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41212394787749014073709197 15454648045405880277640949)
  ·
    refine ⟨1448873254256801276028839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15454648045405880277640949 1448873254256801276028839)
    ·
      refine ⟨2173309881385201914043259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448873254256801276028839 2173309881385201914043259)
      ·
        refine ⟨3259964822077802871064889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173309881385201914043259 3259964822077802871064889)
        ·
          refine ⟨2444973616558352153298667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3259964822077802871064889 2444973616558352153298667)
          ·
            refine ⟨3667460424837528229948001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444973616558352153298667 3667460424837528229948001)
            ·
              refine ⟨2750595318628146172461001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667460424837528229948001 2750595318628146172461001)
              ·
                refine ⟨2062946488971109629345751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2750595318628146172461001 2062946488971109629345751)
                ·
                  refine ⟨3094419733456664444018627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062946488971109629345751 3094419733456664444018627)
                  ·
                    refine ⟨4641629600184996666027941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3094419733456664444018627 4641629600184996666027941)
                    ·
                      refine ⟨870305550034686874880239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4641629600184996666027941 870305550034686874880239)
                      ·
                        rfl

theorem cell23_1694914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1694914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694914 prefixEnd_1694914 := by exact prefixLift 1694914
  have htrace : WordTrace (prefixWord ++ tailWord_1694914) baseStart_1694914 baseEnd_1694914 := by
    simpa [prefixWord, tailWord_1694914, baseEnd_1694914] using wordTrace_append hprefix tailTrace_1694914
  have hstable : (prefixWord ++ tailWord_1694914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694914).length < 2 ^ (prefixWord ++ tailWord_1694914).sum := by decide
  have hdescent : baseEnd_1694914 < baseStart_1694914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694974 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_1694974 : Nat := 118140960795 + 1694974 * 2 ^ 59
def prefixEnd_1694974 : Nat := 4983230072969 + 3 ^ 40 * 1694974 * 2
def baseEnd_1694974 : Nat := 870336358873956640129963

theorem tailTrace_1694974 : CollatzResearch.WordTrace tailWord_1694974 prefixEnd_1694974 870336358873956640129963 := by
  unfold tailWord_1694974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727597570175768919718497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41213853707604100905165317 7727597570175768919718497)
  ·
    refine ⟨5795698177631826689788873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7727597570175768919718497 5795698177631826689788873)
    ·
      refine ⟨4346773633223870017341655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5795698177631826689788873 4346773633223870017341655)
      ·
        refine ⟨6520160449835805026012483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346773633223870017341655 6520160449835805026012483)
        ·
          refine ⟨9780240674753707539018725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520160449835805026012483 9780240674753707539018725)
          ·
            refine ⟨1833795126516320163566011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9780240674753707539018725 1833795126516320163566011)
            ·
              refine ⟨2750692689774480245349017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833795126516320163566011 2750692689774480245349017)
              ·
                refine ⟨2063019517330860184011763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2750692689774480245349017 2063019517330860184011763)
                ·
                  refine ⟨3094529275996290276017645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063019517330860184011763 3094529275996290276017645)
                  ·
                    refine ⟨1160448478498608853506617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094529275996290276017645 1160448478498608853506617)
                    ·
                      refine ⟨870336358873956640129963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160448478498608853506617 870336358873956640129963)
                      ·
                        rfl

theorem cell23_1694974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_1694974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694974 prefixEnd_1694974 := by exact prefixLift 1694974
  have htrace : WordTrace (prefixWord ++ tailWord_1694974) baseStart_1694974 baseEnd_1694974 := by
    simpa [prefixWord, tailWord_1694974, baseEnd_1694974] using wordTrace_append hprefix tailTrace_1694974
  have hstable : (prefixWord ++ tailWord_1694974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694974).length < 2 ^ (prefixWord ++ tailWord_1694974).sum := by decide
  have hdescent : baseEnd_1694974 < baseStart_1694974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694993 : List Nat := [1, 2, 2, 1, 1, 4, 2, 5, 5]
def baseStart_1694993 : Nat := 118140960795 + 1694993 * 2 ^ 59
def prefixEnd_1694993 : Nat := 4983230072969 + 3 ^ 40 * 1694993 * 2
def baseEnd_1694993 : Nat := 96705123889599118421375

theorem tailTrace_1694993 : CollatzResearch.WordTrace tailWord_1694993 prefixEnd_1694993 96705123889599118421375 := by
  unfold tailWord_1694993
  simp only [CollatzResearch.WordTrace]
  refine ⟨61821473548337317602689633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41214315698891545068459755 61821473548337317602689633)
  ·
    refine ⟨46366105161252988202017225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61821473548337317602689633 46366105161252988202017225)
    ·
      refine ⟨34774578870939741151512919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46366105161252988202017225 34774578870939741151512919)
      ·
        refine ⟨52161868306409611727269379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34774578870939741151512919 52161868306409611727269379)
        ·
          refine ⟨78242802459614417590904069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52161868306409611727269379 78242802459614417590904069)
          ·
            refine ⟨14670525461177703298294513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78242802459614417590904069 14670525461177703298294513)
            ·
              refine ⟨11002894095883277473720885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14670525461177703298294513 11002894095883277473720885)
              ·
                refine ⟨1031521321489057263161333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11002894095883277473720885 1031521321489057263161333)
                ·
                  refine ⟨96705123889599118421375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1031521321489057263161333 96705123889599118421375)
                  ·
                    rfl

theorem cell23_1694993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 5].length) (baseStart_1694993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1694993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1694993 prefixEnd_1694993 := by exact prefixLift 1694993
  have htrace : WordTrace (prefixWord ++ tailWord_1694993) baseStart_1694993 baseEnd_1694993 := by
    simpa [prefixWord, tailWord_1694993, baseEnd_1694993] using wordTrace_append hprefix tailTrace_1694993
  have hstable : (prefixWord ++ tailWord_1694993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694993).length < 2 ^ (prefixWord ++ tailWord_1694993).sum := by decide
  have hdescent : baseEnd_1694993 < baseStart_1694993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695043 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 3, 6, 2]
def baseStart_1695043 : Nat := 118140960795 + 1695043 * 2 ^ 59
def prefixEnd_1695043 : Nat := 4983230072969 + 3 ^ 40 * 1695043 * 2
def baseEnd_1695043 : Nat := 870371789039116870167145

theorem tailTrace_1695043 : CollatzResearch.WordTrace tailWord_1695043 prefixEnd_1695043 870371789039116870167145 := by
  unfold tailWord_1695043
  simp only [CollatzResearch.WordTrace]
  refine ⟨61823297198156176142009783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41215531465437450761339855 61823297198156176142009783)
  ·
    refine ⟨92734945797234264213014675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61823297198156176142009783 92734945797234264213014675)
    ·
      refine ⟨139102418695851396319522013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92734945797234264213014675 139102418695851396319522013)
      ·
        refine ⟨52163407010944273619820755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139102418695851396319522013 52163407010944273619820755)
        ·
          refine ⟨78245110516416410429731133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52163407010944273619820755 78245110516416410429731133)
          ·
            refine ⟨29341916443656153911149175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78245110516416410429731133 29341916443656153911149175)
            ·
              refine ⟨44012874665484230866723763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29341916443656153911149175 44012874665484230866723763)
              ·
                refine ⟨66019311998226346300085645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44012874665484230866723763 66019311998226346300085645)
                ·
                  refine ⟨24757241999334879862532117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66019311998226346300085645 24757241999334879862532117)
                  ·
                    refine ⟨1160495718718822493556193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24757241999334879862532117 1160495718718822493556193)
                    ·
                      refine ⟨870371789039116870167145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160495718718822493556193 870371789039116870167145)
                      ·
                        rfl

theorem cell23_1695043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_1695043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695043 prefixEnd_1695043 := by exact prefixLift 1695043
  have htrace : WordTrace (prefixWord ++ tailWord_1695043) baseStart_1695043 baseEnd_1695043 := by
    simpa [prefixWord, tailWord_1695043, baseEnd_1695043] using wordTrace_append hprefix tailTrace_1695043
  have hstable : (prefixWord ++ tailWord_1695043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695043).length < 2 ^ (prefixWord ++ tailWord_1695043).sum := by decide
  have hdescent : baseEnd_1695043 < baseStart_1695043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695056 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_1695056 : Nat := 118140960795 + 1695056 * 2 ^ 59
def prefixEnd_1695056 : Nat := 4983230072969 + 3 ^ 40 * 1695056 * 2
def baseEnd_1695056 : Nat := 870378464287625319304585

theorem tailTrace_1695056 : CollatzResearch.WordTrace tailWord_1695056 prefixEnd_1695056 870378464287625319304585 := by
  unfold tailWord_1695056
  simp only [CollatzResearch.WordTrace]
  refine ⟨30911885673554539681116511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41215847564739386241488681 30911885673554539681116511)
  ·
    refine ⟨46367828510331809521674767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30911885673554539681116511 46367828510331809521674767)
    ·
      refine ⟨69551742765497714282512151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46367828510331809521674767 69551742765497714282512151)
      ·
        refine ⟨104327614148246571423768227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69551742765497714282512151 104327614148246571423768227)
        ·
          refine ⟨156491421222369857135652341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104327614148246571423768227 156491421222369857135652341)
          ·
            refine ⟨14671070739597174106467407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156491421222369857135652341 14671070739597174106467407)
            ·
              refine ⟨22006606109395761159701111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14671070739597174106467407 22006606109395761159701111)
              ·
                refine ⟨33009909164093641739551667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22006606109395761159701111 33009909164093641739551667)
                ·
                  refine ⟨49514863746140462609327501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33009909164093641739551667 49514863746140462609327501)
                  ·
                    refine ⟨18568073904802673478497813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49514863746140462609327501 18568073904802673478497813)
                    ·
                      refine ⟨870378464287625319304585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18568073904802673478497813 870378464287625319304585)
                      ·
                        rfl

theorem cell23_1695056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_1695056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695056 prefixEnd_1695056 := by exact prefixLift 1695056
  have htrace : WordTrace (prefixWord ++ tailWord_1695056) baseStart_1695056 baseEnd_1695056 := by
    simpa [prefixWord, tailWord_1695056, baseEnd_1695056] using wordTrace_append hprefix tailTrace_1695056
  have hstable : (prefixWord ++ tailWord_1695056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695056).length < 2 ^ (prefixWord ++ tailWord_1695056).sum := by decide
  have hdescent : baseEnd_1695056 < baseStart_1695056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695060 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_1695060 : Nat := 118140960795 + 1695060 * 2 ^ 59
def prefixEnd_1695060 : Nat := 4983230072969 + 3 ^ 40 * 1695060 * 2
def baseEnd_1695060 : Nat := 870380518210243303654567

theorem tailTrace_1695060 : CollatzResearch.WordTrace tailWord_1695060 prefixEnd_1695060 870380518210243303654567 := by
  unfold tailWord_1695060
  simp only [CollatzResearch.WordTrace]
  refine ⟨30911958619547294022689317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41215944826063058696919089 30911958619547294022689317)
  ·
    refine ⟨5795992241165117629254247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30911958619547294022689317 5795992241165117629254247)
    ·
      refine ⟨8693988361747676443881371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5795992241165117629254247 8693988361747676443881371)
      ·
        refine ⟨13040982542621514665822057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8693988361747676443881371 13040982542621514665822057)
        ·
          refine ⟨9780736906966135999366543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13040982542621514665822057 9780736906966135999366543)
          ·
            refine ⟨14671105360449203999049815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9780736906966135999366543 14671105360449203999049815)
            ·
              refine ⟨22006658040673805998574723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14671105360449203999049815 22006658040673805998574723)
              ·
                refine ⟨33009987061010708997862085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22006658040673805998574723 33009987061010708997862085)
                ·
                  refine ⟨6189372573939507937099141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33009987061010708997862085 6189372573939507937099141)
                  ·
                    refine ⟨1160507357613657738206089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6189372573939507937099141 1160507357613657738206089)
                    ·
                      refine ⟨870380518210243303654567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160507357613657738206089 870380518210243303654567)
                      ·
                        rfl

theorem cell23_1695060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_1695060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695060 prefixEnd_1695060 := by exact prefixLift 1695060
  have htrace : WordTrace (prefixWord ++ tailWord_1695060) baseStart_1695060 baseEnd_1695060 := by
    simpa [prefixWord, tailWord_1695060, baseEnd_1695060] using wordTrace_append hprefix tailTrace_1695060
  have hstable : (prefixWord ++ tailWord_1695060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695060).length < 2 ^ (prefixWord ++ tailWord_1695060).sum := by decide
  have hdescent : baseEnd_1695060 < baseStart_1695060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695096 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 4, 9]
def baseStart_1695096 : Nat := 118140960795 + 1695096 * 2 ^ 59
def prefixEnd_1695096 : Nat := 4983230072969 + 3 ^ 40 * 1695096 * 2
def baseEnd_1695096 : Nat := 290133001171268387601467

theorem tailTrace_1695096 : CollatzResearch.WordTrace tailWord_1695096 prefixEnd_1695096 290133001171268387601467 := by
  unfold tailWord_1695096
  simp only [CollatzResearch.WordTrace]
  refine ⟨30912615133482083096844571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41216820177976110795792761 30912615133482083096844571)
  ·
    refine ⟨46368922700223124645266857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30912615133482083096844571 46368922700223124645266857)
    ·
      refine ⟨34776692025167343483950143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46368922700223124645266857 34776692025167343483950143)
      ·
        refine ⟨52165038037751015225925215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34776692025167343483950143 52165038037751015225925215)
        ·
          refine ⟨78247557056626522838887823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52165038037751015225925215 78247557056626522838887823)
          ·
            refine ⟨117371335584939784258331735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78247557056626522838887823 117371335584939784258331735)
            ·
              refine ⟨176057003377409676387497603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117371335584939784258331735 176057003377409676387497603)
              ·
                refine ⟨264085505066114514581246405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176057003377409676387497603 264085505066114514581246405)
                ·
                  refine ⟨49516032199896471483983701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264085505066114514581246405 49516032199896471483983701)
                  ·
                    refine ⟨290133001171268387601467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 49516032199896471483983701 290133001171268387601467)
                    ·
                      rfl

theorem cell23_1695096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_1695096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695096 prefixEnd_1695096 := by exact prefixLift 1695096
  have htrace : WordTrace (prefixWord ++ tailWord_1695096) baseStart_1695096 baseEnd_1695096 := by
    simpa [prefixWord, tailWord_1695096, baseEnd_1695096] using wordTrace_append hprefix tailTrace_1695096
  have hstable : (prefixWord ++ tailWord_1695096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695096).length < 2 ^ (prefixWord ++ tailWord_1695096).sum := by decide
  have hdescent : baseEnd_1695096 < baseStart_1695096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695164 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_1695164 : Nat := 118140960795 + 1695164 * 2 ^ 59
def prefixEnd_1695164 : Nat := 4983230072969 + 3 ^ 40 * 1695164 * 2
def baseEnd_1695164 : Nat := 290144640066103632251363

theorem tailTrace_1695164 : CollatzResearch.WordTrace tailWord_1695164 prefixEnd_1695164 290144640066103632251363 := by
  unfold tailWord_1695164
  simp only [CollatzResearch.WordTrace]
  refine ⟨30913855215358906903582273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41218473620478542538109697 30913855215358906903582273)
  ·
    refine ⟨23185391411519180177686705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30913855215358906903582273 23185391411519180177686705)
    ·
      refine ⟨17389043558639385133265029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23185391411519180177686705 17389043558639385133265029)
      ·
        refine ⟨3260445667244884712487193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17389043558639385133265029 3260445667244884712487193)
        ·
          refine ⟨2445334250433663534365395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3260445667244884712487193 2445334250433663534365395)
          ·
            refine ⟨3668001375650495301548093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445334250433663534365395 3668001375650495301548093)
            ·
              refine ⟨1375500515868935738080535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3668001375650495301548093 1375500515868935738080535)
              ·
                refine ⟨2063250773803403607120803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375500515868935738080535 2063250773803403607120803)
                ·
                  refine ⟨3094876160705105410681205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063250773803403607120803 3094876160705105410681205)
                  ·
                    refine ⟨290144640066103632251363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3094876160705105410681205 290144640066103632251363)
                    ·
                      rfl

theorem cell23_1695164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_1695164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695164 prefixEnd_1695164 := by exact prefixLift 1695164
  have htrace : WordTrace (prefixWord ++ tailWord_1695164) baseStart_1695164 baseEnd_1695164 := by
    simpa [prefixWord, tailWord_1695164, baseEnd_1695164] using wordTrace_append hprefix tailTrace_1695164
  have hstable : (prefixWord ++ tailWord_1695164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695164).length < 2 ^ (prefixWord ++ tailWord_1695164).sum := by decide
  have hdescent : baseEnd_1695164 < baseStart_1695164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695184 : List Nat := [2, 1, 1, 1, 1, 2, 2, 8, 1, 2, 2]
def baseStart_1695184 : Nat := 118140960795 + 1695184 * 2 ^ 59
def prefixEnd_1695184 : Nat := 4983230072969 + 3 ^ 40 * 1695184 * 2
def baseEnd_1695184 : Nat := 870444189811400818503997

theorem tailTrace_1695184 : CollatzResearch.WordTrace tailWord_1695184 prefixEnd_1695184 870444189811400818503997 := by
  unfold tailWord_1695184
  simp only [CollatzResearch.WordTrace]
  refine ⟨30914219945322678611446303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41218959927096904815261737 30914219945322678611446303)
  ·
    refine ⟨46371329917984017917169455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30914219945322678611446303 46371329917984017917169455)
    ·
      refine ⟨69556994876976026875754183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46371329917984017917169455 69556994876976026875754183)
      ·
        refine ⟨104335492315464040313631275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69556994876976026875754183 104335492315464040313631275)
        ·
          refine ⟨156503238473196060470446913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104335492315464040313631275 156503238473196060470446913)
          ·
            refine ⟨117377428854897045352835185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156503238473196060470446913 117377428854897045352835185)
            ·
              refine ⟨88033071641172784014626389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117377428854897045352835185 88033071641172784014626389)
              ·
                refine ⟨1031637558294993562671403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 88033071641172784014626389 1031637558294993562671403)
                ·
                  refine ⟨1547456337442490344007105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031637558294993562671403 1547456337442490344007105)
                  ·
                    refine ⟨1160592253081867758005329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1547456337442490344007105 1160592253081867758005329)
                    ·
                      refine ⟨870444189811400818503997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160592253081867758005329 870444189811400818503997)
                      ·
                        rfl

theorem cell23_1695184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 2, 2].length) (baseStart_1695184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695184 prefixEnd_1695184 := by exact prefixLift 1695184
  have htrace : WordTrace (prefixWord ++ tailWord_1695184) baseStart_1695184 baseEnd_1695184 := by
    simpa [prefixWord, tailWord_1695184, baseEnd_1695184] using wordTrace_append hprefix tailTrace_1695184
  have hstable : (prefixWord ++ tailWord_1695184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695184).length < 2 ^ (prefixWord ++ tailWord_1695184).sum := by decide
  have hdescent : baseEnd_1695184 < baseStart_1695184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695197 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1695197 : Nat := 118140960795 + 1695197 * 2 ^ 59
def prefixEnd_1695197 : Nat := 4983230072969 + 3 ^ 40 * 1695197 * 2
def baseEnd_1695197 : Nat := 870450865059909267641437

theorem tailTrace_1695197 : CollatzResearch.WordTrace tailWord_1695197 prefixEnd_1695197 870450865059909267641437 := by
  unfold tailWord_1695197
  simp only [CollatzResearch.WordTrace]
  refine ⟨61828914039598260443115845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41219276026398840295410563 61828914039598260443115845)
  ·
    refine ⟨11592921382424673833084221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61828914039598260443115845 11592921382424673833084221)
    ·
      refine ⟨4347345518409252687406583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11592921382424673833084221 4347345518409252687406583)
      ·
        refine ⟨6521018277613879031109875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4347345518409252687406583 6521018277613879031109875)
        ·
          refine ⟨9781527416420818546664813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521018277613879031109875 9781527416420818546664813)
          ·
            refine ⟨3668072781157806954999305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9781527416420818546664813 3668072781157806954999305)
            ·
              refine ⟨2751054585868355216249479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668072781157806954999305 2751054585868355216249479)
              ·
                refine ⟨4126581878802532824374219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751054585868355216249479 4126581878802532824374219)
                ·
                  refine ⟨6189872818203799236561329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126581878802532824374219 6189872818203799236561329)
                  ·
                    refine ⟨4642404613652849427420997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6189872818203799236561329 4642404613652849427420997)
                    ·
                      refine ⟨870450865059909267641437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4642404613652849427420997 870450865059909267641437)
                      ·
                        rfl

theorem cell23_1695197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1695197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695197 prefixEnd_1695197 := by exact prefixLift 1695197
  have htrace : WordTrace (prefixWord ++ tailWord_1695197) baseStart_1695197 baseEnd_1695197 := by
    simpa [prefixWord, tailWord_1695197, baseEnd_1695197] using wordTrace_append hprefix tailTrace_1695197
  have hstable : (prefixWord ++ tailWord_1695197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695197).length < 2 ^ (prefixWord ++ tailWord_1695197).sum := by decide
  have hdescent : baseEnd_1695197 < baseStart_1695197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695218 : List Nat := [3, 2, 1, 4, 1, 2, 2, 3, 1, 2, 2]
def baseStart_1695218 : Nat := 118140960795 + 1695218 * 2 ^ 59
def prefixEnd_1695218 : Nat := 4983230072969 + 3 ^ 40 * 1695218 * 2
def baseEnd_1695218 : Nat := 870461648153653685478841

theorem tailTrace_1695218 : CollatzResearch.WordTrace tailWord_1695218 prefixEnd_1695218 870461648153653685478841 := by
  unfold tailWord_1695218
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457419993130545257407577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41219786648348120686420205 15457419993130545257407577)
  ·
    refine ⟨11593064994847908943055683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15457419993130545257407577 11593064994847908943055683)
    ·
      refine ⟨17389597492271863414583525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11593064994847908943055683 17389597492271863414583525)
      ·
        refine ⟨3260549529800974390234411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17389597492271863414583525 3260549529800974390234411)
        ·
          refine ⟨4890824294701461585351617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260549529800974390234411 4890824294701461585351617)
          ·
            refine ⟨3668118221026096189013713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4890824294701461585351617 3668118221026096189013713)
            ·
              refine ⟨2751088665769572141760285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668118221026096189013713 2751088665769572141760285)
              ·
                refine ⟨1031658249663589553160107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2751088665769572141760285 1031658249663589553160107)
                ·
                  refine ⟨1547487374495384329740161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031658249663589553160107 1547487374495384329740161)
                  ·
                    refine ⟨1160615530871538247305121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1547487374495384329740161 1160615530871538247305121)
                    ·
                      refine ⟨870461648153653685478841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160615530871538247305121 870461648153653685478841)
                      ·
                        rfl

theorem cell23_1695218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_1695218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695218 prefixEnd_1695218 := by exact prefixLift 1695218
  have htrace : WordTrace (prefixWord ++ tailWord_1695218) baseStart_1695218 baseEnd_1695218 := by
    simpa [prefixWord, tailWord_1695218, baseEnd_1695218] using wordTrace_append hprefix tailTrace_1695218
  have hstable : (prefixWord ++ tailWord_1695218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695218).length < 2 ^ (prefixWord ++ tailWord_1695218).sum := by decide
  have hdescent : baseEnd_1695218 < baseStart_1695218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695221 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_1695221 : Nat := 118140960795 + 1695221 * 2 ^ 59
def prefixEnd_1695221 : Nat := 4983230072969 + 3 ^ 40 * 1695221 * 2
def baseEnd_1695221 : Nat := 870463188595617173741327

theorem tailTrace_1695221 : CollatzResearch.WordTrace tailWord_1695221 prefixEnd_1695221 870463188595617173741327 := by
  unfold tailWord_1695221
  simp only [CollatzResearch.WordTrace]
  refine ⟨61829789391511312541989517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41219859594340875027993011 61829789391511312541989517)
  ·
    refine ⟨23186171021816742203246069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61829789391511312541989517 23186171021816742203246069)
    ·
      refine ⟨2173703533295319581554319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23186171021816742203246069 2173703533295319581554319)
      ·
        refine ⟨3260555299942979372331479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173703533295319581554319 3260555299942979372331479)
        ·
          refine ⟨4890832949914469058497219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260555299942979372331479 4890832949914469058497219)
          ·
            refine ⟨7336249424871703587745829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890832949914469058497219 7336249424871703587745829)
            ·
              refine ⟨1375546767163444422702343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7336249424871703587745829 1375546767163444422702343)
              ·
                refine ⟨2063320150745166634053515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375546767163444422702343 2063320150745166634053515)
                ·
                  refine ⟨3094980226117749951080273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063320150745166634053515 3094980226117749951080273)
                  ·
                    refine ⟨2321235169588312463310205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3094980226117749951080273 2321235169588312463310205)
                    ·
                      refine ⟨870463188595617173741327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2321235169588312463310205 870463188595617173741327)
                      ·
                        rfl

theorem cell23_1695221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_1695221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695221 prefixEnd_1695221 := by exact prefixLift 1695221
  have htrace : WordTrace (prefixWord ++ tailWord_1695221) baseStart_1695221 baseEnd_1695221 := by
    simpa [prefixWord, tailWord_1695221, baseEnd_1695221] using wordTrace_append hprefix tailTrace_1695221
  have hstable : (prefixWord ++ tailWord_1695221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695221).length < 2 ^ (prefixWord ++ tailWord_1695221).sum := by decide
  have hdescent : baseEnd_1695221 < baseStart_1695221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695223 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_1695223 : Nat := 118140960795 + 1695223 * 2 ^ 59
def prefixEnd_1695223 : Nat := 4983230072969 + 3 ^ 40 * 1695223 * 2
def baseEnd_1695223 : Nat := 870464215556926165916317

theorem tailTrace_1695223 : CollatzResearch.WordTrace tailWord_1695223 prefixEnd_1695223 870464215556926165916317 := by
  unfold tailWord_1695223
  simp only [CollatzResearch.WordTrace]
  refine ⟨61829862337504066883562323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41219908225002711255708215 61829862337504066883562323)
  ·
    refine ⟨92744793506256100325343485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61829862337504066883562323 92744793506256100325343485)
    ·
      refine ⟨34779297564846037622003807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92744793506256100325343485 34779297564846037622003807)
      ·
        refine ⟨52168946347269056433005711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34779297564846037622003807 52168946347269056433005711)
        ·
          refine ⟨78253419520903584649508567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52168946347269056433005711 78253419520903584649508567)
          ·
            refine ⟨117380129281355376974262851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78253419520903584649508567 117380129281355376974262851)
            ·
              refine ⟨176070193922033065461394277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117380129281355376974262851 176070193922033065461394277)
              ·
                refine ⟨33013161360381199774011427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176070193922033065461394277 33013161360381199774011427)
                ·
                  refine ⟨49519742040571799661017141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33013161360381199774011427 49519742040571799661017141)
                  ·
                    refine ⟨4642475816303606218220357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49519742040571799661017141 4642475816303606218220357)
                    ·
                      refine ⟨870464215556926165916317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4642475816303606218220357 870464215556926165916317)
                      ·
                        rfl

theorem cell23_1695223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_1695223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695223 prefixEnd_1695223 := by exact prefixLift 1695223
  have htrace : WordTrace (prefixWord ++ tailWord_1695223) baseStart_1695223 baseEnd_1695223 := by
    simpa [prefixWord, tailWord_1695223, baseEnd_1695223] using wordTrace_append hprefix tailTrace_1695223
  have hstable : (prefixWord ++ tailWord_1695223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695223).length < 2 ^ (prefixWord ++ tailWord_1695223).sum := by decide
  have hdescent : baseEnd_1695223 < baseStart_1695223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695227 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 1, 3, 2]
def baseStart_1695227 : Nat := 118140960795 + 1695227 * 2 ^ 59
def prefixEnd_1695227 : Nat := 4983230072969 + 3 ^ 40 * 1695227 * 2
def baseEnd_1695227 : Nat := 870466269479544150266299

theorem tailTrace_1695227 : CollatzResearch.WordTrace tailWord_1695227 prefixEnd_1695227 870466269479544150266299 := by
  unfold tailWord_1695227
  simp only [CollatzResearch.WordTrace]
  refine ⟨61830008229489575566707935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41220005486326383711138623 61830008229489575566707935)
  ·
    refine ⟨92745012344234363350061903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61830008229489575566707935 92745012344234363350061903)
    ·
      refine ⟨139117518516351545025092855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92745012344234363350061903 139117518516351545025092855)
      ·
        refine ⟨208676277774527317537639283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139117518516351545025092855 208676277774527317537639283)
        ·
          refine ⟨313014416661790976306458925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208676277774527317537639283 313014416661790976306458925)
          ·
            refine ⟨117380406248171616114922097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313014416661790976306458925 117380406248171616114922097)
            ·
              refine ⟨88035304686128712086191573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117380406248171616114922097 88035304686128712086191573)
              ·
                refine ⟨2063327453581141689520115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88035304686128712086191573 2063327453581141689520115)
                ·
                  refine ⟨3094991180371712534280173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063327453581141689520115 3094991180371712534280173)
                  ·
                    refine ⟨1160621692639392200355065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094991180371712534280173 1160621692639392200355065)
                    ·
                      refine ⟨870466269479544150266299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160621692639392200355065 870466269479544150266299)
                      ·
                        rfl

theorem cell23_1695227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 3, 2].length) (baseStart_1695227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695227 prefixEnd_1695227 := by exact prefixLift 1695227
  have htrace : WordTrace (prefixWord ++ tailWord_1695227) baseStart_1695227 baseEnd_1695227 := by
    simpa [prefixWord, tailWord_1695227, baseEnd_1695227] using wordTrace_append hprefix tailTrace_1695227
  have hstable : (prefixWord ++ tailWord_1695227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695227).length < 2 ^ (prefixWord ++ tailWord_1695227).sum := by decide
  have hdescent : baseEnd_1695227 < baseStart_1695227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695257 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 8, 2, 2]
def baseStart_1695257 : Nat := 118140960795 + 1695257 * 2 ^ 59
def prefixEnd_1695257 : Nat := 4983230072969 + 3 ^ 40 * 1695257 * 2
def baseEnd_1695257 : Nat := 870481673899179032891161

theorem tailTrace_1695257 : CollatzResearch.WordTrace tailWord_1695257 prefixEnd_1695257 870481673899179032891161 := by
  unfold tailWord_1695257
  simp only [CollatzResearch.WordTrace]
  refine ⟨61831102419380890690300025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41220734946253927126866683 61831102419380890690300025)
  ·
    refine ⟨46373326814535668017725019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61831102419380890690300025 46373326814535668017725019)
    ·
      refine ⟨69559990221803502026587529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46373326814535668017725019 69559990221803502026587529)
      ·
        refine ⟨52169992666352626519940647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69559990221803502026587529 52169992666352626519940647)
        ·
          refine ⟨78254988999528939779910971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52169992666352626519940647 78254988999528939779910971)
          ·
            refine ⟨117382483499293409669866457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78254988999528939779910971 117382483499293409669866457)
            ·
              refine ⟨88036862624470057252399843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117382483499293409669866457 88036862624470057252399843)
              ·
                refine ⟨132055293936705085878599765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88036862624470057252399843 132055293936705085878599765)
                ·
                  refine ⟨1547522975820762725139841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 132055293936705085878599765 1547522975820762725139841)
                  ·
                    refine ⟨1160642231865572043854881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1547522975820762725139841 1160642231865572043854881)
                    ·
                      refine ⟨870481673899179032891161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160642231865572043854881 870481673899179032891161)
                      ·
                        rfl

theorem cell23_1695257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_1695257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695257 prefixEnd_1695257 := by exact prefixLift 1695257
  have htrace : WordTrace (prefixWord ++ tailWord_1695257) baseStart_1695257 baseEnd_1695257 := by
    simpa [prefixWord, tailWord_1695257, baseEnd_1695257] using wordTrace_append hprefix tailTrace_1695257
  have hstable : (prefixWord ++ tailWord_1695257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695257).length < 2 ^ (prefixWord ++ tailWord_1695257).sum := by decide
  have hdescent : baseEnd_1695257 < baseStart_1695257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695260 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_1695260 : Nat := 118140960795 + 1695260 * 2 ^ 59
def prefixEnd_1695260 : Nat := 4983230072969 + 3 ^ 40 * 1695260 * 2
def baseEnd_1695260 : Nat := 870483214341142521153647

theorem tailTrace_1695260 : CollatzResearch.WordTrace tailWord_1695260 prefixEnd_1695260 870483214341142521153647 := by
  unfold tailWord_1695260
  simp only [CollatzResearch.WordTrace]
  refine ⟨30915605919185011101329617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41220807892246681468439489 30915605919185011101329617)
  ·
    refine ⟨23186704439388758325997213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30915605919185011101329617 23186704439388758325997213)
    ·
      refine ⟨8695014164770784372248955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23186704439388758325997213 8695014164770784372248955)
      ·
        refine ⟨13042521247156176558373433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8695014164770784372248955 13042521247156176558373433)
        ·
          refine ⟨9781890935367132418780075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13042521247156176558373433 9781890935367132418780075)
          ·
            refine ⟨14672836403050698628170113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9781890935367132418780075 14672836403050698628170113)
            ·
              refine ⟨11004627302288023971127585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14672836403050698628170113 11004627302288023971127585)
              ·
                refine ⟨8253470476716017978345689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11004627302288023971127585 8253470476716017978345689)
                ·
                  refine ⟨6190102857537013483759267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8253470476716017978345689 6190102857537013483759267)
                  ·
                    refine ⟨9285154286305520225638901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6190102857537013483759267 9285154286305520225638901)
                    ·
                      refine ⟨870483214341142521153647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9285154286305520225638901 870483214341142521153647)
                      ·
                        rfl

theorem cell23_1695260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_1695260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695260 prefixEnd_1695260 := by exact prefixLift 1695260
  have htrace : WordTrace (prefixWord ++ tailWord_1695260) baseStart_1695260 baseEnd_1695260 := by
    simpa [prefixWord, tailWord_1695260, baseEnd_1695260] using wordTrace_append hprefix tailTrace_1695260
  have hstable : (prefixWord ++ tailWord_1695260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695260).length < 2 ^ (prefixWord ++ tailWord_1695260).sum := by decide
  have hdescent : baseEnd_1695260 < baseStart_1695260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695274 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_1695274 : Nat := 118140960795 + 1695274 * 2 ^ 59
def prefixEnd_1695274 : Nat := 4983230072969 + 3 ^ 40 * 1695274 * 2
def baseEnd_1695274 : Nat := 870490403070305466378583

theorem tailTrace_1695274 : CollatzResearch.WordTrace tailWord_1695274 prefixEnd_1695274 870490403070305466378583 := by
  unfold tailWord_1695274
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457930615079825648417219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41221148306879535062445917 15457930615079825648417219)
  ·
    refine ⟨23186895922619738472625829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15457930615079825648417219 23186895922619738472625829)
    ·
      refine ⟨4347542985491200963617343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23186895922619738472625829 4347542985491200963617343)
      ·
        refine ⟨6521314478236801445426015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4347542985491200963617343 6521314478236801445426015)
        ·
          refine ⟨9781971717355202168139023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521314478236801445426015 9781971717355202168139023)
          ·
            refine ⟨14672957576032803252208535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9781971717355202168139023 14672957576032803252208535)
            ·
              refine ⟨22009436364049204878312803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14672957576032803252208535 22009436364049204878312803)
              ·
                refine ⟨33014154546073807317469205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22009436364049204878312803 33014154546073807317469205)
                ·
                  refine ⟨1547538494347209718006369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33014154546073807317469205 1547538494347209718006369)
                  ·
                    refine ⟨1160653870760407288504777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1547538494347209718006369 1160653870760407288504777)
                    ·
                      refine ⟨870490403070305466378583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160653870760407288504777 870490403070305466378583)
                      ·
                        rfl

theorem cell23_1695274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_1695274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695274 prefixEnd_1695274 := by exact prefixLift 1695274
  have htrace : WordTrace (prefixWord ++ tailWord_1695274) baseStart_1695274 baseEnd_1695274 := by
    simpa [prefixWord, tailWord_1695274, baseEnd_1695274] using wordTrace_append hprefix tailTrace_1695274
  have hstable : (prefixWord ++ tailWord_1695274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695274).length < 2 ^ (prefixWord ++ tailWord_1695274).sum := by decide
  have hdescent : baseEnd_1695274 < baseStart_1695274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695302 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_1695302 : Nat := 118140960795 + 1695302 * 2 ^ 59
def prefixEnd_1695302 : Nat := 4983230072969 + 3 ^ 40 * 1695302 * 2
def baseEnd_1695302 : Nat := 870504780528631356828455

theorem tailTrace_1695302 : CollatzResearch.WordTrace tailWord_1695302 prefixEnd_1695302 870504780528631356828455 := by
  unfold tailWord_1695302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932273240756808230490255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41221829136145242250458773 1932273240756808230490255)
  ·
    refine ⟨2898409861135212345735383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1932273240756808230490255 2898409861135212345735383)
    ·
      refine ⟨4347614791702818518603075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2898409861135212345735383 4347614791702818518603075)
      ·
        refine ⟨6521422187554227777904613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4347614791702818518603075 6521422187554227777904613)
        ·
          refine ⟨1222766660166417708357115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6521422187554227777904613 1222766660166417708357115)
          ·
            refine ⟨1834149990249626562535673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222766660166417708357115 1834149990249626562535673)
            ·
              refine ⟨1375612492687219921901755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834149990249626562535673 1375612492687219921901755)
              ·
                refine ⟨2063418739030829882852633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375612492687219921901755 2063418739030829882852633)
                ·
                  refine ⟨1547564054273122412139475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2063418739030829882852633 1547564054273122412139475)
                  ·
                    refine ⟨2321346081409683618209213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1547564054273122412139475 2321346081409683618209213)
                    ·
                      refine ⟨870504780528631356828455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2321346081409683618209213 870504780528631356828455)
                      ·
                        rfl

theorem cell23_1695302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_1695302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695302 prefixEnd_1695302 := by exact prefixLift 1695302
  have htrace : WordTrace (prefixWord ++ tailWord_1695302) baseStart_1695302 baseEnd_1695302 := by
    simpa [prefixWord, tailWord_1695302, baseEnd_1695302] using wordTrace_append hprefix tailTrace_1695302
  have hstable : (prefixWord ++ tailWord_1695302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695302).length < 2 ^ (prefixWord ++ tailWord_1695302).sum := by decide
  have hdescent : baseEnd_1695302 < baseStart_1695302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695308 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 2, 2, 2]
def baseStart_1695308 : Nat := 118140960795 + 1695308 * 2 ^ 59
def prefixEnd_1695308 : Nat := 4983230072969 + 3 ^ 40 * 1695308 * 2
def baseEnd_1695308 : Nat := 870507861412558333353427

theorem tailTrace_1695308 : CollatzResearch.WordTrace tailWord_1695308 prefixEnd_1695308 870507861412558333353427 := by
  unfold tailWord_1695308
  simp only [CollatzResearch.WordTrace]
  refine ⟨30916481271098063200203289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41221975028130750933604385 30916481271098063200203289)
  ·
    refine ⟨23187360953323547400152467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30916481271098063200203289 23187360953323547400152467)
    ·
      refine ⟨34781041429985321100228701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23187360953323547400152467 34781041429985321100228701)
      ·
        refine ⟨13042890536244495412585763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34781041429985321100228701 13042890536244495412585763)
        ·
          refine ⟨19564335804366743118878645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13042890536244495412585763 19564335804366743118878645)
          ·
            refine ⟨1834156481659382167394873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19564335804366743118878645 1834156481659382167394873)
            ·
              refine ⟨1375617361244536625546155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834156481659382167394873 1375617361244536625546155)
              ·
                refine ⟨2063426041866804938319233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375617361244536625546155 2063426041866804938319233)
                ·
                  refine ⟨1547569531400103703739425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2063426041866804938319233 1547569531400103703739425)
                  ·
                    refine ⟨1160677148550077777804569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1547569531400103703739425 1160677148550077777804569)
                    ·
                      refine ⟨870507861412558333353427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160677148550077777804569 870507861412558333353427)
                      ·
                        rfl

theorem cell23_1695308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_1695308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695308 prefixEnd_1695308 := by exact prefixLift 1695308
  have htrace : WordTrace (prefixWord ++ tailWord_1695308) baseStart_1695308 baseEnd_1695308 := by
    simpa [prefixWord, tailWord_1695308, baseEnd_1695308] using wordTrace_append hprefix tailTrace_1695308
  have hstable : (prefixWord ++ tailWord_1695308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695308).length < 2 ^ (prefixWord ++ tailWord_1695308).sum := by decide
  have hdescent : baseEnd_1695308 < baseStart_1695308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695310 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_1695310 : Nat := 118140960795 + 1695310 * 2 ^ 59
def prefixEnd_1695310 : Nat := 4983230072969 + 3 ^ 40 * 1695310 * 2
def baseEnd_1695310 : Nat := 290169629457955775176139

theorem tailTrace_1695310 : CollatzResearch.WordTrace tailWord_1695310 prefixEnd_1695310 290169629457955775176139 := by
  unfold tailWord_1695310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729129436023610092747423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41222023658792587161319589 7729129436023610092747423)
  ·
    refine ⟨11593694154035415139121135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7729129436023610092747423 11593694154035415139121135)
    ·
      refine ⟨17390541231053122708681703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11593694154035415139121135 17390541231053122708681703)
      ·
        refine ⟨26085811846579684063022555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17390541231053122708681703 26085811846579684063022555)
        ·
          refine ⟨39128717769869526094533833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26085811846579684063022555 39128717769869526094533833)
          ·
            refine ⟨29346538327402144570900375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39128717769869526094533833 29346538327402144570900375)
            ·
              refine ⟨44019807491103216856350563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29346538327402144570900375 44019807491103216856350563)
              ·
                refine ⟨66029711236654825284525845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44019807491103216856350563 66029711236654825284525845)
                ·
                  refine ⟨3095142714218194935212149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66029711236654825284525845 3095142714218194935212149)
                  ·
                    refine ⟨290169629457955775176139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3095142714218194935212149 290169629457955775176139)
                    ·
                      rfl

theorem cell23_1695310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_1695310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695310 prefixEnd_1695310 := by exact prefixLift 1695310
  have htrace : WordTrace (prefixWord ++ tailWord_1695310) baseStart_1695310 baseEnd_1695310 := by
    simpa [prefixWord, tailWord_1695310, baseEnd_1695310] using wordTrace_append hprefix tailTrace_1695310
  have hstable : (prefixWord ++ tailWord_1695310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695310).length < 2 ^ (prefixWord ++ tailWord_1695310).sum := by decide
  have hdescent : baseEnd_1695310 < baseStart_1695310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695374 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_1695374 : Nat := 118140960795 + 1695374 * 2 ^ 59
def prefixEnd_1695374 : Nat := 4983230072969 + 3 ^ 40 * 1695374 * 2
def baseEnd_1695374 : Nat := 290180583711918358376041

theorem tailTrace_1695374 : CollatzResearch.WordTrace tailWord_1695374 prefixEnd_1695374 290180583711918358376041 := by
  unfold tailWord_1695374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729421219994627459038647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41223579839971346448206117 7729421219994627459038647)
  ·
    refine ⟨11594131829991941188557971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7729421219994627459038647 11594131829991941188557971)
    ·
      refine ⟨17391197744987911782836957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11594131829991941188557971 17391197744987911782836957)
      ·
        refine ⟨6521699154370466918563859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17391197744987911782836957 6521699154370466918563859)
        ·
          refine ⟨9782548731555700377845789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521699154370466918563859 9782548731555700377845789)
          ·
            refine ⟨3668455774333387641692171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9782548731555700377845789 3668455774333387641692171)
            ·
              refine ⟨5502683661500081462538257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668455774333387641692171 5502683661500081462538257)
              ·
                refine ⟨4127012746125061096903693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5502683661500081462538257 4127012746125061096903693)
                ·
                  refine ⟨1547629779796897911338885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4127012746125061096903693 1547629779796897911338885)
                  ·
                    refine ⟨290180583711918358376041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1547629779796897911338885 290180583711918358376041)
                    ·
                      rfl

theorem cell23_1695374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_1695374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695374 prefixEnd_1695374 := by exact prefixLift 1695374
  have htrace : WordTrace (prefixWord ++ tailWord_1695374) baseStart_1695374 baseEnd_1695374 := by
    simpa [prefixWord, tailWord_1695374, baseEnd_1695374] using wordTrace_append hprefix tailTrace_1695374
  have hstable : (prefixWord ++ tailWord_1695374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695374).length < 2 ^ (prefixWord ++ tailWord_1695374).sum := by decide
  have hdescent : baseEnd_1695374 < baseStart_1695374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695384 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1695384 : Nat := 118140960795 + 1695384 * 2 ^ 59
def prefixEnd_1695384 : Nat := 4983230072969 + 3 ^ 40 * 1695384 * 2
def baseEnd_1695384 : Nat := 870546885942300036003077

theorem tailTrace_1695384 : CollatzResearch.WordTrace tailWord_1695384 prefixEnd_1695384 870546885942300036003077 := by
  unfold tailWord_1695384
  simp only [CollatzResearch.WordTrace]
  refine ⟨30917867244960395690086603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41223822993280527586782137 30917867244960395690086603)
  ·
    refine ⟨46376800867440593535129905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30917867244960395690086603 46376800867440593535129905)
    ·
      refine ⟨34782600650580445151347429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46376800867440593535129905 34782600650580445151347429)
      ·
        refine ⟨6521737621983833465877643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34782600650580445151347429 6521737621983833465877643)
        ·
          refine ⟨9782606432975750198816465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521737621983833465877643 9782606432975750198816465)
          ·
            refine ⟨7336954824731812649112349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9782606432975750198816465 7336954824731812649112349)
            ·
              refine ⟨2751358059274429743417131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7336954824731812649112349 2751358059274429743417131)
              ·
                refine ⟨4127037088911644615125697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751358059274429743417131 4127037088911644615125697)
                ·
                  refine ⟨3095277816683733461344273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4127037088911644615125697 3095277816683733461344273)
                  ·
                    refine ⟨2321458362512800096008205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3095277816683733461344273 2321458362512800096008205)
                    ·
                      refine ⟨870546885942300036003077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2321458362512800096008205 870546885942300036003077)
                      ·
                        rfl

theorem cell23_1695384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1695384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695384 prefixEnd_1695384 := by exact prefixLift 1695384
  have htrace : WordTrace (prefixWord ++ tailWord_1695384) baseStart_1695384 baseEnd_1695384 := by
    simpa [prefixWord, tailWord_1695384, baseEnd_1695384] using wordTrace_append hprefix tailTrace_1695384
  have hstable : (prefixWord ++ tailWord_1695384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695384).length < 2 ^ (prefixWord ++ tailWord_1695384).sum := by decide
  have hdescent : baseEnd_1695384 < baseStart_1695384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695447 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 6, 4]
def baseStart_1695447 : Nat := 118140960795 + 1695447 * 2 ^ 59
def prefixEnd_1695447 : Nat := 4983230072969 + 3 ^ 40 * 1695447 * 2
def baseEnd_1695447 : Nat := 290193078407844429838429

theorem tailTrace_1695447 : CollatzResearch.WordTrace tailWord_1695447 prefixEnd_1695447 290193078407844429838429 := by
  unfold tailWord_1695447
  simp only [CollatzResearch.WordTrace]
  refine ⟨61838032288692553139716595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41225354859128368759811063 61838032288692553139716595)
  ·
    refine ⟨92757048433038829709574893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61838032288692553139716595 92757048433038829709574893)
    ·
      refine ⟨34783893162389561141090585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92757048433038829709574893 34783893162389561141090585)
      ·
        refine ⟨26087919871792170855817939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34783893162389561141090585 26087919871792170855817939)
        ·
          refine ⟨39131879807688256283726909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26087919871792170855817939 39131879807688256283726909)
          ·
            refine ⟨14674454927883096106397591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39131879807688256283726909 14674454927883096106397591)
            ·
              refine ⟨22011682391824644159596387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14674454927883096106397591 22011682391824644159596387)
              ·
                refine ⟨33017523587736966239394581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22011682391824644159596387 33017523587736966239394581)
                ·
                  refine ⟨1547696418175170292471621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33017523587736966239394581 1547696418175170292471621)
                  ·
                    refine ⟨290193078407844429838429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1547696418175170292471621 290193078407844429838429)
                    ·
                      rfl

theorem cell23_1695447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_1695447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695447 prefixEnd_1695447 := by exact prefixLift 1695447
  have htrace : WordTrace (prefixWord ++ tailWord_1695447) baseStart_1695447 baseEnd_1695447 := by
    simpa [prefixWord, tailWord_1695447, baseEnd_1695447] using wordTrace_append hprefix tailTrace_1695447
  have hstable : (prefixWord ++ tailWord_1695447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695447).length < 2 ^ (prefixWord ++ tailWord_1695447).sum := by decide
  have hdescent : baseEnd_1695447 < baseStart_1695447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695464 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 4, 4]
def baseStart_1695464 : Nat := 118140960795 + 1695464 * 2 ^ 59
def prefixEnd_1695464 : Nat := 4983230072969 + 3 ^ 40 * 1695464 * 2
def baseEnd_1695464 : Nat := 290195988131553241000903

theorem tailTrace_1695464 : CollatzResearch.WordTrace tailWord_1695464 prefixEnd_1695464 290195988131553241000903 := by
  unfold tailWord_1695464
  simp only [CollatzResearch.WordTrace]
  refine ⟨30919326164815482521542723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41225768219753976695390297 30919326164815482521542723)
  ·
    refine ⟨46378989247223223782314085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30919326164815482521542723 46378989247223223782314085)
    ·
      refine ⟨8696060483854354459183891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46378989247223223782314085 8696060483854354459183891)
      ·
        refine ⟨13044090725781531688775837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8696060483854354459183891 13044090725781531688775837)
        ·
          refine ⟨4891534022168074383290939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13044090725781531688775837 4891534022168074383290939)
          ·
            refine ⟨7337301033252111574936409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891534022168074383290939 7337301033252111574936409)
            ·
              refine ⟨5502975774939083681202307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7337301033252111574936409 5502975774939083681202307)
              ·
                refine ⟨8254463662408625521803461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5502975774939083681202307 8254463662408625521803461)
                ·
                  refine ⟨1547711936701617285338149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8254463662408625521803461 1547711936701617285338149)
                  ·
                    refine ⟨290195988131553241000903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1547711936701617285338149 290195988131553241000903)
                    ·
                      rfl

theorem cell23_1695464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_1695464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695464 prefixEnd_1695464 := by exact prefixLift 1695464
  have htrace : WordTrace (prefixWord ++ tailWord_1695464) baseStart_1695464 baseEnd_1695464 := by
    simpa [prefixWord, tailWord_1695464, baseEnd_1695464] using wordTrace_append hprefix tailTrace_1695464
  have hstable : (prefixWord ++ tailWord_1695464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695464).length < 2 ^ (prefixWord ++ tailWord_1695464).sum := by decide
  have hdescent : baseEnd_1695464 < baseStart_1695464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695474 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1695474 : Nat := 118140960795 + 1695474 * 2 ^ 59
def prefixEnd_1695474 : Nat := 4983230072969 + 3 ^ 40 * 1695474 * 2
def baseEnd_1695474 : Nat := 870593099201204683877663

theorem tailTrace_1695474 : CollatzResearch.WordTrace tailWord_1695474 prefixEnd_1695474 870593099201204683877663 := by
  unfold tailWord_1695474
  simp only [CollatzResearch.WordTrace]
  refine ⟨15459754264898684187737369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41226011373063157833966317 15459754264898684187737369)
  ·
    refine ⟨11594815698674013140803027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15459754264898684187737369 11594815698674013140803027)
    ·
      refine ⟨17392223548011019711204541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11594815698674013140803027 17392223548011019711204541)
      ·
        refine ⟨6522083830504132391701703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17392223548011019711204541 6522083830504132391701703)
        ·
          refine ⟨9783125745756198587552555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522083830504132391701703 9783125745756198587552555)
          ·
            refine ⟨14674688618634297881328833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9783125745756198587552555 14674688618634297881328833)
            ·
              refine ⟨11006016463975723410996625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14674688618634297881328833 11006016463975723410996625)
              ·
                refine ⟨8254512347981792558247469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11006016463975723410996625 8254512347981792558247469)
                ·
                  refine ⟨3095442130493172209342801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8254512347981792558247469 3095442130493172209342801)
                  ·
                    refine ⟨2321581597869879157007101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3095442130493172209342801 2321581597869879157007101)
                    ·
                      refine ⟨870593099201204683877663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2321581597869879157007101 870593099201204683877663)
                      ·
                        rfl

theorem cell23_1695474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1695474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695474 prefixEnd_1695474 := by exact prefixLift 1695474
  have htrace : WordTrace (prefixWord ++ tailWord_1695474) baseStart_1695474 baseEnd_1695474 := by
    simpa [prefixWord, tailWord_1695474, baseEnd_1695474] using wordTrace_append hprefix tailTrace_1695474
  have hstable : (prefixWord ++ tailWord_1695474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695474).length < 2 ^ (prefixWord ++ tailWord_1695474).sum := by decide
  have hdescent : baseEnd_1695474 < baseStart_1695474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695521 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_1695521 : Nat := 118140960795 + 1695521 * 2 ^ 59
def prefixEnd_1695521 : Nat := 4983230072969 + 3 ^ 40 * 1695521 * 2
def baseEnd_1695521 : Nat := 870617232791965999989947

theorem tailTrace_1695521 : CollatzResearch.WordTrace tailWord_1695521 prefixEnd_1695521 870617232791965999989947 := by
  unfold tailWord_1695521
  simp only [CollatzResearch.WordTrace]
  refine ⟨61840731290424463777910417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41227154193616309185273611 61840731290424463777910417)
  ·
    refine ⟨46380548467818347833432813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61840731290424463777910417 46380548467818347833432813)
    ·
      refine ⟨17392705675431880437537305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46380548467818347833432813 17392705675431880437537305)
      ·
        refine ⟨13044529256573910328152979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17392705675431880437537305 13044529256573910328152979)
        ·
          refine ⟨19566793884860865492229469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13044529256573910328152979 19566793884860865492229469)
          ·
            refine ⟨7337547706822824559586051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19566793884860865492229469 7337547706822824559586051)
            ·
              refine ⟨11006321560234236839379077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337547706822824559586051 11006321560234236839379077)
              ·
                refine ⟨2063685292543919407383577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11006321560234236839379077 2063685292543919407383577)
                ·
                  refine ⟨1547763969407939555537683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2063685292543919407383577 1547763969407939555537683)
                  ·
                    refine ⟨2321645954111909333306525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1547763969407939555537683 2321645954111909333306525)
                    ·
                      refine ⟨870617232791965999989947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2321645954111909333306525 870617232791965999989947)
                      ·
                        rfl

theorem cell23_1695521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_1695521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695521 prefixEnd_1695521 := by exact prefixLift 1695521
  have htrace : WordTrace (prefixWord ++ tailWord_1695521) baseStart_1695521 baseEnd_1695521 := by
    simpa [prefixWord, tailWord_1695521, baseEnd_1695521] using wordTrace_append hprefix tailTrace_1695521
  have hstable : (prefixWord ++ tailWord_1695521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695521).length < 2 ^ (prefixWord ++ tailWord_1695521).sum := by decide
  have hdescent : baseEnd_1695521 < baseStart_1695521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695537 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 1, 8]
def baseStart_1695537 : Nat := 118140960795 + 1695537 * 2 ^ 59
def prefixEnd_1695537 : Nat := 4983230072969 + 3 ^ 40 * 1695537 * 2
def baseEnd_1695537 : Nat := 290208482827479312463291

theorem tailTrace_1695537 : CollatzResearch.WordTrace tailWord_1695537 prefixEnd_1695537 290208482827479312463291 := by
  unfold tailWord_1695537
  simp only [CollatzResearch.WordTrace]
  refine ⟨61841314858366498510492865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41227543238910999006995243 61841314858366498510492865)
  ·
    refine ⟨46380986143774873882869649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61841314858366498510492865 46380986143774873882869649)
    ·
      refine ⟨34785739607831155412152237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46380986143774873882869649 34785739607831155412152237)
      ·
        refine ⟨13044652352936683279557089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34785739607831155412152237 13044652352936683279557089)
        ·
          refine ⟨9783489264702512459667817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13044652352936683279557089 9783489264702512459667817)
          ·
            refine ⟨7337616948526884344750863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9783489264702512459667817 7337616948526884344750863)
            ·
              refine ⟨11006425422790326517126295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337616948526884344750863 11006425422790326517126295)
              ·
                refine ⟨16509638134185489775689443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11006425422790326517126295 16509638134185489775689443)
                ·
                  refine ⟨24764457201278234663534165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16509638134185489775689443 24764457201278234663534165)
                  ·
                    refine ⟨290208482827479312463291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24764457201278234663534165 290208482827479312463291)
                    ·
                      rfl

theorem cell23_1695537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_1695537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695537 prefixEnd_1695537 := by exact prefixLift 1695537
  have htrace : WordTrace (prefixWord ++ tailWord_1695537) baseStart_1695537 baseEnd_1695537 := by
    simpa [prefixWord, tailWord_1695537, baseEnd_1695537] using wordTrace_append hprefix tailTrace_1695537
  have hstable : (prefixWord ++ tailWord_1695537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695537).length < 2 ^ (prefixWord ++ tailWord_1695537).sum := by decide
  have hdescent : baseEnd_1695537 < baseStart_1695537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695557 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_1695557 : Nat := 118140960795 + 1695557 * 2 ^ 59
def prefixEnd_1695557 : Nat := 4983230072969 + 3 ^ 40 * 1695557 * 2
def baseEnd_1695557 : Nat := 870635718095527859139781

theorem tailTrace_1695557 : CollatzResearch.WordTrace tailWord_1695557 prefixEnd_1695557 870635718095527859139781 := by
  unfold tailWord_1695557
  simp only [CollatzResearch.WordTrace]
  refine ⟨61842044318294041926220925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41228029545529361284147283 61842044318294041926220925)
  ·
    refine ⟨23190766619360265722332847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61842044318294041926220925 23190766619360265722332847)
    ·
      refine ⟨34786149929040398583499271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23190766619360265722332847 34786149929040398583499271)
      ·
        refine ⟨52179224893560597875248907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34786149929040398583499271 52179224893560597875248907)
        ·
          refine ⟨78268837340340896812873361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52179224893560597875248907 78268837340340896812873361)
          ·
            refine ⟨58701628005255672609655021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78268837340340896812873361 58701628005255672609655021)
            ·
              refine ⟨22013110501970877228620633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58701628005255672609655021 22013110501970877228620633)
              ·
                refine ⟨16509832876478157921465475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22013110501970877228620633 16509832876478157921465475)
                ·
                  refine ⟨24764749314717236882198213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16509832876478157921465475 24764749314717236882198213)
                  ·
                    refine ⟨4643390496509481915412165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24764749314717236882198213 4643390496509481915412165)
                    ·
                      refine ⟨870635718095527859139781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4643390496509481915412165 870635718095527859139781)
                      ·
                        rfl

theorem cell23_1695557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_1695557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695557 prefixEnd_1695557 := by exact prefixLift 1695557
  have htrace : WordTrace (prefixWord ++ tailWord_1695557) baseStart_1695557 baseEnd_1695557 := by
    simpa [prefixWord, tailWord_1695557, baseEnd_1695557] using wordTrace_append hprefix tailTrace_1695557
  have hstable : (prefixWord ++ tailWord_1695557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695557).length < 2 ^ (prefixWord ++ tailWord_1695557).sum := by decide
  have hdescent : baseEnd_1695557 < baseStart_1695557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695561 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 4, 2, 2]
def baseStart_1695561 : Nat := 118140960795 + 1695561 * 2 ^ 59
def prefixEnd_1695561 : Nat := 4983230072969 + 3 ^ 40 * 1695561 * 2
def baseEnd_1695561 : Nat := 870637772018145843489763

theorem tailTrace_1695561 : CollatzResearch.WordTrace tailWord_1695561 prefixEnd_1695561 870637772018145843489763 := by
  unfold tailWord_1695561
  simp only [CollatzResearch.WordTrace]
  refine ⟨61842190210279550609366537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41228126806853033739577691 61842190210279550609366537)
  ·
    refine ⟨46381642657709662957024903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61842190210279550609366537 46381642657709662957024903)
    ·
      refine ⟨69572463986564494435537355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46381642657709662957024903 69572463986564494435537355)
      ·
        refine ⟨104358695979846741653306033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69572463986564494435537355 104358695979846741653306033)
        ·
          refine ⟨78269021984885056239979525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104358695979846741653306033 78269021984885056239979525)
          ·
            refine ⟨14675441622165948044996161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78269021984885056239979525 14675441622165948044996161)
            ·
              refine ⟨11006581216624461033747121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14675441622165948044996161 11006581216624461033747121)
              ·
                refine ⟨8254935912468345775310341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11006581216624461033747121 8254935912468345775310341)
                ·
                  refine ⟨1547800483587814832870689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8254935912468345775310341 1547800483587814832870689)
                  ·
                    refine ⟨1160850362690861124653017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1547800483587814832870689 1160850362690861124653017)
                    ·
                      refine ⟨870637772018145843489763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160850362690861124653017 870637772018145843489763)
                      ·
                        rfl

theorem cell23_1695561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 2, 2].length) (baseStart_1695561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695561 prefixEnd_1695561 := by exact prefixLift 1695561
  have htrace : WordTrace (prefixWord ++ tailWord_1695561) baseStart_1695561 baseEnd_1695561 := by
    simpa [prefixWord, tailWord_1695561, baseEnd_1695561] using wordTrace_append hprefix tailTrace_1695561
  have hstable : (prefixWord ++ tailWord_1695561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695561).length < 2 ^ (prefixWord ++ tailWord_1695561).sum := by decide
  have hdescent : baseEnd_1695561 < baseStart_1695561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695565 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_1695565 : Nat := 118140960795 + 1695565 * 2 ^ 59
def prefixEnd_1695565 : Nat := 4983230072969 + 3 ^ 40 * 1695565 * 2
def baseEnd_1695565 : Nat := 870639825940763827839745

theorem tailTrace_1695565 : CollatzResearch.WordTrace tailWord_1695565 prefixEnd_1695565 870639825940763827839745 := by
  unfold tailWord_1695565
  simp only [CollatzResearch.WordTrace]
  refine ⟨61842336102265059292512149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41228224068176706195008099 61842336102265059292512149)
  ·
    refine ⟨2898859504793674654336507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61842336102265059292512149 2898859504793674654336507)
    ·
      refine ⟨4348289257190511981504761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2898859504793674654336507 4348289257190511981504761)
      ·
        refine ⟨3261216942892883986128571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4348289257190511981504761 3261216942892883986128571)
        ·
          refine ⟨4891825414339325979192857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261216942892883986128571 4891825414339325979192857)
          ·
            refine ⟨3668869060754494484394643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4891825414339325979192857 3668869060754494484394643)
            ·
              refine ⟨5503303591131741726591965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668869060754494484394643 5503303591131741726591965)
              ·
                refine ⟨2063738846674403147471987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5503303591131741726591965 2063738846674403147471987)
                ·
                  refine ⟨3095608270011604721207981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063738846674403147471987 3095608270011604721207981)
                  ·
                    refine ⟨1160853101254351770452993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095608270011604721207981 1160853101254351770452993)
                    ·
                      refine ⟨870639825940763827839745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160853101254351770452993 870639825940763827839745)
                      ·
                        rfl

theorem cell23_1695565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_1695565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695565 prefixEnd_1695565 := by exact prefixLift 1695565
  have htrace : WordTrace (prefixWord ++ tailWord_1695565) baseStart_1695565 baseEnd_1695565 := by
    simpa [prefixWord, tailWord_1695565, baseEnd_1695565] using wordTrace_append hprefix tailTrace_1695565
  have hstable : (prefixWord ++ tailWord_1695565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695565).length < 2 ^ (prefixWord ++ tailWord_1695565).sum := by decide
  have hdescent : baseEnd_1695565 < baseStart_1695565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695584 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 7]
def baseStart_1695584 : Nat := 118140960795 + 1695584 * 2 ^ 59
def prefixEnd_1695584 : Nat := 4983230072969 + 3 ^ 40 * 1695584 * 2
def baseEnd_1695584 : Nat := 96738842452577694833573

theorem tailTrace_1695584 : CollatzResearch.WordTrace tailWord_1695584 prefixEnd_1695584 96738842452577694833573 := by
  unfold tailWord_1695584
  simp only [CollatzResearch.WordTrace]
  refine ⟨30921514544598112768726903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41228686059464150358302537 30921514544598112768726903)
  ·
    refine ⟨46382271816897169153090355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30921514544598112768726903 46382271816897169153090355)
    ·
      refine ⟨69573407725345753729635533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46382271816897169153090355 69573407725345753729635533)
      ·
        refine ⟨26090027897004657648613325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69573407725345753729635533 26090027897004657648613325)
        ·
          refine ⟨9783760461376746618229997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26090027897004657648613325 9783760461376746618229997)
          ·
            refine ⟨3668910173016279981836249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9783760461376746618229997 3668910173016279981836249)
            ·
              refine ⟨2751682629762209986377187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668910173016279981836249 2751682629762209986377187)
              ·
                refine ⟨4127523944643314979565781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751682629762209986377187 4127523944643314979565781)
                ·
                  refine ⟨96738842452577694833573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4127523944643314979565781 96738842452577694833573)
                  ·
                    rfl

theorem cell23_1695584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 7].length) (baseStart_1695584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695584 prefixEnd_1695584 := by exact prefixLift 1695584
  have htrace : WordTrace (prefixWord ++ tailWord_1695584) baseStart_1695584 baseEnd_1695584 := by
    simpa [prefixWord, tailWord_1695584, baseEnd_1695584] using wordTrace_append hprefix tailTrace_1695584
  have hstable : (prefixWord ++ tailWord_1695584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695584).length < 2 ^ (prefixWord ++ tailWord_1695584).sum := by decide
  have hdescent : baseEnd_1695584 < baseStart_1695584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695607 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_1695607 : Nat := 118140960795 + 1695607 * 2 ^ 59
def prefixEnd_1695607 : Nat := 4983230072969 + 3 ^ 40 * 1695607 * 2
def baseEnd_1695607 : Nat := 870661392128252663514551

theorem tailTrace_1695607 : CollatzResearch.WordTrace tailWord_1695607 prefixEnd_1695607 870661392128252663514551 := by
  unfold tailWord_1695607
  simp only [CollatzResearch.WordTrace]
  refine ⟨61843867968112900465541075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41229245312075266977027383 61843867968112900465541075)
  ·
    refine ⟨92765801952169350698311613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61843867968112900465541075 92765801952169350698311613)
    ·
      refine ⟨34787175732063506511866855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92765801952169350698311613 34787175732063506511866855)
      ·
        refine ⟨52180763598095259767800283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34787175732063506511866855 52180763598095259767800283)
        ·
          refine ⟨78271145397142889651700425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52180763598095259767800283 78271145397142889651700425)
          ·
            refine ⟨58703359047857167238775319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78271145397142889651700425 58703359047857167238775319)
            ·
              refine ⟨88055038571785750858162979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58703359047857167238775319 88055038571785750858162979)
              ·
                refine ⟨132082557857678626287244469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88055038571785750858162979 132082557857678626287244469)
                ·
                  refine ⟨12382739799157371214429169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132082557857678626287244469 12382739799157371214429169)
                  ·
                    refine ⟨9287054849368028410821877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12382739799157371214429169 9287054849368028410821877)
                    ·
                      refine ⟨870661392128252663514551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9287054849368028410821877 870661392128252663514551)
                      ·
                        rfl

theorem cell23_1695607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_1695607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695607 prefixEnd_1695607 := by exact prefixLift 1695607
  have htrace : WordTrace (prefixWord ++ tailWord_1695607) baseStart_1695607 baseEnd_1695607 := by
    simpa [prefixWord, tailWord_1695607, baseEnd_1695607] using wordTrace_append hprefix tailTrace_1695607
  have hstable : (prefixWord ++ tailWord_1695607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695607).length < 2 ^ (prefixWord ++ tailWord_1695607).sum := by decide
  have hdescent : baseEnd_1695607 < baseStart_1695607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695646 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1695646 : Nat := 118140960795 + 1695646 * 2 ^ 59
def prefixEnd_1695646 : Nat := 4983230072969 + 3 ^ 40 * 1695646 * 2
def baseEnd_1695646 : Nat := 870681417873778010926873

theorem tailTrace_1695646 : CollatzResearch.WordTrace tailWord_1695646 prefixEnd_1695646 870681417873778010926873 := by
  unfold tailWord_1695646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7730661301871451265776349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41230193609981073417473861 7730661301871451265776349)
  ·
    refine ⟨2898997988201794224666131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7730661301871451265776349 2898997988201794224666131)
    ·
      refine ⟨4348496982302691336999197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2898997988201794224666131 4348496982302691336999197)
      ·
        refine ⟨1630686368363509251374699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4348496982302691336999197 1630686368363509251374699)
        ·
          refine ⟨2446029552545263877062049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1630686368363509251374699 2446029552545263877062049)
          ·
            refine ⟨1834522164408947907796537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2446029552545263877062049 1834522164408947907796537)
            ·
              refine ⟨1375891623306710930847403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834522164408947907796537 1375891623306710930847403)
              ·
                refine ⟨2063837434960066396271105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375891623306710930847403 2063837434960066396271105)
                ·
                  refine ⟨1547878076220049797203329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2063837434960066396271105 1547878076220049797203329)
                  ·
                    refine ⟨1160908557165037347902497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1547878076220049797203329 1160908557165037347902497)
                    ·
                      refine ⟨870681417873778010926873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160908557165037347902497 870681417873778010926873)
                      ·
                        rfl

theorem cell23_1695646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1695646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695646 prefixEnd_1695646 := by exact prefixLift 1695646
  have htrace : WordTrace (prefixWord ++ tailWord_1695646) baseStart_1695646 baseEnd_1695646 := by
    simpa [prefixWord, tailWord_1695646, baseEnd_1695646] using wordTrace_append hprefix tailTrace_1695646
  have hstable : (prefixWord ++ tailWord_1695646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695646).length < 2 ^ (prefixWord ++ tailWord_1695646).sum := by decide
  have hdescent : baseEnd_1695646 < baseStart_1695646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695657 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 10]
def baseStart_1695657 : Nat := 118140960795 + 1695657 * 2 ^ 59
def prefixEnd_1695657 : Nat := 4983230072969 + 3 ^ 40 * 1695657 * 2
def baseEnd_1695657 : Nat := 96743007351219718654369

theorem tailTrace_1695657 : CollatzResearch.WordTrace tailWord_1695657 prefixEnd_1695657 96743007351219718654369 := by
  unfold tailWord_1695657
  simp only [CollatzResearch.WordTrace]
  refine ⟨61845691617931759004861225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41230461078621172669907483 61845691617931759004861225)
  ·
    refine ⟨46384268713448819253645919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61845691617931759004861225 46384268713448819253645919)
    ·
      refine ⟨69576403070173228880468879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46384268713448819253645919 69576403070173228880468879)
      ·
        refine ⟨104364604605259843320703319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69576403070173228880468879 104364604605259843320703319)
        ·
          refine ⟨156546906907889764981054979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104364604605259843320703319 156546906907889764981054979)
          ·
            refine ⟨234820360361834647471582469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156546906907889764981054979 234820360361834647471582469)
            ·
              refine ⟨44028817567843996400921713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234820360361834647471582469 44028817567843996400921713)
              ·
                refine ⟨33021613175882997300691285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44028817567843996400921713 33021613175882997300691285)
                ·
                  refine ⟨96743007351219718654369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 33021613175882997300691285 96743007351219718654369)
                  ·
                    rfl

theorem cell23_1695657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 10].length) (baseStart_1695657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695657 prefixEnd_1695657 := by exact prefixLift 1695657
  have htrace : WordTrace (prefixWord ++ tailWord_1695657) baseStart_1695657 baseEnd_1695657 := by
    simpa [prefixWord, tailWord_1695657, baseEnd_1695657] using wordTrace_append hprefix tailTrace_1695657
  have hstable : (prefixWord ++ tailWord_1695657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695657).length < 2 ^ (prefixWord ++ tailWord_1695657).sum := by decide
  have hdescent : baseEnd_1695657 < baseStart_1695657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695694 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1695694 : Nat := 118140960795 + 1695694 * 2 ^ 59
def prefixEnd_1695694 : Nat := 4983230072969 + 3 ^ 40 * 1695694 * 2
def baseEnd_1695694 : Nat := 870706064945193823126651

theorem tailTrace_1695694 : CollatzResearch.WordTrace tailWord_1695694 prefixEnd_1695694 870706064945193823126651 := by
  unfold tailWord_1695694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7730880139849714290494767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41231360745865142882638757 7730880139849714290494767)
  ·
    refine ⟨11596320209774571435742151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7730880139849714290494767 11596320209774571435742151)
    ·
      refine ⟨17394480314661857153613227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11596320209774571435742151 17394480314661857153613227)
      ·
        refine ⟨26091720471992785730419841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17394480314661857153613227 26091720471992785730419841)
        ·
          refine ⟨19568790353994589297814881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26091720471992785730419841 19568790353994589297814881)
          ·
            refine ⟨14676592765495941973361161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19568790353994589297814881 14676592765495941973361161)
            ·
              refine ⟨11007444574121956480020871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14676592765495941973361161 11007444574121956480020871)
              ·
                refine ⟨16511166861182934720031307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11007444574121956480020871 16511166861182934720031307)
                ·
                  refine ⟨24766750291774402080046961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16511166861182934720031307 24766750291774402080046961)
                  ·
                    refine ⟨18575062718830801560035221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24766750291774402080046961 18575062718830801560035221)
                    ·
                      refine ⟨870706064945193823126651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18575062718830801560035221 870706064945193823126651)
                      ·
                        rfl

theorem cell23_1695694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1695694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695694 prefixEnd_1695694 := by exact prefixLift 1695694
  have htrace : WordTrace (prefixWord ++ tailWord_1695694) baseStart_1695694 baseEnd_1695694 := by
    simpa [prefixWord, tailWord_1695694, baseEnd_1695694] using wordTrace_append hprefix tailTrace_1695694
  have hstable : (prefixWord ++ tailWord_1695694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695694).length < 2 ^ (prefixWord ++ tailWord_1695694).sum := by decide
  have hdescent : baseEnd_1695694 < baseStart_1695694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695704 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 5, 5]
def baseStart_1695704 : Nat := 118140960795 + 1695704 * 2 ^ 59
def prefixEnd_1695704 : Nat := 4983230072969 + 3 ^ 40 * 1695704 * 2
def baseEnd_1695704 : Nat := 290237066583912928000535

theorem tailTrace_1695704 : CollatzResearch.WordTrace tailWord_1695704 prefixEnd_1695704 290237066583912928000535 := by
  unfold tailWord_1695704
  simp only [CollatzResearch.WordTrace]
  refine ⟨30923702924380743015911083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41231603899174324021214777 30923702924380743015911083)
  ·
    refine ⟨46385554386571114523866625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30923702924380743015911083 46385554386571114523866625)
    ·
      refine ⟨34789165789928335892899969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46385554386571114523866625 34789165789928335892899969)
      ·
        refine ⟨26091874342446251919674977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34789165789928335892899969 26091874342446251919674977)
        ·
          refine ⟨19568905756834688939756233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26091874342446251919674977 19568905756834688939756233)
          ·
            refine ⟨14676679317626016704817175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19568905756834688939756233 14676679317626016704817175)
            ·
              refine ⟨22015018976439025057225763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14676679317626016704817175 22015018976439025057225763)
              ·
                refine ⟨33022528464658537585838645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22015018976439025057225763 33022528464658537585838645)
                ·
                  refine ⟨3095862043561737898672373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33022528464658537585838645 3095862043561737898672373)
                  ·
                    refine ⟨290237066583912928000535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3095862043561737898672373 290237066583912928000535)
                    ·
                      rfl

theorem cell23_1695704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_1695704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695704 prefixEnd_1695704 := by exact prefixLift 1695704
  have htrace : WordTrace (prefixWord ++ tailWord_1695704) baseStart_1695704 baseEnd_1695704 := by
    simpa [prefixWord, tailWord_1695704, baseEnd_1695704] using wordTrace_append hprefix tailTrace_1695704
  have hstable : (prefixWord ++ tailWord_1695704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695704).length < 2 ^ (prefixWord ++ tailWord_1695704).sum := by decide
  have hdescent : baseEnd_1695704 < baseStart_1695704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695728 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 2, 3, 2]
def baseStart_1695728 : Nat := 118140960795 + 1695728 * 2 ^ 59
def prefixEnd_1695728 : Nat := 4983230072969 + 3 ^ 40 * 1695728 * 2
def baseEnd_1695728 : Nat := 870723523287446690101495

theorem tailTrace_1695728 : CollatzResearch.WordTrace tailWord_1695728 prefixEnd_1695728 870723523287446690101495 := by
  unfold tailWord_1695728
  simp only [CollatzResearch.WordTrace]
  refine ⟨30924140600337269065347919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41232187467116358753797225 30924140600337269065347919)
  ·
    refine ⟨46386210900505903598021879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30924140600337269065347919 46386210900505903598021879)
    ·
      refine ⟨69579316350758855397032819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46386210900505903598021879 69579316350758855397032819)
      ·
        refine ⟨104368974526138283095549229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69579316350758855397032819 104368974526138283095549229)
        ·
          refine ⟨39138365447301856160830961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104368974526138283095549229 39138365447301856160830961)
          ·
            refine ⟨29353774085476392120623221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39138365447301856160830961 29353774085476392120623221)
            ·
              refine ⟨2751916320513411761308427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29353774085476392120623221 2751916320513411761308427)
              ·
                refine ⟨4127874480770117641962641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751916320513411761308427 4127874480770117641962641)
                ·
                  refine ⟨3095905860577588231471981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4127874480770117641962641 3095905860577588231471981)
                  ·
                    refine ⟨1160964697716595586801993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095905860577588231471981 1160964697716595586801993)
                    ·
                      refine ⟨870723523287446690101495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1160964697716595586801993 870723523287446690101495)
                      ·
                        rfl

theorem cell23_1695728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 3, 2].length) (baseStart_1695728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695728 prefixEnd_1695728 := by exact prefixLift 1695728
  have htrace : WordTrace (prefixWord ++ tailWord_1695728) baseStart_1695728 baseEnd_1695728 := by
    simpa [prefixWord, tailWord_1695728, baseEnd_1695728] using wordTrace_append hprefix tailTrace_1695728
  have hstable : (prefixWord ++ tailWord_1695728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695728).length < 2 ^ (prefixWord ++ tailWord_1695728).sum := by decide
  have hdescent : baseEnd_1695728 < baseStart_1695728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695781 : List Nat := [1, 3, 1, 2, 2, 3, 4, 7]
def baseStart_1695781 : Nat := 118140960795 + 1695781 * 2 ^ 59
def prefixEnd_1695781 : Nat := 4983230072969 + 3 ^ 40 * 1695781 * 2
def baseEnd_1695781 : Nat := 32250027324523517879213

theorem tailTrace_1695781 : CollatzResearch.WordTrace tailWord_1695781 prefixEnd_1695781 32250027324523517879213 := by
  unfold tailWord_1695781
  simp only [CollatzResearch.WordTrace]
  refine ⟨61850214269482528182375197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41233476179655018788250131 61850214269482528182375197)
  ·
    refine ⟨23193830351055948068390699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61850214269482528182375197 23193830351055948068390699)
    ·
      refine ⟨34790745526583922102586049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23193830351055948068390699 34790745526583922102586049)
      ·
        refine ⟨26093059144937941576939537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34790745526583922102586049 26093059144937941576939537)
        ·
          refine ⟨19569794358703456182704653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26093059144937941576939537 19569794358703456182704653)
          ·
            refine ⟨7338672884513796068514245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19569794358703456182704653 7338672884513796068514245)
            ·
              refine ⟨1376001165846336762846421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7338672884513796068514245 1376001165846336762846421)
              ·
                refine ⟨32250027324523517879213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1376001165846336762846421 32250027324523517879213)
                ·
                  rfl

theorem cell23_1695781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 7].length) (baseStart_1695781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695781 prefixEnd_1695781 := by exact prefixLift 1695781
  have htrace : WordTrace (prefixWord ++ tailWord_1695781) baseStart_1695781 baseEnd_1695781 := by
    simpa [prefixWord, tailWord_1695781, baseEnd_1695781] using wordTrace_append hprefix tailTrace_1695781
  have hstable : (prefixWord ++ tailWord_1695781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695781).length < 2 ^ (prefixWord ++ tailWord_1695781).sum := by decide
  have hdescent : baseEnd_1695781 < baseStart_1695781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695792 : List Nat := [2, 1, 1, 1, 2, 5, 3, 3, 1, 2, 2]
def baseStart_1695792 : Nat := 118140960795 + 1695792 * 2 ^ 59
def prefixEnd_1695792 : Nat := 4983230072969 + 3 ^ 40 * 1695792 * 2
def baseEnd_1695792 : Nat := 870756386049334439701201

theorem tailTrace_1695792 : CollatzResearch.WordTrace tailWord_1695792 prefixEnd_1695792 870756386049334439701201 := by
  unfold tailWord_1695792
  simp only [CollatzResearch.WordTrace]
  refine ⟨30925307736221338530512815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41233743648295118040683753 30925307736221338530512815)
  ·
    refine ⟨46387961604332007795769223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30925307736221338530512815 46387961604332007795769223)
    ·
      refine ⟨69581942406498011693653835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46387961604332007795769223 69581942406498011693653835)
      ·
        refine ⟨104372913609747017540480753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69581942406498011693653835 104372913609747017540480753)
        ·
          refine ⟨78279685207310263155360565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104372913609747017540480753 78279685207310263155360565)
          ·
            refine ⟨7338720488185337170815053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78279685207310263155360565 7338720488185337170815053)
            ·
              refine ⟨2752020183069501439055645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7338720488185337170815053 2752020183069501439055645)
              ·
                refine ⟨1032007568651063039645867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2752020183069501439055645 1032007568651063039645867)
                ·
                  refine ⟨1548011352976594559468801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032007568651063039645867 1548011352976594559468801)
                  ·
                    refine ⟨1161008514732445919601601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1548011352976594559468801 1161008514732445919601601)
                    ·
                      refine ⟨870756386049334439701201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161008514732445919601601 870756386049334439701201)
                      ·
                        rfl

theorem cell23_1695792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 2, 2].length) (baseStart_1695792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695792 prefixEnd_1695792 := by exact prefixLift 1695792
  have htrace : WordTrace (prefixWord ++ tailWord_1695792) baseStart_1695792 baseEnd_1695792 := by
    simpa [prefixWord, tailWord_1695792, baseEnd_1695792] using wordTrace_append hprefix tailTrace_1695792
  have hstable : (prefixWord ++ tailWord_1695792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695792).length < 2 ^ (prefixWord ++ tailWord_1695792).sum := by decide
  have hdescent : baseEnd_1695792 < baseStart_1695792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695808 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 4, 1, 3]
def baseStart_1695808 : Nat := 118140960795 + 1695808 * 2 ^ 59
def prefixEnd_1695808 : Nat := 4983230072969 + 3 ^ 40 * 1695808 * 2
def baseEnd_1695808 : Nat := 870764601739806377101127

theorem tailTrace_1695808 : CollatzResearch.WordTrace tailWord_1695808 prefixEnd_1695808 870764601739806377101127 := by
  unfold tailWord_1695808
  simp only [CollatzResearch.WordTrace]
  refine ⟨30925599520192355896804039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41234132693589807862405385 30925599520192355896804039)
  ·
    refine ⟨46388399280288533845206059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30925599520192355896804039 46388399280288533845206059)
    ·
      refine ⟨69582598920432800767809089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46388399280288533845206059 69582598920432800767809089)
      ·
        refine ⟨52186949190324600575856817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69582598920432800767809089 52186949190324600575856817)
        ·
          refine ⟨39140211892743450431892613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52186949190324600575856817 39140211892743450431892613)
          ·
            refine ⟨7338789729889396955979865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39140211892743450431892613 7338789729889396955979865)
            ·
              refine ⟨5504092297417047716984899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7338789729889396955979865 5504092297417047716984899)
              ·
                refine ⟨8256138446125571575477349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5504092297417047716984899 8256138446125571575477349)
                ·
                  refine ⟨1548025958648544670402003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8256138446125571575477349 1548025958648544670402003)
                  ·
                    refine ⟨2322038937972817005603005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1548025958648544670402003 2322038937972817005603005)
                    ·
                      refine ⟨870764601739806377101127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2322038937972817005603005 870764601739806377101127)
                      ·
                        rfl

theorem cell23_1695808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_1695808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695808 prefixEnd_1695808 := by exact prefixLift 1695808
  have htrace : WordTrace (prefixWord ++ tailWord_1695808) baseStart_1695808 baseEnd_1695808 := by
    simpa [prefixWord, tailWord_1695808, baseEnd_1695808] using wordTrace_append hprefix tailTrace_1695808
  have hstable : (prefixWord ++ tailWord_1695808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695808).length < 2 ^ (prefixWord ++ tailWord_1695808).sum := by decide
  have hdescent : baseEnd_1695808 < baseStart_1695808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695818 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_1695818 : Nat := 118140960795 + 1695818 * 2 ^ 59
def prefixEnd_1695818 : Nat := 4983230072969 + 3 ^ 40 * 1695818 * 2
def baseEnd_1695818 : Nat := 870769736546351337976081

theorem tailTrace_1695818 : CollatzResearch.WordTrace tailWord_1695818 prefixEnd_1695818 870769736546351337976081 := by
  unfold tailWord_1695818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15462890942587120875368027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41234375846898989000981405 15462890942587120875368027)
  ·
    refine ⟨23194336413880681313052041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15462890942587120875368027 23194336413880681313052041)
    ·
      refine ⟨17395752310410510984789031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23194336413880681313052041 17395752310410510984789031)
      ·
        refine ⟨26093628465615766477183547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17395752310410510984789031 26093628465615766477183547)
        ·
          refine ⟨39140442698423649715775321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26093628465615766477183547 39140442698423649715775321)
          ·
            refine ⟨29355332023817737286831491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39140442698423649715775321 29355332023817737286831491)
            ·
              refine ⟨44032998035726605930247237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29355332023817737286831491 44032998035726605930247237)
              ·
                refine ⟨8256187131698738611921357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44032998035726605930247237 8256187131698738611921357)
                ·
                  refine ⟨3096070174387026979470509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8256187131698738611921357 3096070174387026979470509)
                  ·
                    refine ⟨1161026315395135117301441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096070174387026979470509 1161026315395135117301441)
                    ·
                      refine ⟨870769736546351337976081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161026315395135117301441 870769736546351337976081)
                      ·
                        rfl

theorem cell23_1695818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_1695818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695818 prefixEnd_1695818 := by exact prefixLift 1695818
  have htrace : WordTrace (prefixWord ++ tailWord_1695818) baseStart_1695818 baseEnd_1695818 := by
    simpa [prefixWord, tailWord_1695818, baseEnd_1695818] using wordTrace_append hprefix tailTrace_1695818
  have hstable : (prefixWord ++ tailWord_1695818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695818).length < 2 ^ (prefixWord ++ tailWord_1695818).sum := by decide
  have hdescent : baseEnd_1695818 < baseStart_1695818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695852 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 1, 3, 2]
def baseStart_1695852 : Nat := 118140960795 + 1695852 * 2 ^ 59
def prefixEnd_1695852 : Nat := 4983230072969 + 3 ^ 40 * 1695852 * 2
def baseEnd_1695852 : Nat := 870787194888604204950925

theorem tailTrace_1695852 : CollatzResearch.WordTrace tailWord_1695852 prefixEnd_1695852 870787194888604204950925 := by
  unfold tailWord_1695852
  simp only [CollatzResearch.WordTrace]
  refine ⟨30926401926112653654104905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41235202568150204872139873 30926401926112653654104905)
  ·
    refine ⟨23194801444584490240578679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30926401926112653654104905 23194801444584490240578679)
    ·
      refine ⟨34792202166876735360868019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23194801444584490240578679 34792202166876735360868019)
      ·
        refine ⟨52188303250315103041302029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34792202166876735360868019 52188303250315103041302029)
        ·
          refine ⟨19570613718868163640488261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52188303250315103041302029 19570613718868163640488261)
          ·
            refine ⟨3669490072287780682591549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19570613718868163640488261 3669490072287780682591549)
            ·
              refine ⟨1376058777107917755971831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3669490072287780682591549 1376058777107917755971831)
              ·
                refine ⟨2064088165661876633957747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376058777107917755971831 2064088165661876633957747)
                ·
                  refine ⟨3096132248492814950936621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064088165661876633957747 3096132248492814950936621)
                  ·
                    refine ⟨1161049593184805606601233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096132248492814950936621 1161049593184805606601233)
                    ·
                      refine ⟨870787194888604204950925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161049593184805606601233 870787194888604204950925)
                      ·
                        rfl

theorem cell23_1695852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_1695852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695852 prefixEnd_1695852 := by exact prefixLift 1695852
  have htrace : WordTrace (prefixWord ++ tailWord_1695852) baseStart_1695852 baseEnd_1695852 := by
    simpa [prefixWord, tailWord_1695852, baseEnd_1695852] using wordTrace_append hprefix tailTrace_1695852
  have hstable : (prefixWord ++ tailWord_1695852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695852).length < 2 ^ (prefixWord ++ tailWord_1695852).sum := by decide
  have hdescent : baseEnd_1695852 < baseStart_1695852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695882 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_1695882 : Nat := 118140960795 + 1695882 * 2 ^ 59
def prefixEnd_1695882 : Nat := 4983230072969 + 3 ^ 40 * 1695882 * 2
def baseEnd_1695882 : Nat := 870802599308239087575787

theorem tailTrace_1695882 : CollatzResearch.WordTrace tailWord_1695882 prefixEnd_1695882 870802599308239087575787 := by
  unfold tailWord_1695882
  simp only [CollatzResearch.WordTrace]
  refine ⟨15463474510529155607950475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41235932028077748287867933 15463474510529155607950475)
  ·
    refine ⟨23195211765793733411925713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15463474510529155607950475 23195211765793733411925713)
    ·
      refine ⟨17396408824345300058944285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23195211765793733411925713 17396408824345300058944285)
      ·
        refine ⟨6523653309129487522104107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17396408824345300058944285 6523653309129487522104107)
        ·
          refine ⟨9785479963694231283156161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6523653309129487522104107 9785479963694231283156161)
          ·
            refine ⟨7339109972770673462367121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9785479963694231283156161 7339109972770673462367121)
            ·
              refine ⟨5504332479578005096775341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7339109972770673462367121 5504332479578005096775341)
              ·
                refine ⟨2064124679841751911290753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5504332479578005096775341 2064124679841751911290753)
                ·
                  refine ⟨1548093509881313933468065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2064124679841751911290753 1548093509881313933468065)
                  ·
                    refine ⟨1161070132410985450101049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1548093509881313933468065 1161070132410985450101049)
                    ·
                      refine ⟨870802599308239087575787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161070132410985450101049 870802599308239087575787)
                      ·
                        rfl

theorem cell23_1695882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_1695882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695882 prefixEnd_1695882 := by exact prefixLift 1695882
  have htrace : WordTrace (prefixWord ++ tailWord_1695882) baseStart_1695882 baseEnd_1695882 := by
    simpa [prefixWord, tailWord_1695882, baseEnd_1695882] using wordTrace_append hprefix tailTrace_1695882
  have hstable : (prefixWord ++ tailWord_1695882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695882).length < 2 ^ (prefixWord ++ tailWord_1695882).sum := by decide
  have hdescent : baseEnd_1695882 < baseStart_1695882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695905 : List Nat := [1, 2, 3, 3, 1, 3, 2, 3, 5]
def baseStart_1695905 : Nat := 118140960795 + 1695905 * 2 ^ 59
def prefixEnd_1695905 : Nat := 4983230072969 + 3 ^ 40 * 1695905 * 2
def baseEnd_1695905 : Nat := 96757156595921388620909

theorem tailTrace_1695905 : CollatzResearch.WordTrace tailWord_1695905 prefixEnd_1695905 96757156595921388620909 := by
  unfold tailWord_1695905
  simp only [CollatzResearch.WordTrace]
  refine ⟨61854736921033297359889169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41236491280688864906592779 61854736921033297359889169)
  ·
    refine ⟨46391052690774973019916877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61854736921033297359889169 46391052690774973019916877)
    ·
      refine ⟨17396644759040614882468829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46391052690774973019916877 17396644759040614882468829)
      ·
        refine ⟨6523741784640230580925811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17396644759040614882468829 6523741784640230580925811)
        ·
          refine ⟨9785612676960345871388717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6523741784640230580925811 9785612676960345871388717)
          ·
            refine ⟨3669604753860129701770769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9785612676960345871388717 3669604753860129701770769)
            ·
              refine ⟨2752203565395097276328077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3669604753860129701770769 2752203565395097276328077)
              ·
                refine ⟨1032076337023161478623029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2752203565395097276328077 1032076337023161478623029)
                ·
                  refine ⟨96757156595921388620909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1032076337023161478623029 96757156595921388620909)
                  ·
                    rfl

theorem cell23_1695905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 5].length) (baseStart_1695905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695905 prefixEnd_1695905 := by exact prefixLift 1695905
  have htrace : WordTrace (prefixWord ++ tailWord_1695905) baseStart_1695905 baseEnd_1695905 := by
    simpa [prefixWord, tailWord_1695905, baseEnd_1695905] using wordTrace_append hprefix tailTrace_1695905
  have hstable : (prefixWord ++ tailWord_1695905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695905).length < 2 ^ (prefixWord ++ tailWord_1695905).sum := by decide
  have hdescent : baseEnd_1695905 < baseStart_1695905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695951 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_1695951 : Nat := 118140960795 + 1695951 * 2 ^ 59
def prefixEnd_1695951 : Nat := 4983230072969 + 3 ^ 40 * 1695951 * 2
def baseEnd_1695951 : Nat := 870838029473399317612969

theorem tailTrace_1695951 : CollatzResearch.WordTrace tailWord_1695951 prefixEnd_1695951 870838029473399317612969 := by
  unfold tailWord_1695951
  simp only [CollatzResearch.WordTrace]
  refine ⟨61856414678866647216063707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41237609785911098144042471 61856414678866647216063707)
  ·
    refine ⟨92784622018299970824095561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61856414678866647216063707 92784622018299970824095561)
    ·
      refine ⟨69588466513724978118071671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92784622018299970824095561 69588466513724978118071671)
      ·
        refine ⟨104382699770587467177107507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69588466513724978118071671 104382699770587467177107507)
        ·
          refine ⟨156574049655881200765661261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104382699770587467177107507 156574049655881200765661261)
          ·
            refine ⟨58715268620955450287122973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156574049655881200765661261 58715268620955450287122973)
            ·
              refine ⟨22018225732858293857671115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58715268620955450287122973 22018225732858293857671115)
              ·
                refine ⟨33027338599287440786506673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22018225732858293857671115 33027338599287440786506673)
                ·
                  refine ⟨24770503949465580589880005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33027338599287440786506673 24770503949465580589880005)
                  ·
                    refine ⟨4644469490524796360602501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24770503949465580589880005 4644469490524796360602501)
                    ·
                      refine ⟨870838029473399317612969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4644469490524796360602501 870838029473399317612969)
                      ·
                        rfl

theorem cell23_1695951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_1695951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695951 prefixEnd_1695951 := by exact prefixLift 1695951
  have htrace : WordTrace (prefixWord ++ tailWord_1695951) baseStart_1695951 baseEnd_1695951 := by
    simpa [prefixWord, tailWord_1695951, baseEnd_1695951] using wordTrace_append hprefix tailTrace_1695951
  have hstable : (prefixWord ++ tailWord_1695951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695951).length < 2 ^ (prefixWord ++ tailWord_1695951).sum := by decide
  have hdescent : baseEnd_1695951 < baseStart_1695951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695961 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 8]
def baseStart_1695961 : Nat := 118140960795 + 1695961 * 2 ^ 59
def prefixEnd_1695961 : Nat := 4983230072969 + 3 ^ 40 * 1695961 * 2
def baseEnd_1695961 : Nat := 96760351586660475387547

theorem tailTrace_1695961 : CollatzResearch.WordTrace tailWord_1695961 prefixEnd_1695961 96760351586660475387547 := by
  unfold tailWord_1695961
  simp only [CollatzResearch.WordTrace]
  refine ⟨61856779408830418923927737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41237852939220279282618491 61856779408830418923927737)
  ·
    refine ⟨46392584556622814192945803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61856779408830418923927737 46392584556622814192945803)
    ·
      refine ⟨69588876834934221289418705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46392584556622814192945803 69588876834934221289418705)
      ·
        refine ⟨52191657626200665967064029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69588876834934221289418705 52191657626200665967064029)
        ·
          refine ⟨19571871609825249737649011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52191657626200665967064029 19571871609825249737649011)
          ·
            refine ⟨29357807414737874606473517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19571871609825249737649011 29357807414737874606473517)
            ·
              refine ⟨11009177780526702977427569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29357807414737874606473517 11009177780526702977427569)
              ·
                refine ⟨8256883335395027233070677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11009177780526702977427569 8256883335395027233070677)
                ·
                  refine ⟨96760351586660475387547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8256883335395027233070677 96760351586660475387547)
                  ·
                    rfl

theorem cell23_1695961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 8].length) (baseStart_1695961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695961 prefixEnd_1695961 := by exact prefixLift 1695961
  have htrace : WordTrace (prefixWord ++ tailWord_1695961) baseStart_1695961 baseEnd_1695961 := by
    simpa [prefixWord, tailWord_1695961, baseEnd_1695961] using wordTrace_append hprefix tailTrace_1695961
  have hstable : (prefixWord ++ tailWord_1695961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695961).length < 2 ^ (prefixWord ++ tailWord_1695961).sum := by decide
  have hdescent : baseEnd_1695961 < baseStart_1695961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695975 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1695975 : Nat := 118140960795 + 1695975 * 2 ^ 59
def prefixEnd_1695975 : Nat := 4983230072969 + 3 ^ 40 * 1695975 * 2
def baseEnd_1695975 : Nat := 870850353009107223712859

theorem tailTrace_1695975 : CollatzResearch.WordTrace tailWord_1695975 prefixEnd_1695975 870850353009107223712859 := by
  unfold tailWord_1695975
  simp only [CollatzResearch.WordTrace]
  refine ⟨61857290030779699314937379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41238193353853132876624919 61857290030779699314937379)
  ·
    refine ⟨92785935046169548972406069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61857290030779699314937379 92785935046169548972406069)
    ·
      refine ⟨8698681410578395216163069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92785935046169548972406069 8698681410578395216163069)
      ·
        refine ⟨3262005528966898206061151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8698681410578395216163069 3262005528966898206061151)
        ·
          refine ⟨4893008293450347309091727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262005528966898206061151 4893008293450347309091727)
          ·
            refine ⟨7339512440175520963637591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893008293450347309091727 7339512440175520963637591)
            ·
              refine ⟨11009268660263281445456387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339512440175520963637591 11009268660263281445456387)
              ·
                refine ⟨16513902990394922168184581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11009268660263281445456387 16513902990394922168184581)
                ·
                  refine ⟨3096356810699047906534609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16513902990394922168184581 3096356810699047906534609)
                  ·
                    refine ⟨2322267608024285929900957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3096356810699047906534609 2322267608024285929900957)
                    ·
                      refine ⟨870850353009107223712859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2322267608024285929900957 870850353009107223712859)
                      ·
                        rfl

theorem cell23_1695975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1695975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695975 prefixEnd_1695975 := by exact prefixLift 1695975
  have htrace : WordTrace (prefixWord ++ tailWord_1695975) baseStart_1695975 baseEnd_1695975 := by
    simpa [prefixWord, tailWord_1695975, baseEnd_1695975] using wordTrace_append hprefix tailTrace_1695975
  have hstable : (prefixWord ++ tailWord_1695975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695975).length < 2 ^ (prefixWord ++ tailWord_1695975).sum := by decide
  have hdescent : baseEnd_1695975 < baseStart_1695975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695978 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 6]
def baseStart_1695978 : Nat := 118140960795 + 1695978 * 2 ^ 59
def prefixEnd_1695978 : Nat := 4983230072969 + 3 ^ 40 * 1695978 * 2
def baseEnd_1695978 : Nat := 96761321494563412441705

theorem tailTrace_1695978 : CollatzResearch.WordTrace tailWord_1695978 prefixEnd_1695978 96761321494563412441705 := by
  unfold tailWord_1695978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15464349862442207706824147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41238266299845887218197725 15464349862442207706824147)
  ·
    refine ⟨23196524793663311560236221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15464349862442207706824147 23196524793663311560236221)
    ·
      refine ⟨8698696797623741835088583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23196524793663311560236221 8698696797623741835088583)
      ·
        refine ⟨13048045196435612752632875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8698696797623741835088583 13048045196435612752632875)
        ·
          refine ⟨19572067794653419128949313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13048045196435612752632875 19572067794653419128949313)
          ·
            refine ⟨14679050845990064346711985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19572067794653419128949313 14679050845990064346711985)
            ·
              refine ⟨11009288134492548260033989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14679050845990064346711985 11009288134492548260033989)
              ·
                refine ⟨2064241525217352798756373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11009288134492548260033989 2064241525217352798756373)
                ·
                  refine ⟨96761321494563412441705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2064241525217352798756373 96761321494563412441705)
                  ·
                    rfl

theorem cell23_1695978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_1695978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1695978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1695978 prefixEnd_1695978 := by exact prefixLift 1695978
  have htrace : WordTrace (prefixWord ++ tailWord_1695978) baseStart_1695978 baseEnd_1695978 := by
    simpa [prefixWord, tailWord_1695978, baseEnd_1695978] using wordTrace_append hprefix tailTrace_1695978
  have hstable : (prefixWord ++ tailWord_1695978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695978).length < 2 ^ (prefixWord ++ tailWord_1695978).sum := by decide
  have hdescent : baseEnd_1695978 < baseStart_1695978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696032 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 2, 3, 2]
def baseStart_1696032 : Nat := 118140960795 + 1696032 * 2 ^ 59
def prefixEnd_1696032 : Nat := 4983230072969 + 3 ^ 40 * 1696032 * 2
def baseEnd_1696032 : Nat := 870879621406413500700097

theorem tailTrace_1696032 : CollatzResearch.WordTrace tailWord_1696032 prefixEnd_1696032 870879621406413500700097 := by
  unfold tailWord_1696032
  simp only [CollatzResearch.WordTrace]
  refine ⟨30929684495786599024881175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41239579327715465366508233 30929684495786599024881175)
  ·
    refine ⟨46394526743679898537321763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30929684495786599024881175 46394526743679898537321763)
    ·
      refine ⟨69591790115519847805982645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46394526743679898537321763 69591790115519847805982645)
      ·
        refine ⟨6524230323329985731810873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69591790115519847805982645 6524230323329985731810873)
        ·
          refine ⟨4893172742497489298858155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6524230323329985731810873 4893172742497489298858155)
          ·
            refine ⟨7339759113746233948287233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893172742497489298858155 7339759113746233948287233)
            ·
              refine ⟨5504819335309675461215425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7339759113746233948287233 5504819335309675461215425)
              ·
                refine ⟨4128614501482256595911569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5504819335309675461215425 4128614501482256595911569)
                ·
                  refine ⟨3096460876111692446933677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4128614501482256595911569 3096460876111692446933677)
                  ·
                    refine ⟨1161172828541884667600129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096460876111692446933677 1161172828541884667600129)
                    ·
                      refine ⟨870879621406413500700097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161172828541884667600129 870879621406413500700097)
                      ·
                        rfl

theorem cell23_1696032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_1696032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696032 prefixEnd_1696032 := by exact prefixLift 1696032
  have htrace : WordTrace (prefixWord ++ tailWord_1696032) baseStart_1696032 baseEnd_1696032 := by
    simpa [prefixWord, tailWord_1696032, baseEnd_1696032] using wordTrace_append hprefix tailTrace_1696032
  have hstable : (prefixWord ++ tailWord_1696032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696032).length < 2 ^ (prefixWord ++ tailWord_1696032).sum := by decide
  have hdescent : baseEnd_1696032 < baseStart_1696032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696112 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 3]
def baseStart_1696112 : Nat := 118140960795 + 1696112 * 2 ^ 59
def prefixEnd_1696112 : Nat := 4983230072969 + 3 ^ 40 * 1696112 * 2
def baseEnd_1696112 : Nat := 870920699858773187699729

theorem tailTrace_1696112 : CollatzResearch.WordTrace tailWord_1696112 prefixEnd_1696112 870920699858773187699729 := by
  unfold tailWord_1696112
  simp only [CollatzResearch.WordTrace]
  refine ⟨30931143415641685856337295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41241524554188914475116393 30931143415641685856337295)
  ·
    refine ⟨46396715123462528784505943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30931143415641685856337295 46396715123462528784505943)
    ·
      refine ⟨69595072685193793176758915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46396715123462528784505943 69595072685193793176758915)
      ·
        refine ⟨104392609027790689765138373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69595072685193793176758915 104392609027790689765138373)
        ·
          refine ⟨19573614192710754330963445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104392609027790689765138373 19573614192710754330963445)
          ·
            refine ⟨1835026330566633218527823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19573614192710754330963445 1835026330566633218527823)
            ·
              refine ⟨2752539495849949827791735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835026330566633218527823 2752539495849949827791735)
              ·
                refine ⟨4128809243774924741687603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752539495849949827791735 4128809243774924741687603)
                ·
                  refine ⟨6193213865662387112531405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128809243774924741687603 6193213865662387112531405)
                  ·
                    refine ⟨2322455199623395167199277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6193213865662387112531405 2322455199623395167199277)
                    ·
                      refine ⟨870920699858773187699729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2322455199623395167199277 870920699858773187699729)
                      ·
                        rfl

theorem cell23_1696112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 3].length) (baseStart_1696112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696112 prefixEnd_1696112 := by exact prefixLift 1696112
  have htrace : WordTrace (prefixWord ++ tailWord_1696112) baseStart_1696112 baseEnd_1696112 := by
    simpa [prefixWord, tailWord_1696112, baseEnd_1696112] using wordTrace_append hprefix tailTrace_1696112
  have hstable : (prefixWord ++ tailWord_1696112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696112).length < 2 ^ (prefixWord ++ tailWord_1696112).sum := by decide
  have hdescent : baseEnd_1696112 < baseStart_1696112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696173 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_1696173 : Nat := 118140960795 + 1696173 * 2 ^ 59
def prefixEnd_1696173 : Nat := 4983230072969 + 3 ^ 40 * 1696173 * 2
def baseEnd_1696173 : Nat := 870952022178697449036949

theorem tailTrace_1696173 : CollatzResearch.WordTrace tailWord_1696173 prefixEnd_1696173 870952022178697449036949 := by
  unfold tailWord_1696173
  simp only [CollatzResearch.WordTrace]
  refine ⟨61864511684062379130645173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41243007789374919420430115 61864511684062379130645173)
  ·
    refine ⟨5799797970380848043497985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61864511684062379130645173 5799797970380848043497985)
    ·
      refine ⟨4349848477785636032623489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5799797970380848043497985 4349848477785636032623489)
      ·
        refine ⟨3262386358339227024467617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4349848477785636032623489 3262386358339227024467617)
        ·
          refine ⟨2446789768754420268350713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3262386358339227024467617 2446789768754420268350713)
          ·
            refine ⟨1835092326565815201263035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2446789768754420268350713 1835092326565815201263035)
            ·
              refine ⟨2752638489848722801894553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835092326565815201263035 2752638489848722801894553)
              ·
                refine ⟨2064478867386542101420915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2752638489848722801894553 2064478867386542101420915)
                ·
                  refine ⟨3096718301079813152131373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064478867386542101420915 3096718301079813152131373)
                  ·
                    refine ⟨1161269362904929932049265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096718301079813152131373 1161269362904929932049265)
                    ·
                      refine ⟨870952022178697449036949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161269362904929932049265 870952022178697449036949)
                      ·
                        rfl

theorem cell23_1696173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_1696173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696173 prefixEnd_1696173 := by exact prefixLift 1696173
  have htrace : WordTrace (prefixWord ++ tailWord_1696173) baseStart_1696173 baseEnd_1696173 := by
    simpa [prefixWord, tailWord_1696173, baseEnd_1696173] using wordTrace_append hprefix tailTrace_1696173
  have hstable : (prefixWord ++ tailWord_1696173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696173).length < 2 ^ (prefixWord ++ tailWord_1696173).sum := by decide
  have hdescent : baseEnd_1696173 < baseStart_1696173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696208 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_1696208 : Nat := 118140960795 + 1696208 * 2 ^ 59
def prefixEnd_1696208 : Nat := 4983230072969 + 3 ^ 40 * 1696208 * 2
def baseEnd_1696208 : Nat := 870969994001604812099287

theorem tailTrace_1696208 : CollatzResearch.WordTrace tailWord_1696208 prefixEnd_1696208 870969994001604812099287 := by
  unfold tailWord_1696208
  simp only [CollatzResearch.WordTrace]
  refine ⟨30932894119467790054084639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41243858825957053405446185 30932894119467790054084639)
  ·
    refine ⟨46399341179201685081126959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30932894119467790054084639 46399341179201685081126959)
    ·
      refine ⟨69599011768802527621690439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46399341179201685081126959 69599011768802527621690439)
      ·
        refine ⟨104398517653203791432535659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69599011768802527621690439 104398517653203791432535659)
        ·
          refine ⟨156597776479805687148803489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104398517653203791432535659 156597776479805687148803489)
          ·
            refine ⟨117448332359854265361602617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156597776479805687148803489 117448332359854265361602617)
            ·
              refine ⟨88086249269890699021201963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117448332359854265361602617 88086249269890699021201963)
              ·
                refine ⟨132129373904836048531802945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88086249269890699021201963 132129373904836048531802945)
                ·
                  refine ⟨99097030428627036398852209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132129373904836048531802945 99097030428627036398852209)
                  ·
                    refine ⟨74322772821470277299139157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99097030428627036398852209 74322772821470277299139157)
                    ·
                      refine ⟨870969994001604812099287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 74322772821470277299139157 870969994001604812099287)
                      ·
                        rfl

theorem cell23_1696208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_1696208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696208 prefixEnd_1696208 := by exact prefixLift 1696208
  have htrace : WordTrace (prefixWord ++ tailWord_1696208) baseStart_1696208 baseEnd_1696208 := by
    simpa [prefixWord, tailWord_1696208, baseEnd_1696208] using wordTrace_append hprefix tailTrace_1696208
  have hstable : (prefixWord ++ tailWord_1696208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696208).length < 2 ^ (prefixWord ++ tailWord_1696208).sum := by decide
  have hdescent : baseEnd_1696208 < baseStart_1696208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696225 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1696225 : Nat := 118140960795 + 1696225 * 2 ^ 59
def prefixEnd_1696225 : Nat := 4983230072969 + 3 ^ 40 * 1696225 * 2
def baseEnd_1696225 : Nat := 870978723172731245586709

theorem tailTrace_1696225 : CollatzResearch.WordTrace tailWord_1696225 prefixEnd_1696225 870978723172731245586709 := by
  unfold tailWord_1696225
  simp only [CollatzResearch.WordTrace]
  refine ⟨61866408279873992011538129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41244272186582661341025419 61866408279873992011538129)
  ·
    refine ⟨46399806209905494008653597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61866408279873992011538129 46399806209905494008653597)
    ·
      refine ⟨17399927328714560253245099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46399806209905494008653597 17399927328714560253245099)
      ·
        refine ⟨26099890993071840379867649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17399927328714560253245099 26099890993071840379867649)
        ·
          refine ⟨19574918244803880284900737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26099890993071840379867649 19574918244803880284900737)
          ·
            refine ⟨14681188683602910213675553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19574918244803880284900737 14681188683602910213675553)
            ·
              refine ⟨11010891512702182660256665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14681188683602910213675553 11010891512702182660256665)
              ·
                refine ⟨8258168634526636995192499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11010891512702182660256665 8258168634526636995192499)
                ·
                  refine ⟨12387252951789955492788749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8258168634526636995192499 12387252951789955492788749)
                  ·
                    refine ⟨4645219856921233309795781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12387252951789955492788749 4645219856921233309795781)
                    ·
                      refine ⟨870978723172731245586709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4645219856921233309795781 870978723172731245586709)
                      ·
                        rfl

theorem cell23_1696225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1696225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696225 prefixEnd_1696225 := by exact prefixLift 1696225
  have htrace : WordTrace (prefixWord ++ tailWord_1696225) baseStart_1696225 baseEnd_1696225 := by
    simpa [prefixWord, tailWord_1696225, baseEnd_1696225] using wordTrace_append hprefix tailTrace_1696225
  have hstable : (prefixWord ++ tailWord_1696225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696225).length < 2 ^ (prefixWord ++ tailWord_1696225).sum := by decide
  have hdescent : baseEnd_1696225 < baseStart_1696225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696265 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 6]
def baseStart_1696265 : Nat := 118140960795 + 1696265 * 2 ^ 59
def prefixEnd_1696265 : Nat := 4983230072969 + 3 ^ 40 * 1696265 * 2
def baseEnd_1696265 : Nat := 96777695822101232120725

theorem tailTrace_1696265 : CollatzResearch.WordTrace tailWord_1696265 prefixEnd_1696265 96777695822101232120725 := by
  unfold tailWord_1696265
  simp only [CollatzResearch.WordTrace]
  refine ⟨61867867199729078842994249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41245244799819385895329499 61867867199729078842994249)
  ·
    refine ⟨46400900399796809132245687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61867867199729078842994249 46400900399796809132245687)
    ·
      refine ⟨69601350599695213698368531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46400900399796809132245687 69601350599695213698368531)
      ·
        refine ⟨104402025899542820547552797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69601350599695213698368531 104402025899542820547552797)
        ·
          refine ⟨39150759712328557705332299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104402025899542820547552797 39150759712328557705332299)
          ·
            refine ⟨58726139568492836557998449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39150759712328557705332299 58726139568492836557998449)
            ·
              refine ⟨44044604676369627418498837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58726139568492836557998449 44044604676369627418498837)
              ·
                refine ⟨2064590844204826285242133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44044604676369627418498837 2064590844204826285242133)
                ·
                  refine ⟨96777695822101232120725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2064590844204826285242133 96777695822101232120725)
                  ·
                    rfl

theorem cell23_1696265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 6].length) (baseStart_1696265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696265 prefixEnd_1696265 := by exact prefixLift 1696265
  have htrace : WordTrace (prefixWord ++ tailWord_1696265) baseStart_1696265 baseEnd_1696265 := by
    simpa [prefixWord, tailWord_1696265, baseEnd_1696265] using wordTrace_append hprefix tailTrace_1696265
  have hstable : (prefixWord ++ tailWord_1696265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696265).length < 2 ^ (prefixWord ++ tailWord_1696265).sum := by decide
  have hdescent : baseEnd_1696265 < baseStart_1696265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696276 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_1696276 : Nat := 118140960795 + 1696276 * 2 ^ 59
def prefixEnd_1696276 : Nat := 4983230072969 + 3 ^ 40 * 1696276 * 2
def baseEnd_1696276 : Nat := 871004910686110546048975

theorem tailTrace_1696276 : CollatzResearch.WordTrace tailWord_1696276 prefixEnd_1696276 871004910686110546048975 := by
  unfold tailWord_1696276
  simp only [CollatzResearch.WordTrace]
  refine ⟨30934134201344613860822341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41245512268459485147763121 30934134201344613860822341)
  ·
    refine ⟨5800150162752115098904189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30934134201344613860822341 5800150162752115098904189)
    ·
      refine ⟨2175056311032043162089071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5800150162752115098904189 2175056311032043162089071)
      ·
        refine ⟨3262584466548064743133607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175056311032043162089071 3262584466548064743133607)
        ·
          refine ⟨4893876699822097114700411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262584466548064743133607 4893876699822097114700411)
          ·
            refine ⟨7340815049733145672050617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893876699822097114700411 7340815049733145672050617)
            ·
              refine ⟨5505611287299859254037963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7340815049733145672050617 5505611287299859254037963)
              ·
                refine ⟨8258416930949788881056945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505611287299859254037963 8258416930949788881056945)
                ·
                  refine ⟨6193812698212341660792709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8258416930949788881056945 6193812698212341660792709)
                  ·
                    refine ⟨1161339880914814061398633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6193812698212341660792709 1161339880914814061398633)
                    ·
                      refine ⟨871004910686110546048975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161339880914814061398633 871004910686110546048975)
                      ·
                        rfl

theorem cell23_1696276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_1696276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696276 prefixEnd_1696276 := by exact prefixLift 1696276
  have htrace : WordTrace (prefixWord ++ tailWord_1696276) baseStart_1696276 baseEnd_1696276 := by
    simpa [prefixWord, tailWord_1696276, baseEnd_1696276] using wordTrace_append hprefix tailTrace_1696276
  have hstable : (prefixWord ++ tailWord_1696276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696276).length < 2 ^ (prefixWord ++ tailWord_1696276).sum := by decide
  have hdescent : baseEnd_1696276 < baseStart_1696276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696312 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 1, 5]
def baseStart_1696312 : Nat := 118140960795 + 1696312 * 2 ^ 59
def prefixEnd_1696312 : Nat := 4983230072969 + 3 ^ 40 * 1696312 * 2
def baseEnd_1696312 : Nat := 290341131996557468399603

theorem tailTrace_1696312 : CollatzResearch.WordTrace tailWord_1696312 prefixEnd_1696312 290341131996557468399603 := by
  unfold tailWord_1696312
  simp only [CollatzResearch.WordTrace]
  refine ⟨30934790715279402934977595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41246387620372537246636793 30934790715279402934977595)
  ·
    refine ⟨46402186072919104402466393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30934790715279402934977595 46402186072919104402466393)
    ·
      refine ⟨34801639554689328301849795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46402186072919104402466393 34801639554689328301849795)
      ·
        refine ⟨52202459332033992452774693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34801639554689328301849795 52202459332033992452774693)
        ·
          refine ⟨9787961124756373584895255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52202459332033992452774693 9787961124756373584895255)
          ·
            refine ⟨14681941687134560377342883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9787961124756373584895255 14681941687134560377342883)
            ·
              refine ⟨22022912530701840566014325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14681941687134560377342883 22022912530701840566014325)
              ·
                refine ⟨2064648049753297553063843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22022912530701840566014325 2064648049753297553063843)
                ·
                  refine ⟨3096972074629946329595765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064648049753297553063843 3096972074629946329595765)
                  ·
                    refine ⟨290341131996557468399603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3096972074629946329595765 290341131996557468399603)
                    ·
                      rfl

theorem cell23_1696312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_1696312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696312 prefixEnd_1696312 := by exact prefixLift 1696312
  have htrace : WordTrace (prefixWord ++ tailWord_1696312) baseStart_1696312 baseEnd_1696312 := by
    simpa [prefixWord, tailWord_1696312, baseEnd_1696312] using wordTrace_append hprefix tailTrace_1696312
  have hstable : (prefixWord ++ tailWord_1696312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696312).length < 2 ^ (prefixWord ++ tailWord_1696312).sum := by decide
  have hdescent : baseEnd_1696312 < baseStart_1696312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696319 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 2, 3, 2]
def baseStart_1696319 : Nat := 118140960795 + 1696319 * 2 ^ 59
def prefixEnd_1696319 : Nat := 4983230072969 + 3 ^ 40 * 1696319 * 2
def baseEnd_1696319 : Nat := 871026990354253877811277

theorem tailTrace_1696319 : CollatzResearch.WordTrace tailWord_1696319 prefixEnd_1696319 871026990354253877811277 := by
  unfold tailWord_1696319
  simp only [CollatzResearch.WordTrace]
  refine ⟨61869836741533446065460011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41246557827688964043640007 61869836741533446065460011)
  ·
    refine ⟨92804755112300169098190017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61869836741533446065460011 92804755112300169098190017)
    ·
      refine ⟨69603566334225126823642513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92804755112300169098190017 69603566334225126823642513)
      ·
        refine ⟨52202674750668845117731885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69603566334225126823642513 52202674750668845117731885)
        ·
          refine ⟨19576003031500816919149457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52202674750668845117731885 19576003031500816919149457)
          ·
            refine ⟨14682002273625612689362093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19576003031500816919149457 14682002273625612689362093)
            ·
              refine ⟨5505750852609604758510785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14682002273625612689362093 5505750852609604758510785)
              ·
                refine ⟨4129313139457203568883089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5505750852609604758510785 4129313139457203568883089)
                ·
                  refine ⟨3096984854592902676662317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129313139457203568883089 3096984854592902676662317)
                  ·
                    refine ⟨1161369320472338503748369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096984854592902676662317 1161369320472338503748369)
                    ·
                      refine ⟨871026990354253877811277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161369320472338503748369 871026990354253877811277)
                      ·
                        rfl

theorem cell23_1696319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_1696319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696319 prefixEnd_1696319 := by exact prefixLift 1696319
  have htrace : WordTrace (prefixWord ++ tailWord_1696319) baseStart_1696319 baseEnd_1696319 := by
    simpa [prefixWord, tailWord_1696319, baseEnd_1696319] using wordTrace_append hprefix tailTrace_1696319
  have hstable : (prefixWord ++ tailWord_1696319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696319).length < 2 ^ (prefixWord ++ tailWord_1696319).sum := by decide
  have hdescent : baseEnd_1696319 < baseStart_1696319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696332 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1696332 : Nat := 118140960795 + 1696332 * 2 ^ 59
def prefixEnd_1696332 : Nat := 4983230072969 + 3 ^ 40 * 1696332 * 2
def baseEnd_1696332 : Nat := 871033665602762326948717

theorem tailTrace_1696332 : CollatzResearch.WordTrace tailWord_1696332 prefixEnd_1696332 871033665602762326948717 := by
  unfold tailWord_1696332
  simp only [CollatzResearch.WordTrace]
  refine ⟨30935155445243174642841625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41246873926990899523788833 30935155445243174642841625)
  ·
    refine ⟨23201366583932380982131219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30935155445243174642841625 23201366583932380982131219)
    ·
      refine ⟨34802049875898571473196829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23201366583932380982131219 34802049875898571473196829)
      ·
        refine ⟨13050768703461964302448811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34802049875898571473196829 13050768703461964302448811)
        ·
          refine ⟨19576153055192946453673217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13050768703461964302448811 19576153055192946453673217)
          ·
            refine ⟨14682114791394709840254913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19576153055192946453673217 14682114791394709840254913)
            ·
              refine ⟨11011586093546032380191185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14682114791394709840254913 11011586093546032380191185)
              ·
                refine ⟨8258689570159524285143389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11011586093546032380191185 8258689570159524285143389)
                ·
                  refine ⟨3097008588809821606928771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8258689570159524285143389 3097008588809821606928771)
                  ·
                    refine ⟨4645512883214732410393157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3097008588809821606928771 4645512883214732410393157)
                    ·
                      refine ⟨871033665602762326948717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4645512883214732410393157 871033665602762326948717)
                      ·
                        rfl

theorem cell23_1696332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1696332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696332 prefixEnd_1696332 := by exact prefixLift 1696332
  have htrace : WordTrace (prefixWord ++ tailWord_1696332) baseStart_1696332 baseEnd_1696332 := by
    simpa [prefixWord, tailWord_1696332, baseEnd_1696332] using wordTrace_append hprefix tailTrace_1696332
  have hstable : (prefixWord ++ tailWord_1696332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696332).length < 2 ^ (prefixWord ++ tailWord_1696332).sum := by decide
  have hdescent : baseEnd_1696332 < baseStart_1696332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696355 : List Nat := [1, 1, 1, 5, 1, 2, 1, 11]
def baseStart_1696355 : Nat := 118140960795 + 1696355 * 2 ^ 59
def prefixEnd_1696355 : Nat := 4983230072969 + 3 ^ 40 * 1696355 * 2
def baseEnd_1696355 : Nat := 32260943542882064331893

theorem tailTrace_1696355 : CollatzResearch.WordTrace tailWord_1696355 prefixEnd_1696355 32260943542882064331893 := by
  unfold tailWord_1696355
  simp only [CollatzResearch.WordTrace]
  refine ⟨61871149769403024213770519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41247433179602016142513679 61871149769403024213770519)
  ·
    refine ⟨92806724654104536320655779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61871149769403024213770519 92806724654104536320655779)
    ·
      refine ⟨139210086981156804480983669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92806724654104536320655779 139210086981156804480983669)
      ·
        refine ⟨13050945654483450420092219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139210086981156804480983669 13050945654483450420092219)
        ·
          refine ⟨19576418481725175630138329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13050945654483450420092219 19576418481725175630138329)
          ·
            refine ⟨14682313861293881722603747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19576418481725175630138329 14682313861293881722603747)
            ·
              refine ⟨22023470791940822583905621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14682313861293881722603747 22023470791940822583905621)
              ·
                refine ⟨32260943542882064331893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 22023470791940822583905621 32260943542882064331893)
                ·
                  rfl

theorem cell23_1696355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 11].length) (baseStart_1696355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696355 prefixEnd_1696355 := by exact prefixLift 1696355
  have htrace : WordTrace (prefixWord ++ tailWord_1696355) baseStart_1696355 baseEnd_1696355 := by
    simpa [prefixWord, tailWord_1696355, baseEnd_1696355] using wordTrace_append hprefix tailTrace_1696355
  have hstable : (prefixWord ++ tailWord_1696355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696355).length < 2 ^ (prefixWord ++ tailWord_1696355).sum := by decide
  have hdescent : baseEnd_1696355 < baseStart_1696355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696409 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 3, 3, 2]
def baseStart_1696409 : Nat := 118140960795 + 1696409 * 2 ^ 59
def prefixEnd_1696409 : Nat := 4983230072969 + 3 ^ 40 * 1696409 * 2
def baseEnd_1696409 : Nat := 871073203613158525685863

theorem tailTrace_1696409 : CollatzResearch.WordTrace tailWord_1696409 prefixEnd_1696409 871073203613158525685863 := by
  unfold tailWord_1696409
  simp only [CollatzResearch.WordTrace]
  refine ⟨61873119311207391436236281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41248746207471594290824187 61873119311207391436236281)
  ·
    refine ⟨46404839483405543577177211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61873119311207391436236281 46404839483405543577177211)
    ·
      refine ⟨69607259225108315365765817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46404839483405543577177211 69607259225108315365765817)
      ·
        refine ⟨52205444418831236524324363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69607259225108315365765817 52205444418831236524324363)
        ·
          refine ⟨78308166628246854786486545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52205444418831236524324363 78308166628246854786486545)
          ·
            refine ⟨58731124971185141089864909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78308166628246854786486545 58731124971185141089864909)
            ·
              refine ⟨22024171864194427908699341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58731124971185141089864909 22024171864194427908699341)
              ·
                refine ⟨8259064449072910465762253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22024171864194427908699341 8259064449072910465762253)
                ·
                  refine ⟨3097149168402341424660845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8259064449072910465762253 3097149168402341424660845)
                  ·
                    refine ⟨1161430938150878034247817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097149168402341424660845 1161430938150878034247817)
                    ·
                      refine ⟨871073203613158525685863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161430938150878034247817 871073203613158525685863)
                      ·
                        rfl

theorem cell23_1696409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_1696409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696409 prefixEnd_1696409 := by exact prefixLift 1696409
  have htrace : WordTrace (prefixWord ++ tailWord_1696409) baseStart_1696409 baseEnd_1696409 := by
    simpa [prefixWord, tailWord_1696409, baseEnd_1696409] using wordTrace_append hprefix tailTrace_1696409
  have hstable : (prefixWord ++ tailWord_1696409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696409).length < 2 ^ (prefixWord ++ tailWord_1696409).sum := by decide
  have hdescent : baseEnd_1696409 < baseStart_1696409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696433 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1696433 : Nat := 118140960795 + 1696433 * 2 ^ 59
def prefixEnd_1696433 : Nat := 4983230072969 + 3 ^ 40 * 1696433 * 2
def baseEnd_1696433 : Nat := 871085527148866431785753

theorem tailTrace_1696433 : CollatzResearch.WordTrace tailWord_1696433 prefixEnd_1696433 871085527148866431785753 := by
  unfold tailWord_1696433
  simp only [CollatzResearch.WordTrace]
  refine ⟨61873994663120443535109953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41249329775413629023406635 61873994663120443535109953)
  ·
    refine ⟨46405495997340332651332465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61873994663120443535109953 46405495997340332651332465)
    ·
      refine ⟨34804121998005249488499349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46405495997340332651332465 34804121998005249488499349)
      ·
        refine ⟨1631443218656496069773407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34804121998005249488499349 1631443218656496069773407)
        ·
          refine ⟨2447164827984744104660111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631443218656496069773407 2447164827984744104660111)
          ·
            refine ⟨3670747241977116156990167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447164827984744104660111 3670747241977116156990167)
            ·
              refine ⟨5506120862965674235485251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670747241977116156990167 5506120862965674235485251)
              ·
                refine ⟨8259181294448511353227877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5506120862965674235485251 8259181294448511353227877)
                ·
                  refine ⟨1548596492709095878730227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8259181294448511353227877 1548596492709095878730227)
                  ·
                    refine ⟨2322894739063643818095341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1548596492709095878730227 2322894739063643818095341)
                    ·
                      refine ⟨871085527148866431785753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2322894739063643818095341 871085527148866431785753)
                      ·
                        rfl

theorem cell23_1696433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1696433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696433 prefixEnd_1696433 := by exact prefixLift 1696433
  have htrace : WordTrace (prefixWord ++ tailWord_1696433) baseStart_1696433 baseEnd_1696433 := by
    simpa [prefixWord, tailWord_1696433, baseEnd_1696433] using wordTrace_append hprefix tailTrace_1696433
  have hstable : (prefixWord ++ tailWord_1696433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696433).length < 2 ^ (prefixWord ++ tailWord_1696433).sum := by decide
  have hdescent : baseEnd_1696433 < baseStart_1696433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696456 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_1696456 : Nat := 118140960795 + 1696456 * 2 ^ 59
def prefixEnd_1696456 : Nat := 4983230072969 + 3 ^ 40 * 1696456 * 2
def baseEnd_1696456 : Nat := 871097337203919841798147

theorem tailTrace_1696456 : CollatzResearch.WordTrace tailWord_1696456 prefixEnd_1696456 871097337203919841798147 := by
  unfold tailWord_1696456
  simp only [CollatzResearch.WordTrace]
  refine ⟨30937416771018559231598611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41249889028024745642131481 30937416771018559231598611)
  ·
    refine ⟨46406125156527838847397917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30937416771018559231598611 46406125156527838847397917)
    ·
      refine ⟨17402296933697939567774219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46406125156527838847397917 17402296933697939567774219)
      ·
        refine ⟨26103445400546909351661329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17402296933697939567774219 26103445400546909351661329)
        ·
          refine ⟨19577584050410182013745997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26103445400546909351661329 19577584050410182013745997)
          ·
            refine ⟨7341594018903818255154749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19577584050410182013745997 7341594018903818255154749)
            ·
              refine ⟨2753097757088931845683031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7341594018903818255154749 2753097757088931845683031)
              ·
                refine ⟨4129646635633397768524547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753097757088931845683031 4129646635633397768524547)
                ·
                  refine ⟨6194469953450096652786821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129646635633397768524547 6194469953450096652786821)
                  ·
                    refine ⟨1161463116271893122397529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6194469953450096652786821 1161463116271893122397529)
                    ·
                      refine ⟨871097337203919841798147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161463116271893122397529 871097337203919841798147)
                      ·
                        rfl

theorem cell23_1696456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_1696456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696456 prefixEnd_1696456 := by exact prefixLift 1696456
  have htrace : WordTrace (prefixWord ++ tailWord_1696456) baseStart_1696456 baseEnd_1696456 := by
    simpa [prefixWord, tailWord_1696456, baseEnd_1696456] using wordTrace_append hprefix tailTrace_1696456
  have hstable : (prefixWord ++ tailWord_1696456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696456).length < 2 ^ (prefixWord ++ tailWord_1696456).sum := by decide
  have hdescent : baseEnd_1696456 < baseStart_1696456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696476 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1696476 : Nat := 118140960795 + 1696476 * 2 ^ 59
def prefixEnd_1696476 : Nat := 4983230072969 + 3 ^ 40 * 1696476 * 2
def baseEnd_1696476 : Nat := 871107606817009763548055

theorem tailTrace_1696476 : CollatzResearch.WordTrace tailWord_1696476 prefixEnd_1696476 871107606817009763548055 := by
  unfold tailWord_1696476
  simp only [CollatzResearch.WordTrace]
  refine ⟨30937781500982330939462641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41250375334643107919283521 30937781500982330939462641)
  ·
    refine ⟨23203336125736748204596981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30937781500982330939462641 23203336125736748204596981)
    ·
      refine ⟨2175312761787820144180967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23203336125736748204596981 2175312761787820144180967)
      ·
        refine ⟨3262969142681730216271451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175312761787820144180967 3262969142681730216271451)
        ·
          refine ⟨4894453714022595324407177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262969142681730216271451 4894453714022595324407177)
          ·
            refine ⟨3670840285516946493305383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4894453714022595324407177 3670840285516946493305383)
            ·
              refine ⟨5506260428275419739958075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670840285516946493305383 5506260428275419739958075)
              ·
                refine ⟨8259390642413129609937113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5506260428275419739958075 8259390642413129609937113)
                ·
                  refine ⟨6194542981809847207452835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8259390642413129609937113 6194542981809847207452835)
                  ·
                    refine ⟨9291814472714770811179253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6194542981809847207452835 9291814472714770811179253)
                    ·
                      refine ⟨871107606817009763548055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9291814472714770811179253 871107606817009763548055)
                      ·
                        rfl

theorem cell23_1696476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1696476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696476 prefixEnd_1696476 := by exact prefixLift 1696476
  have htrace : WordTrace (prefixWord ++ tailWord_1696476) baseStart_1696476 baseEnd_1696476 := by
    simpa [prefixWord, tailWord_1696476, baseEnd_1696476] using wordTrace_append hprefix tailTrace_1696476
  have hstable : (prefixWord ++ tailWord_1696476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696476).length < 2 ^ (prefixWord ++ tailWord_1696476).sum := by decide
  have hdescent : baseEnd_1696476 < baseStart_1696476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696496 : List Nat := [2, 1, 1, 1, 3, 1, 7, 2, 5]
def baseStart_1696496 : Nat := 118140960795 + 1696496 * 2 ^ 59
def prefixEnd_1696496 : Nat := 4983230072969 + 3 ^ 40 * 1696496 * 2
def baseEnd_1696496 : Nat := 96790875158899965033107

theorem tailTrace_1696496 : CollatzResearch.WordTrace tailWord_1696496 prefixEnd_1696496 96790875158899965033107 := by
  unfold tailWord_1696496
  simp only [CollatzResearch.WordTrace]
  refine ⟨30938146230946102647326671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41250861641261470196435561 30938146230946102647326671)
  ·
    refine ⟨46407219346419153970990007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30938146230946102647326671 46407219346419153970990007)
    ·
      refine ⟨69610829019628730956485011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46407219346419153970990007 69610829019628730956485011)
      ·
        refine ⟨104416243529443096434727517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69610829019628730956485011 104416243529443096434727517)
        ·
          refine ⟨39156091323541161163022819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104416243529443096434727517 39156091323541161163022819)
          ·
            refine ⟨58734136985311741744534229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39156091323541161163022819 58734136985311741744534229)
            ·
              refine ⟨1376581335593243947137521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58734136985311741744534229 1376581335593243947137521)
              ·
                refine ⟨1032436001694932960353141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376581335593243947137521 1032436001694932960353141)
                ·
                  refine ⟨96790875158899965033107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1032436001694932960353141 96790875158899965033107)
                  ·
                    rfl

theorem cell23_1696496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 5].length) (baseStart_1696496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696496 prefixEnd_1696496 := by exact prefixLift 1696496
  have htrace : WordTrace (prefixWord ++ tailWord_1696496) baseStart_1696496 baseEnd_1696496 := by
    simpa [prefixWord, tailWord_1696496, baseEnd_1696496] using wordTrace_append hprefix tailTrace_1696496
  have hstable : (prefixWord ++ tailWord_1696496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696496).length < 2 ^ (prefixWord ++ tailWord_1696496).sum := by decide
  have hdescent : baseEnd_1696496 < baseStart_1696496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696499 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 2, 5, 2]
def baseStart_1696499 : Nat := 118140960795 + 1696499 * 2 ^ 59
def prefixEnd_1696499 : Nat := 4983230072969 + 3 ^ 40 * 1696499 * 2
def baseEnd_1696499 : Nat := 871119416872063173560449

theorem tailTrace_1696499 : CollatzResearch.WordTrace tailWord_1696499 prefixEnd_1696499 871119416872063173560449 := by
  unfold tailWord_1696499
  simp only [CollatzResearch.WordTrace]
  refine ⟨61876401880881336807012551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41250934587254224538008367 61876401880881336807012551)
  ·
    refine ⟨92814602821322005210518827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61876401880881336807012551 92814602821322005210518827)
    ·
      refine ⟨139221904231983007815778241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92814602821322005210518827 139221904231983007815778241)
      ·
        refine ⟨104416428173987255861833681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139221904231983007815778241 104416428173987255861833681)
        ·
          refine ⟨78312321130490441896375261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104416428173987255861833681 78312321130490441896375261)
          ·
            refine ⟨29367120423933915711140723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78312321130490441896375261 29367120423933915711140723)
            ·
              refine ⟨44050680635900873566711085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29367120423933915711140723 44050680635900873566711085)
              ·
                refine ⟨16519005238462827587516657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44050680635900873566711085 16519005238462827587516657)
                ·
                  refine ⟨12389253928847120690637493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16519005238462827587516657 12389253928847120690637493)
                  ·
                    refine ⟨1161492555829417564747265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12389253928847120690637493 1161492555829417564747265)
                    ·
                      refine ⟨871119416872063173560449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161492555829417564747265 871119416872063173560449)
                      ·
                        rfl

theorem cell23_1696499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 5, 2].length) (baseStart_1696499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696499 prefixEnd_1696499 := by exact prefixLift 1696499
  have htrace : WordTrace (prefixWord ++ tailWord_1696499) baseStart_1696499 baseEnd_1696499 := by
    simpa [prefixWord, tailWord_1696499, baseEnd_1696499] using wordTrace_append hprefix tailTrace_1696499
  have hstable : (prefixWord ++ tailWord_1696499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696499).length < 2 ^ (prefixWord ++ tailWord_1696499).sum := by decide
  have hdescent : baseEnd_1696499 < baseStart_1696499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696501 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1696501 : Nat := 118140960795 + 1696501 * 2 ^ 59
def prefixEnd_1696501 : Nat := 4983230072969 + 3 ^ 40 * 1696501 * 2
def baseEnd_1696501 : Nat := 871120443833372165735441

theorem tailTrace_1696501 : CollatzResearch.WordTrace tailWord_1696501 prefixEnd_1696501 871120443833372165735441 := by
  unfold tailWord_1696501
  simp only [CollatzResearch.WordTrace]
  refine ⟨61876474826874091148585357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41250983217916060765723571 61876474826874091148585357)
  ·
    refine ⟨23203678060077784180719509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61876474826874091148585357 23203678060077784180719509)
    ·
      refine ⟨1087672409066146133471227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23203678060077784180719509 1087672409066146133471227)
      ·
        refine ⟨1631508613599219200206841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087672409066146133471227 1631508613599219200206841)
        ·
          refine ⟨1223631460199414400155131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1631508613599219200206841 1223631460199414400155131)
          ·
            refine ⟨1835447190299121600232697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223631460199414400155131 1835447190299121600232697)
            ·
              refine ⟨1376585392724341200174523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835447190299121600232697 1376585392724341200174523)
              ·
                refine ⟨2064878089086511800261785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376585392724341200174523 2064878089086511800261785)
                ·
                  refine ⟨1548658566814883850196339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2064878089086511800261785 1548658566814883850196339)
                  ·
                    refine ⟨2322987850222325775294509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1548658566814883850196339 2322987850222325775294509)
                    ·
                      refine ⟨871120443833372165735441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2322987850222325775294509 871120443833372165735441)
                      ·
                        rfl

theorem cell23_1696501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1696501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696501 prefixEnd_1696501 := by exact prefixLift 1696501
  have htrace : WordTrace (prefixWord ++ tailWord_1696501) baseStart_1696501 baseEnd_1696501 := by
    simpa [prefixWord, tailWord_1696501, baseEnd_1696501] using wordTrace_append hprefix tailTrace_1696501
  have hstable : (prefixWord ++ tailWord_1696501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696501).length < 2 ^ (prefixWord ++ tailWord_1696501).sum := by decide
  have hdescent : baseEnd_1696501 < baseStart_1696501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696529 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_1696529 : Nat := 118140960795 + 1696529 * 2 ^ 59
def prefixEnd_1696529 : Nat := 4983230072969 + 3 ^ 40 * 1696529 * 2
def baseEnd_1696529 : Nat := 871134821291698056185311

theorem tailTrace_1696529 : CollatzResearch.WordTrace tailWord_1696529 prefixEnd_1696529 871134821291698056185311 := by
  unfold tailWord_1696529
  simp only [CollatzResearch.WordTrace]
  refine ⟨61877496070772651930604641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41251664047181767953736427 61877496070772651930604641)
  ·
    refine ⟨46408122053079488947953481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61877496070772651930604641 46408122053079488947953481)
    ·
      refine ⟨34806091539809616710965111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46408122053079488947953481 34806091539809616710965111)
      ·
        refine ⟨52209137309714425066447667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34806091539809616710965111 52209137309714425066447667)
        ·
          refine ⟨78313705964571637599671501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52209137309714425066447667 78313705964571637599671501)
          ·
            refine ⟨29367639736714364099876813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78313705964571637599671501 29367639736714364099876813)
            ·
              refine ⟨11012864901267886537453805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29367639736714364099876813 11012864901267886537453805)
              ·
                refine ⟨4129824337975457451545177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11012864901267886537453805 4129824337975457451545177)
                ·
                  refine ⟨3097368253481593088658883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129824337975457451545177 3097368253481593088658883)
                  ·
                    refine ⟨4646052380222389632988325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3097368253481593088658883 4646052380222389632988325)
                    ·
                      refine ⟨871134821291698056185311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4646052380222389632988325 871134821291698056185311)
                      ·
                        rfl

theorem cell23_1696529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_1696529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696529 prefixEnd_1696529 := by exact prefixLift 1696529
  have htrace : WordTrace (prefixWord ++ tailWord_1696529) baseStart_1696529 baseEnd_1696529 := by
    simpa [prefixWord, tailWord_1696529, baseEnd_1696529] using wordTrace_append hprefix tailTrace_1696529
  have hstable : (prefixWord ++ tailWord_1696529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696529).length < 2 ^ (prefixWord ++ tailWord_1696529).sum := by decide
  have hdescent : baseEnd_1696529 < baseStart_1696529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696546 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1696546 : Nat := 118140960795 + 1696546 * 2 ^ 59
def prefixEnd_1696546 : Nat := 4983230072969 + 3 ^ 40 * 1696546 * 2
def baseEnd_1696546 : Nat := 871143550462824489672733

theorem tailTrace_1696546 : CollatzResearch.WordTrace tailWord_1696546 prefixEnd_1696546 871143550462824489672733 := by
  unfold tailWord_1696546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15469529027927765958493373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41252077407807375889315661 15469529027927765958493373)
  ·
    refine ⟨5801073385472912234435015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15469529027927765958493373 5801073385472912234435015)
    ·
      refine ⟨8701610078209368351652523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5801073385472912234435015 8701610078209368351652523)
      ·
        refine ⟨13052415117314052527478785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8701610078209368351652523 13052415117314052527478785)
        ·
          refine ⟨9789311337985539395609089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13052415117314052527478785 9789311337985539395609089)
          ·
            refine ⟨7341983503489154546706817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9789311337985539395609089 7341983503489154546706817)
            ·
              refine ⟨5506487627616865910030113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7341983503489154546706817 5506487627616865910030113)
              ·
                refine ⟨4129865720712649432522585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5506487627616865910030113 4129865720712649432522585)
                ·
                  refine ⟨3097399290534487074391939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129865720712649432522585 3097399290534487074391939)
                  ·
                    refine ⟨4646098935801730611587909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3097399290534487074391939 4646098935801730611587909)
                    ·
                      refine ⟨871143550462824489672733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4646098935801730611587909 871143550462824489672733)
                      ·
                        rfl

theorem cell23_1696546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1696546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696546 prefixEnd_1696546 := by exact prefixLift 1696546
  have htrace : WordTrace (prefixWord ++ tailWord_1696546) baseStart_1696546 baseEnd_1696546 := by
    simpa [prefixWord, tailWord_1696546, baseEnd_1696546] using wordTrace_append hprefix tailTrace_1696546
  have hstable : (prefixWord ++ tailWord_1696546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696546).length < 2 ^ (prefixWord ++ tailWord_1696546).sum := by decide
  have hdescent : baseEnd_1696546 < baseStart_1696546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696573 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_1696573 : Nat := 118140960795 + 1696573 * 2 ^ 59
def prefixEnd_1696573 : Nat := 4983230072969 + 3 ^ 40 * 1696573 * 2
def baseEnd_1696573 : Nat := 290385804813498628011703

theorem tailTrace_1696573 : CollatzResearch.WordTrace tailWord_1696573 prefixEnd_1696573 290385804813498628011703 := by
  unfold tailWord_1696573
  simp only [CollatzResearch.WordTrace]
  refine ⟨61879100882613247445206373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41252733921742164963470915 61879100882613247445206373)
  ·
    refine ⟨11602331415489983895976195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61879100882613247445206373 11602331415489983895976195)
    ·
      refine ⟨17403497123234975843964293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11602331415489983895976195 17403497123234975843964293)
      ·
        refine ⟨3263155710606557970743305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17403497123234975843964293 3263155710606557970743305)
        ·
          refine ⟨2447366782954918478057479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3263155710606557970743305 2447366782954918478057479)
          ·
            refine ⟨3671050174432377717086219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447366782954918478057479 3671050174432377717086219)
            ·
              refine ⟨5506575261648566575629329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671050174432377717086219 5506575261648566575629329)
              ·
                refine ⟨4129931446236424931721997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5506575261648566575629329 4129931446236424931721997)
                ·
                  refine ⟨1548724292338659349395749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4129931446236424931721997 1548724292338659349395749)
                  ·
                    refine ⟨290385804813498628011703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1548724292338659349395749 290385804813498628011703)
                    ·
                      rfl

theorem cell23_1696573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_1696573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696573 prefixEnd_1696573 := by exact prefixLift 1696573
  have htrace : WordTrace (prefixWord ++ tailWord_1696573) baseStart_1696573 baseEnd_1696573 := by
    simpa [prefixWord, tailWord_1696573, baseEnd_1696573] using wordTrace_append hprefix tailTrace_1696573
  have hstable : (prefixWord ++ tailWord_1696573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696573).length < 2 ^ (prefixWord ++ tailWord_1696573).sum := by decide
  have hdescent : baseEnd_1696573 < baseStart_1696573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696619 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 4]
def baseStart_1696619 : Nat := 118140960795 + 1696619 * 2 ^ 59
def prefixEnd_1696619 : Nat := 4983230072969 + 3 ^ 40 * 1696619 * 2
def baseEnd_1696619 : Nat := 871181034550602704059897

theorem tailTrace_1696619 : CollatzResearch.WordTrace tailWord_1696619 prefixEnd_1696619 871181034550602704059897 := by
  unfold tailWord_1696619
  simp only [CollatzResearch.WordTrace]
  refine ⟨61880778640446597301380911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41253852426964398200920607 61880778640446597301380911)
  ·
    refine ⟨92821167960669895952071367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61880778640446597301380911 92821167960669895952071367)
    ·
      refine ⟨139231751941004843928107051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92821167960669895952071367 139231751941004843928107051)
      ·
        refine ⟨208847627911507265892160577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139231751941004843928107051 208847627911507265892160577)
        ·
          refine ⟨156635720933630449419120433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208847627911507265892160577 156635720933630449419120433)
          ·
            refine ⟨117476790700222837064340325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156635720933630449419120433 117476790700222837064340325)
            ·
              refine ⟨22026898256291781949563811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117476790700222837064340325 22026898256291781949563811)
              ·
                refine ⟨33040347384437672924345717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22026898256291781949563811 33040347384437672924345717)
                ·
                  refine ⟨3097532567291031836657411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33040347384437672924345717 3097532567291031836657411)
                  ·
                    refine ⟨4646298850936547754986117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3097532567291031836657411 4646298850936547754986117)
                    ·
                      refine ⟨871181034550602704059897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4646298850936547754986117 871181034550602704059897)
                      ·
                        rfl

theorem cell23_1696619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 4].length) (baseStart_1696619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696619 prefixEnd_1696619 := by exact prefixLift 1696619
  have htrace : WordTrace (prefixWord ++ tailWord_1696619) baseStart_1696619 baseEnd_1696619 := by
    simpa [prefixWord, tailWord_1696619, baseEnd_1696619] using wordTrace_append hprefix tailTrace_1696619
  have hstable : (prefixWord ++ tailWord_1696619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696619).length < 2 ^ (prefixWord ++ tailWord_1696619).sum := by decide
  have hdescent : baseEnd_1696619 < baseStart_1696619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696630 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1696630 : Nat := 118140960795 + 1696630 * 2 ^ 59
def prefixEnd_1696630 : Nat := 4983230072969 + 3 ^ 40 * 1696630 * 2
def baseEnd_1696630 : Nat := 871186682837802161022347

theorem tailTrace_1696630 : CollatzResearch.WordTrace tailWord_1696630 prefixEnd_1696630 871186682837802161022347 := by
  unfold tailWord_1696630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3867573740212921636251959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41254119895604497453354229 3867573740212921636251959)
  ·
    refine ⟨5801360610319382454377939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3867573740212921636251959 5801360610319382454377939)
    ·
      refine ⟨8702040915479073681566909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5801360610319382454377939 8702040915479073681566909)
      ·
        refine ⟨3263265343304652630587591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8702040915479073681566909 3263265343304652630587591)
        ·
          refine ⟨4894898014956978945881387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263265343304652630587591 4894898014956978945881387)
          ·
            refine ⟨7342347022435468418822081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894898014956978945881387 7342347022435468418822081)
            ·
              refine ⟨5506760266826601314116561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7342347022435468418822081 5506760266826601314116561)
              ·
                refine ⟨4130070200119950985587421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5506760266826601314116561 4130070200119950985587421)
                ·
                  refine ⟨1548776325044981619595283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4130070200119950985587421 1548776325044981619595283)
                  ·
                    refine ⟨2323164487567472429392925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1548776325044981619595283 2323164487567472429392925)
                    ·
                      refine ⟨871186682837802161022347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2323164487567472429392925 871186682837802161022347)
                      ·
                        rfl

theorem cell23_1696630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1696630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696630 prefixEnd_1696630 := by exact prefixLift 1696630
  have htrace : WordTrace (prefixWord ++ tailWord_1696630) baseStart_1696630 baseEnd_1696630 := by
    simpa [prefixWord, tailWord_1696630, baseEnd_1696630] using wordTrace_append hprefix tailTrace_1696630
  have hstable : (prefixWord ++ tailWord_1696630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696630).length < 2 ^ (prefixWord ++ tailWord_1696630).sum := by decide
  have hdescent : baseEnd_1696630 < baseStart_1696630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696647 : List Nat := [1, 1, 4, 2, 3, 3, 1, 3, 1, 1, 3]
def baseStart_1696647 : Nat := 118140960795 + 1696647 * 2 ^ 59
def prefixEnd_1696647 : Nat := 4983230072969 + 3 ^ 40 * 1696647 * 2
def baseEnd_1696647 : Nat := 871195412008928594509769

theorem tailTrace_1696647 : CollatzResearch.WordTrace tailWord_1696647 prefixEnd_1696647 871195412008928594509769 := by
  unfold tailWord_1696647
  simp only [CollatzResearch.WordTrace]
  refine ⟨61881799884345158083400195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41254533256230105388933463 61881799884345158083400195)
  ·
    refine ⟨92822699826517737125100293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61881799884345158083400195 92822699826517737125100293)
    ·
      refine ⟨17404256217472075710956305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92822699826517737125100293 17404256217472075710956305)
      ·
        refine ⟨13053192163104056783217229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17404256217472075710956305 13053192163104056783217229)
        ·
          refine ⟨4894947061164021293706461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13053192163104056783217229 4894947061164021293706461)
          ·
            refine ⟨1835605147936507985139923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4894947061164021293706461 1835605147936507985139923)
            ·
              refine ⟨2753407721904761977709885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835605147936507985139923 2753407721904761977709885)
              ·
                refine ⟨1032527895714285741641207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2753407721904761977709885 1032527895714285741641207)
                ·
                  refine ⟨1548791843571428612461811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032527895714285741641207 1548791843571428612461811)
                  ·
                    refine ⟨2323187765357142918692717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1548791843571428612461811 2323187765357142918692717)
                    ·
                      refine ⟨871195412008928594509769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2323187765357142918692717 871195412008928594509769)
                      ·
                        rfl

theorem cell23_1696647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_1696647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696647 prefixEnd_1696647 := by exact prefixLift 1696647
  have htrace : WordTrace (prefixWord ++ tailWord_1696647) baseStart_1696647 baseEnd_1696647 := by
    simpa [prefixWord, tailWord_1696647, baseEnd_1696647] using wordTrace_append hprefix tailTrace_1696647
  have hstable : (prefixWord ++ tailWord_1696647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696647).length < 2 ^ (prefixWord ++ tailWord_1696647).sum := by decide
  have hdescent : baseEnd_1696647 < baseStart_1696647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696710 : List Nat := [6, 1, 3, 1, 12]
def baseStart_1696710 : Nat := 118140960795 + 1696710 * 2 ^ 59
def prefixEnd_1696710 : Nat := 4983230072969 + 3 ^ 40 * 1696710 * 2
def baseEnd_1696710 : Nat := 1195099809725873591251

theorem tailTrace_1696710 : CollatzResearch.WordTrace tailWord_1696710 prefixEnd_1696710 1195099809725873591251 := by
  unfold tailWord_1696710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933878052597403745091987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41256065122077946561962389 1933878052597403745091987)
  ·
    refine ⟨2900817078896105617637981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1933878052597403745091987 2900817078896105617637981)
    ·
      refine ⟨1087806404586039606614243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2900817078896105617637981 1087806404586039606614243)
      ·
        refine ⟨1631709606879059409921365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087806404586039606614243 1631709606879059409921365)
        ·
          refine ⟨1195099809725873591251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1631709606879059409921365 1195099809725873591251)
          ·
            rfl

theorem cell23_1696710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 12].length) (baseStart_1696710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696710 prefixEnd_1696710 := by exact prefixLift 1696710
  have htrace : WordTrace (prefixWord ++ tailWord_1696710) baseStart_1696710 baseEnd_1696710 := by
    simpa [prefixWord, tailWord_1696710, baseEnd_1696710] using wordTrace_append hprefix tailTrace_1696710
  have hstable : (prefixWord ++ tailWord_1696710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696710).length < 2 ^ (prefixWord ++ tailWord_1696710).sum := by decide
  have hdescent : baseEnd_1696710 < baseStart_1696710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696816 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_1696816 : Nat := 118140960795 + 1696816 * 2 ^ 59
def prefixEnd_1696816 : Nat := 4983230072969 + 3 ^ 40 * 1696816 * 2
def baseEnd_1696816 : Nat := 871282190239538433296491

theorem tailTrace_1696816 : CollatzResearch.WordTrace tailWord_1696816 prefixEnd_1696816 871282190239538433296491 := by
  unfold tailWord_1696816
  simp only [CollatzResearch.WordTrace]
  refine ⟨30943981910366449973151151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41258642547155266630868201 30943981910366449973151151)
  ·
    refine ⟨46415972865549674959726727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30943981910366449973151151 46415972865549674959726727)
    ·
      refine ⟨69623959298324512439590091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46415972865549674959726727 69623959298324512439590091)
      ·
        refine ⟨104435938947486768659385137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69623959298324512439590091 104435938947486768659385137)
        ·
          refine ⟨78326954210615076494538853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104435938947486768659385137 78326954210615076494538853)
          ·
            refine ⟨14686303914490326842726035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78326954210615076494538853 14686303914490326842726035)
            ·
              refine ⟨22029455871735490264089053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14686303914490326842726035 22029455871735490264089053)
              ·
                refine ⟨8261045951900808849033395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22029455871735490264089053 8261045951900808849033395)
                ·
                  refine ⟨12391568927851213273550093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8261045951900808849033395 12391568927851213273550093)
                  ·
                    refine ⟨4646838347944204977581285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12391568927851213273550093 4646838347944204977581285)
                    ·
                      refine ⟨871282190239538433296491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4646838347944204977581285 871282190239538433296491)
                      ·
                        rfl

theorem cell23_1696816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_1696816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696816 prefixEnd_1696816 := by exact prefixLift 1696816
  have htrace : WordTrace (prefixWord ++ tailWord_1696816) baseStart_1696816 baseEnd_1696816 := by
    simpa [prefixWord, tailWord_1696816, baseEnd_1696816] using wordTrace_append hprefix tailTrace_1696816
  have hstable : (prefixWord ++ tailWord_1696816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696816).length < 2 ^ (prefixWord ++ tailWord_1696816).sum := by decide
  have hdescent : baseEnd_1696816 < baseStart_1696816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696830 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1696830 : Nat := 118140960795 + 1696830 * 2 ^ 59
def prefixEnd_1696830 : Nat := 4983230072969 + 3 ^ 40 * 1696830 * 2
def baseEnd_1696830 : Nat := 290429792989567126173809

theorem tailTrace_1696830 : CollatzResearch.WordTrace tailWord_1696830 prefixEnd_1696830 290429792989567126173809 := by
  unfold tailWord_1696830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7736059305335272542163993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41258982961788120224874629 7736059305335272542163993)
  ·
    refine ⟨5802044479001454406622995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7736059305335272542163993 5802044479001454406622995)
    ·
      refine ⟨8703066718502181609934493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5802044479001454406622995 8703066718502181609934493)
      ·
        refine ⟨3263650019438318103725435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8703066718502181609934493 3263650019438318103725435)
        ·
          refine ⟨4895475029157477155588153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263650019438318103725435 4895475029157477155588153)
          ·
            refine ⟨3671606271868107866691115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4895475029157477155588153 3671606271868107866691115)
            ·
              refine ⟨5507409407802161800036673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671606271868107866691115 5507409407802161800036673)
              ·
                refine ⟨4130557055851621350027505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5507409407802161800036673 4130557055851621350027505)
                ·
                  refine ⟨3097917791888716012520629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4130557055851621350027505 3097917791888716012520629)
                  ·
                    refine ⟨290429792989567126173809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3097917791888716012520629 290429792989567126173809)
                    ·
                      rfl

theorem cell23_1696830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1696830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696830 prefixEnd_1696830 := by exact prefixLift 1696830
  have htrace : WordTrace (prefixWord ++ tailWord_1696830) baseStart_1696830 baseEnd_1696830 := by
    simpa [prefixWord, tailWord_1696830, baseEnd_1696830] using wordTrace_append hprefix tailTrace_1696830
  have hstable : (prefixWord ++ tailWord_1696830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696830).length < 2 ^ (prefixWord ++ tailWord_1696830).sum := by decide
  have hdescent : baseEnd_1696830 < baseStart_1696830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696853 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_1696853 : Nat := 118140960795 + 1696853 * 2 ^ 59
def prefixEnd_1696853 : Nat := 4983230072969 + 3 ^ 40 * 1696853 * 2
def baseEnd_1696853 : Nat := 871301189023754788533821

theorem tailTrace_1696853 : CollatzResearch.WordTrace tailWord_1696853 prefixEnd_1696853 871301189023754788533821 := by
  unfold tailWord_1696853
  simp only [CollatzResearch.WordTrace]
  refine ⟨61889313321598855265399213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41259542214399236843599475 61889313321598855265399213)
  ·
    refine ⟨23208492495599570724524705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61889313321598855265399213 23208492495599570724524705)
    ·
      refine ⟨17406369371699678043393529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23208492495599570724524705 17406369371699678043393529)
      ·
        refine ⟨13054777028774758532545147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17406369371699678043393529 13054777028774758532545147)
        ·
          refine ⟨19582165543162137798817721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13054777028774758532545147 19582165543162137798817721)
          ·
            refine ⟨14686624157371603349113291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19582165543162137798817721 14686624157371603349113291)
            ·
              refine ⟨22029936236057405023669937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14686624157371603349113291 22029936236057405023669937)
              ·
                refine ⟨16522452177043053767752453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22029936236057405023669937 16522452177043053767752453)
                ·
                  refine ⟨3097959783195572581453585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16522452177043053767752453 3097959783195572581453585)
                  ·
                    refine ⟨2323469837396679436090189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3097959783195572581453585 2323469837396679436090189)
                    ·
                      refine ⟨871301189023754788533821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2323469837396679436090189 871301189023754788533821)
                      ·
                        rfl

theorem cell23_1696853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_1696853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696853 prefixEnd_1696853 := by exact prefixLift 1696853
  have htrace : WordTrace (prefixWord ++ tailWord_1696853) baseStart_1696853 baseEnd_1696853 := by
    simpa [prefixWord, tailWord_1696853, baseEnd_1696853] using wordTrace_append hprefix tailTrace_1696853
  have hstable : (prefixWord ++ tailWord_1696853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696853).length < 2 ^ (prefixWord ++ tailWord_1696853).sum := by decide
  have hdescent : baseEnd_1696853 < baseStart_1696853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696927 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 1, 5, 2]
def baseStart_1696927 : Nat := 118140960795 + 1696927 * 2 ^ 59
def prefixEnd_1696927 : Nat := 4983230072969 + 3 ^ 40 * 1696927 * 2
def baseEnd_1696927 : Nat := 871339186592187499008481

theorem tailTrace_1696927 : CollatzResearch.WordTrace tailWord_1696927 prefixEnd_1696927 871339186592187499008481 := by
  unfold tailWord_1696927
  simp only [CollatzResearch.WordTrace]
  refine ⟨61892012323330765903593035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41261341548887177269062023 61892012323330765903593035)
  ·
    refine ⟨92838018484996148855389553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61892012323330765903593035 92838018484996148855389553)
    ·
      refine ⟨69628513863747111641542165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92838018484996148855389553 69628513863747111641542165)
      ·
        refine ⟨3263836587363145858197289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69628513863747111641542165 3263836587363145858197289)
        ·
          refine ⟨2447877440522359393647967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3263836587363145858197289 2447877440522359393647967)
          ·
            refine ⟨3671816160783539090471951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447877440522359393647967 3671816160783539090471951)
            ·
              refine ⟨5507724241175308635707927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671816160783539090471951 5507724241175308635707927)
              ·
                refine ⟨8261586361762962953561891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5507724241175308635707927 8261586361762962953561891)
                ·
                  refine ⟨12392379542644444430342837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8261586361762962953561891 12392379542644444430342837)
                  ·
                    refine ⟨1161785582122916665344641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12392379542644444430342837 1161785582122916665344641)
                    ·
                      refine ⟨871339186592187499008481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161785582122916665344641 871339186592187499008481)
                      ·
                        rfl

theorem cell23_1696927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_1696927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696927 prefixEnd_1696927 := by exact prefixLift 1696927
  have htrace : WordTrace (prefixWord ++ tailWord_1696927) baseStart_1696927 baseEnd_1696927 := by
    simpa [prefixWord, tailWord_1696927, baseEnd_1696927] using wordTrace_append hprefix tailTrace_1696927
  have hstable : (prefixWord ++ tailWord_1696927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696927).length < 2 ^ (prefixWord ++ tailWord_1696927).sum := by decide
  have hdescent : baseEnd_1696927 < baseStart_1696927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696933 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_1696933 : Nat := 118140960795 + 1696933 * 2 ^ 59
def prefixEnd_1696933 : Nat := 4983230072969 + 3 ^ 40 * 1696933 * 2
def baseEnd_1696933 : Nat := 290447422492038158511151

theorem tailTrace_1696933 : CollatzResearch.WordTrace tailWord_1696933 prefixEnd_1696933 290447422492038158511151 := by
  unfold tailWord_1696933
  simp only [CollatzResearch.WordTrace]
  refine ⟨61892231161309028928311453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41261487440872685952207635 61892231161309028928311453)
  ·
    refine ⟨23209586685490885848116795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61892231161309028928311453 23209586685490885848116795)
    ·
      refine ⟨34814380028236328772175193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23209586685490885848116795 34814380028236328772175193)
      ·
        refine ⟨26110785021177246579131395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34814380028236328772175193 26110785021177246579131395)
        ·
          refine ⟨39166177531765869868697093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26110785021177246579131395 39166177531765869868697093)
          ·
            refine ⟨7343658287206100600380705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39166177531765869868697093 7343658287206100600380705)
            ·
              refine ⟨5507743715404575450285529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343658287206100600380705 5507743715404575450285529)
              ·
                refine ⟨4130807786553431587714147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5507743715404575450285529 4130807786553431587714147)
                ·
                  refine ⟨6196211679830147381571221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130807786553431587714147 6196211679830147381571221)
                  ·
                    refine ⟨290447422492038158511151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6196211679830147381571221 290447422492038158511151)
                    ·
                      rfl

theorem cell23_1696933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_1696933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696933 prefixEnd_1696933 := by exact prefixLift 1696933
  have htrace : WordTrace (prefixWord ++ tailWord_1696933) baseStart_1696933 baseEnd_1696933 := by
    simpa [prefixWord, tailWord_1696933, baseEnd_1696933] using wordTrace_append hprefix tailTrace_1696933
  have hstable : (prefixWord ++ tailWord_1696933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696933).length < 2 ^ (prefixWord ++ tailWord_1696933).sum := by decide
  have hdescent : baseEnd_1696933 < baseStart_1696933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696957 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_1696957 : Nat := 118140960795 + 1696957 * 2 ^ 59
def prefixEnd_1696957 : Nat := 4983230072969 + 3 ^ 40 * 1696957 * 2
def baseEnd_1696957 : Nat := 871354591011822381633343

theorem tailTrace_1696957 : CollatzResearch.WordTrace tailWord_1696957 prefixEnd_1696957 871354591011822381633343 := by
  unfold tailWord_1696957
  simp only [CollatzResearch.WordTrace]
  refine ⟨61893106513222081027185125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41262071008814720684790083 61893106513222081027185125)
  ·
    refine ⟨11604957471229140192597211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61893106513222081027185125 11604957471229140192597211)
    ·
      refine ⟨17407436206843710288895817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11604957471229140192597211 17407436206843710288895817)
      ·
        refine ⟨13055577155132782716671863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17407436206843710288895817 13055577155132782716671863)
        ·
          refine ⟨19583365732699174075007795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055577155132782716671863 19583365732699174075007795)
          ·
            refine ⟨29375048599048761112511693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19583365732699174075007795 29375048599048761112511693)
            ·
              refine ⟨11015643224643285417191885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29375048599048761112511693 11015643224643285417191885)
              ·
                refine ⟨4130866209241232031446957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11015643224643285417191885 4130866209241232031446957)
                ·
                  refine ⟨1549074828465462011792609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4130866209241232031446957 1549074828465462011792609)
                  ·
                    refine ⟨1161806121349096508844457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1549074828465462011792609 1161806121349096508844457)
                    ·
                      refine ⟨871354591011822381633343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161806121349096508844457 871354591011822381633343)
                      ·
                        rfl

theorem cell23_1696957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_1696957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696957 prefixEnd_1696957 := by exact prefixLift 1696957
  have htrace : WordTrace (prefixWord ++ tailWord_1696957) baseStart_1696957 baseEnd_1696957 := by
    simpa [prefixWord, tailWord_1696957, baseEnd_1696957] using wordTrace_append hprefix tailTrace_1696957
  have hstable : (prefixWord ++ tailWord_1696957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696957).length < 2 ^ (prefixWord ++ tailWord_1696957).sum := by decide
  have hdescent : baseEnd_1696957 < baseStart_1696957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696960 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 5]
def baseStart_1696960 : Nat := 118140960795 + 1696960 * 2 ^ 59
def prefixEnd_1696960 : Nat := 4983230072969 + 3 ^ 40 * 1696960 * 2
def baseEnd_1696960 : Nat := 871356131453785869895829

theorem tailTrace_1696960 : CollatzResearch.WordTrace tailWord_1696960 prefixEnd_1696960 871356131453785869895829 := by
  unfold tailWord_1696960
  simp only [CollatzResearch.WordTrace]
  refine ⟨30946607966105606269772167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41262143954807475026362889 30946607966105606269772167)
  ·
    refine ⟨46419911949158409404658251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30946607966105606269772167 46419911949158409404658251)
    ·
      refine ⟨69629867923737614106987377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46419911949158409404658251 69629867923737614106987377)
      ·
        refine ⟨52222400942803210580240533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69629867923737614106987377 52222400942803210580240533)
        ·
          refine ⟨2447925044193900495948775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52222400942803210580240533 2447925044193900495948775)
          ·
            refine ⟨3671887566290850743923163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447925044193900495948775 3671887566290850743923163)
            ·
              refine ⟨5507831349436276115884745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671887566290850743923163 5507831349436276115884745)
              ·
                refine ⟨4130873512077207086913559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5507831349436276115884745 4130873512077207086913559)
                ·
                  refine ⟨6196310268115810630370339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130873512077207086913559 6196310268115810630370339)
                  ·
                    refine ⟨9294465402173715945555509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6196310268115810630370339 9294465402173715945555509)
                    ·
                      refine ⟨871356131453785869895829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9294465402173715945555509 871356131453785869895829)
                      ·
                        rfl

theorem cell23_1696960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_1696960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696960 prefixEnd_1696960 := by exact prefixLift 1696960
  have htrace : WordTrace (prefixWord ++ tailWord_1696960) baseStart_1696960 baseEnd_1696960 := by
    simpa [prefixWord, tailWord_1696960, baseEnd_1696960] using wordTrace_append hprefix tailTrace_1696960
  have hstable : (prefixWord ++ tailWord_1696960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696960).length < 2 ^ (prefixWord ++ tailWord_1696960).sum := by decide
  have hdescent : baseEnd_1696960 < baseStart_1696960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696970 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_1696970 : Nat := 118140960795 + 1696970 * 2 ^ 59
def prefixEnd_1696970 : Nat := 4983230072969 + 3 ^ 40 * 1696970 * 2
def baseEnd_1696970 : Nat := 871361266260330830770783

theorem tailTrace_1696970 : CollatzResearch.WordTrace tailWord_1696970 prefixEnd_1696970 871361266260330830770783 := by
  unfold tailWord_1696970
  simp only [CollatzResearch.WordTrace]
  refine ⟨15473395165543746061852091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41262387108116656164938909 15473395165543746061852091)
  ·
    refine ⟨23210092748315619092778137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15473395165543746061852091 23210092748315619092778137)
    ·
      refine ⟨17407569561236714319583603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23210092748315619092778137 17407569561236714319583603)
      ·
        refine ⟨26111354341855071479375405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17407569561236714319583603 26111354341855071479375405)
        ·
          refine ⟨9791757878195651804765777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26111354341855071479375405 9791757878195651804765777)
          ·
            refine ⟨7343818408646738853574333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9791757878195651804765777 7343818408646738853574333)
            ·
              refine ⟨2753931903242527070090375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7343818408646738853574333 2753931903242527070090375)
              ·
                refine ⟨4130897854863790605135563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753931903242527070090375 4130897854863790605135563)
                ·
                  refine ⟨6196346782295685907703345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130897854863790605135563 6196346782295685907703345)
                  ·
                    refine ⟨4647260086721764430777509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196346782295685907703345 4647260086721764430777509)
                    ·
                      refine ⟨871361266260330830770783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4647260086721764430777509 871361266260330830770783)
                      ·
                        rfl

theorem cell23_1696970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_1696970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1696970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1696970 prefixEnd_1696970 := by exact prefixLift 1696970
  have htrace : WordTrace (prefixWord ++ tailWord_1696970) baseStart_1696970 baseEnd_1696970 := by
    simpa [prefixWord, tailWord_1696970, baseEnd_1696970] using wordTrace_append hprefix tailTrace_1696970
  have hstable : (prefixWord ++ tailWord_1696970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696970).length < 2 ^ (prefixWord ++ tailWord_1696970).sum := by decide
  have hdescent : baseEnd_1696970 < baseStart_1696970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697033 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_1697033 : Nat := 118140960795 + 1697033 * 2 ^ 59
def prefixEnd_1697033 : Nat := 4983230072969 + 3 ^ 40 * 1697033 * 2
def baseEnd_1697033 : Nat := 871393615541564084282993

theorem tailTrace_1697033 : CollatzResearch.WordTrace tailWord_1697033 prefixEnd_1697033 871393615541564084282993 := by
  unfold tailWord_1697033
  simp only [CollatzResearch.WordTrace]
  refine ⟨61895878460946746006951753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41263918973964497337967835 61895878460946746006951753)
  ·
    refine ⟨46421908845710059505213815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61895878460946746006951753 46421908845710059505213815)
    ·
      refine ⟨69632863268565089257820723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46421908845710059505213815 69632863268565089257820723)
      ·
        refine ⟨104449294902847633886731085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69632863268565089257820723 104449294902847633886731085)
        ·
          refine ⟨39168485588567862707524157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104449294902847633886731085 39168485588567862707524157)
          ·
            refine ⟨14688182095712948515321559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39168485588567862707524157 14688182095712948515321559)
            ·
              refine ⟨22032273143569422772982339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14688182095712948515321559 22032273143569422772982339)
              ·
                refine ⟨33048409715354134159473509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22032273143569422772982339 33048409715354134159473509)
                ·
                  refine ⟨6196576821628900154901283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33048409715354134159473509 6196576821628900154901283)
                  ·
                    refine ⟨9294865232443350232351925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6196576821628900154901283 9294865232443350232351925)
                    ·
                      refine ⟨871393615541564084282993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9294865232443350232351925 871393615541564084282993)
                      ·
                        rfl

theorem cell23_1697033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_1697033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697033 prefixEnd_1697033 := by exact prefixLift 1697033
  have htrace : WordTrace (prefixWord ++ tailWord_1697033) baseStart_1697033 baseEnd_1697033 := by
    simpa [prefixWord, tailWord_1697033, baseEnd_1697033] using wordTrace_append hprefix tailTrace_1697033
  have hstable : (prefixWord ++ tailWord_1697033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697033).length < 2 ^ (prefixWord ++ tailWord_1697033).sum := by decide
  have hdescent : baseEnd_1697033 < baseStart_1697033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697043 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 4]
def baseStart_1697043 : Nat := 118140960795 + 1697043 * 2 ^ 59
def prefixEnd_1697043 : Nat := 4983230072969 + 3 ^ 40 * 1697043 * 2
def baseEnd_1697043 : Nat := 871398750348109045157947

theorem tailTrace_1697043 : CollatzResearch.WordTrace tailWord_1697043 prefixEnd_1697043 871398750348109045157947 := by
  unfold tailWord_1697043
  simp only [CollatzResearch.WordTrace]
  refine ⟨61896243190910517714815783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41264162127273678476543855 61896243190910517714815783)
  ·
    refine ⟨92844364786365776572223675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61896243190910517714815783 92844364786365776572223675)
    ·
      refine ⟨139266547179548664858335513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92844364786365776572223675 139266547179548664858335513)
      ·
        refine ⟨104449910384661498643751635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139266547179548664858335513 104449910384661498643751635)
        ·
          refine ⟨156674865576992247965627453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104449910384661498643751635 156674865576992247965627453)
          ·
            refine ⟨58753074591372092987110295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156674865576992247965627453 58753074591372092987110295)
            ·
              refine ⟨88129611887058139480665443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58753074591372092987110295 88129611887058139480665443)
              ·
                refine ⟨132194417830587209220998165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88129611887058139480665443 132194417830587209220998165)
                ·
                  refine ⟨6196613335808775432234289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132194417830587209220998165 6196613335808775432234289)
                  ·
                    refine ⟨4647460001856581574175717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196613335808775432234289 4647460001856581574175717)
                    ·
                      refine ⟨871398750348109045157947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4647460001856581574175717 871398750348109045157947)
                      ·
                        rfl

theorem cell23_1697043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_1697043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697043 prefixEnd_1697043 := by exact prefixLift 1697043
  have htrace : WordTrace (prefixWord ++ tailWord_1697043) baseStart_1697043 baseEnd_1697043 := by
    simpa [prefixWord, tailWord_1697043, baseEnd_1697043] using wordTrace_append hprefix tailTrace_1697043
  have hstable : (prefixWord ++ tailWord_1697043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697043).length < 2 ^ (prefixWord ++ tailWord_1697043).sum := by decide
  have hdescent : baseEnd_1697043 < baseStart_1697043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697047 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 1, 4, 2]
def baseStart_1697047 : Nat := 118140960795 + 1697047 * 2 ^ 59
def prefixEnd_1697047 : Nat := 4983230072969 + 3 ^ 40 * 1697047 * 2
def baseEnd_1697047 : Nat := 871400804270727029507929

theorem tailTrace_1697047 : CollatzResearch.WordTrace tailWord_1697047 prefixEnd_1697047 871400804270727029507929 := by
  unfold tailWord_1697047
  simp only [CollatzResearch.WordTrace]
  refine ⟨61896389082896026397961395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41264259388597350931974263 61896389082896026397961395)
  ·
    refine ⟨92844583624344039596942093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61896389082896026397961395 92844583624344039596942093)
    ·
      refine ⟨34816718859129014848853285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92844583624344039596942093 34816718859129014848853285)
      ·
        refine ⟨6528134786086690284159991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34816718859129014848853285 6528134786086690284159991)
        ·
          refine ⟨9792202179130035426239987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528134786086690284159991 9792202179130035426239987)
          ·
            refine ⟨14688303268695053139359981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9792202179130035426239987 14688303268695053139359981)
            ·
              refine ⟨5508113725760644927259993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14688303268695053139359981 5508113725760644927259993)
              ·
                refine ⟨4131085294320483695444995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5508113725760644927259993 4131085294320483695444995)
                ·
                  refine ⟨6196627941480725543167493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131085294320483695444995 6196627941480725543167493)
                  ·
                    refine ⟨1161867739027636039343905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196627941480725543167493 1161867739027636039343905)
                    ·
                      refine ⟨871400804270727029507929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161867739027636039343905 871400804270727029507929)
                      ·
                        rfl

theorem cell23_1697047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_1697047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697047 prefixEnd_1697047 := by exact prefixLift 1697047
  have htrace : WordTrace (prefixWord ++ tailWord_1697047) baseStart_1697047 baseEnd_1697047 := by
    simpa [prefixWord, tailWord_1697047, baseEnd_1697047] using wordTrace_append hprefix tailTrace_1697047
  have hstable : (prefixWord ++ tailWord_1697047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697047).length < 2 ^ (prefixWord ++ tailWord_1697047).sum := by decide
  have hdescent : baseEnd_1697047 < baseStart_1697047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697050 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1697050 : Nat := 118140960795 + 1697050 * 2 ^ 59
def prefixEnd_1697050 : Nat := 4983230072969 + 3 ^ 40 * 1697050 * 2
def baseEnd_1697050 : Nat := 871402344712690517770415

theorem tailTrace_1697050 : CollatzResearch.WordTrace tailWord_1697050 prefixEnd_1697050 871402344712690517770415 := by
  unfold tailWord_1697050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15474124625471289477580151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41264332334590105273547069 15474124625471289477580151)
  ·
    refine ⟨23211186938206934216370227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15474124625471289477580151 23211186938206934216370227)
    ·
      refine ⟨34816780407310401324555341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23211186938206934216370227 34816780407310401324555341)
      ·
        refine ⟨13056292652741400496708253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34816780407310401324555341 13056292652741400496708253)
        ·
          refine ⟨4896109744778025186265595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13056292652741400496708253 4896109744778025186265595)
          ·
            refine ⟨7344164617167037779398393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4896109744778025186265595 7344164617167037779398393)
            ·
              refine ⟨5508123462875278334548795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7344164617167037779398393 5508123462875278334548795)
              ·
                refine ⟨8262185194312917501823193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508123462875278334548795 8262185194312917501823193)
                ·
                  refine ⟨6196638895734688126367395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8262185194312917501823193 6196638895734688126367395)
                  ·
                    refine ⟨9294958343602032189551093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6196638895734688126367395 9294958343602032189551093)
                    ·
                      refine ⟨871402344712690517770415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9294958343602032189551093 871402344712690517770415)
                      ·
                        rfl

theorem cell23_1697050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1697050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697050 prefixEnd_1697050 := by exact prefixLift 1697050
  have htrace : WordTrace (prefixWord ++ tailWord_1697050) baseStart_1697050 baseEnd_1697050 := by
    simpa [prefixWord, tailWord_1697050, baseEnd_1697050] using wordTrace_append hprefix tailTrace_1697050
  have hstable : (prefixWord ++ tailWord_1697050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697050).length < 2 ^ (prefixWord ++ tailWord_1697050).sum := by decide
  have hdescent : baseEnd_1697050 < baseStart_1697050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697060 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1697060 : Nat := 118140960795 + 1697060 * 2 ^ 59
def prefixEnd_1697060 : Nat := 4983230072969 + 3 ^ 40 * 1697060 * 2
def baseEnd_1697060 : Nat := 871407479519235478645369

theorem tailTrace_1697060 : CollatzResearch.WordTrace tailWord_1697060 prefixEnd_1697060 871407479519235478645369 := by
  unfold tailWord_1697060
  simp only [CollatzResearch.WordTrace]
  refine ⟨30948431615924464809092317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41264575487899286412123089 30948431615924464809092317)
  ·
    refine ⟨11605661855971674303409619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30948431615924464809092317 11605661855971674303409619)
    ·
      refine ⟨17408492783957511455114429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11605661855971674303409619 17408492783957511455114429)
      ·
        refine ⟨6528184793984066795667911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17408492783957511455114429 6528184793984066795667911)
        ·
          refine ⟨9792277190976100193501867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528184793984066795667911 9792277190976100193501867)
          ·
            refine ⟨14688415786464150290252801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9792277190976100193501867 14688415786464150290252801)
            ·
              refine ⟨11016311839848112717689601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14688415786464150290252801 11016311839848112717689601)
              ·
                refine ⟨8262233879886084538267201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11016311839848112717689601 8262233879886084538267201)
                ·
                  refine ⟨6196675409914563403700401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8262233879886084538267201 6196675409914563403700401)
                  ·
                    refine ⟨4647506557435922552775301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196675409914563403700401 4647506557435922552775301)
                    ·
                      refine ⟨871407479519235478645369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4647506557435922552775301 871407479519235478645369)
                      ·
                        rfl

theorem cell23_1697060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1697060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697060 prefixEnd_1697060 := by exact prefixLift 1697060
  have htrace : WordTrace (prefixWord ++ tailWord_1697060) baseStart_1697060 baseEnd_1697060 := by
    simpa [prefixWord, tailWord_1697060, baseEnd_1697060] using wordTrace_append hprefix tailTrace_1697060
  have hstable : (prefixWord ++ tailWord_1697060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697060).length < 2 ^ (prefixWord ++ tailWord_1697060).sum := by decide
  have hdescent : baseEnd_1697060 < baseStart_1697060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697093 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_1697093 : Nat := 118140960795 + 1697093 * 2 ^ 59
def prefixEnd_1697093 : Nat := 4983230072969 + 3 ^ 40 * 1697093 * 2
def baseEnd_1697093 : Nat := 871424424380833849532717

theorem tailTrace_1697093 : CollatzResearch.WordTrace tailWord_1697093 prefixEnd_1697093 871424424380833849532717 := by
  unfold tailWord_1697093
  simp only [CollatzResearch.WordTrace]
  refine ⟨61898066840729376254135933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41265377893819584169423955 61898066840729376254135933)
  ·
    refine ⟨23211775065273516095300975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61898066840729376254135933 23211775065273516095300975)
    ·
      refine ⟨34817662597910274142951463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23211775065273516095300975 34817662597910274142951463)
      ·
        refine ⟨52226493896865411214427195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34817662597910274142951463 52226493896865411214427195)
        ·
          refine ⟨78339740845298116821640793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52226493896865411214427195 78339740845298116821640793)
          ·
            refine ⟨58754805633973587616230595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78339740845298116821640793 58754805633973587616230595)
            ·
              refine ⟨88132208450960381424345893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58754805633973587616230595 88132208450960381424345893)
              ·
                refine ⟨16524789084555071517064855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88132208450960381424345893 16524789084555071517064855)
                ·
                  refine ⟨24787183626832607275597283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16524789084555071517064855 24787183626832607275597283)
                  ·
                    refine ⟨37180775440248910913395925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24787183626832607275597283 37180775440248910913395925)
                    ·
                      refine ⟨871424424380833849532717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37180775440248910913395925 871424424380833849532717)
                      ·
                        rfl

theorem cell23_1697093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_1697093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697093 prefixEnd_1697093 := by exact prefixLift 1697093
  have htrace : WordTrace (prefixWord ++ tailWord_1697093) baseStart_1697093 baseEnd_1697093 := by
    simpa [prefixWord, tailWord_1697093, baseEnd_1697093] using wordTrace_append hprefix tailTrace_1697093
  have hstable : (prefixWord ++ tailWord_1697093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697093).length < 2 ^ (prefixWord ++ tailWord_1697093).sum := by decide
  have hdescent : baseEnd_1697093 < baseStart_1697093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697100 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_1697100 : Nat := 118140960795 + 1697100 * 2 ^ 59
def prefixEnd_1697100 : Nat := 4983230072969 + 3 ^ 40 * 1697100 * 2
def baseEnd_1697100 : Nat := 290476006248471774048395

theorem tailTrace_1697100 : CollatzResearch.WordTrace tailWord_1697100 prefixEnd_1697100 290476006248471774048395 := by
  unfold tailWord_1697100
  simp only [CollatzResearch.WordTrace]
  refine ⟨30949161075852008224820377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41265548101136010966427169 30949161075852008224820377)
  ·
    refine ⟨23211870806889006168615283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30949161075852008224820377 23211870806889006168615283)
    ·
      refine ⟨34817806210333509252922925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23211870806889006168615283 34817806210333509252922925)
      ·
        refine ⟨13056677328875065969846097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34817806210333509252922925 13056677328875065969846097)
        ·
          refine ⟨9792507996656299477384573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13056677328875065969846097 9792507996656299477384573)
          ·
            refine ⟨3672190498746112304019215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9792507996656299477384573 3672190498746112304019215)
            ·
              refine ⟨5508285748119168456028823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672190498746112304019215 5508285748119168456028823)
              ·
                refine ⟨8262428622178752684043235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508285748119168456028823 8262428622178752684043235)
                ·
                  refine ⟨12393642933268129026064853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8262428622178752684043235 12393642933268129026064853)
                  ·
                    refine ⟨290476006248471774048395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12393642933268129026064853 290476006248471774048395)
                    ·
                      rfl

theorem cell23_1697100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_1697100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697100 prefixEnd_1697100 := by exact prefixLift 1697100
  have htrace : WordTrace (prefixWord ++ tailWord_1697100) baseStart_1697100 baseEnd_1697100 := by
    simpa [prefixWord, tailWord_1697100, baseEnd_1697100] using wordTrace_append hprefix tailTrace_1697100
  have hstable : (prefixWord ++ tailWord_1697100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697100).length < 2 ^ (prefixWord ++ tailWord_1697100).sum := by decide
  have hdescent : baseEnd_1697100 < baseStart_1697100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697137 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 2, 4, 2]
def baseStart_1697137 : Nat := 118140960795 + 1697137 * 2 ^ 59
def prefixEnd_1697137 : Nat := 4983230072969 + 3 ^ 40 * 1697137 * 2
def baseEnd_1697137 : Nat := 871447017529631677382515

theorem tailTrace_1697137 : CollatzResearch.WordTrace tailWord_1697137 prefixEnd_1697137 871447017529631677382515 := by
  unfold tailWord_1697137
  simp only [CollatzResearch.WordTrace]
  refine ⟨61899671652569971768737665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41266447768379981179158443 61899671652569971768737665)
  ·
    refine ⟨46424753739427478826553249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61899671652569971768737665 46424753739427478826553249)
    ·
      refine ⟨34818565304570609119914937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46424753739427478826553249 34818565304570609119914937)
      ·
        refine ⟨26113923978427956839936203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34818565304570609119914937 26113923978427956839936203)
        ·
          refine ⟨39170885967641935259904305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26113923978427956839936203 39170885967641935259904305)
          ·
            refine ⟨29378164475731451444928229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39170885967641935259904305 29378164475731451444928229)
            ·
              refine ⟨5508405839199647145924043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29378164475731451444928229 5508405839199647145924043)
              ·
                refine ⟨8262608758799470718886065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508405839199647145924043 8262608758799470718886065)
                ·
                  refine ⟨6196956569099603039164549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8262608758799470718886065 6196956569099603039164549)
                  ·
                    refine ⟨1161929356706175569843353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196956569099603039164549 1161929356706175569843353)
                    ·
                      refine ⟨871447017529631677382515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1161929356706175569843353 871447017529631677382515)
                      ·
                        rfl

theorem cell23_1697137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_1697137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697137 prefixEnd_1697137 := by exact prefixLift 1697137
  have htrace : WordTrace (prefixWord ++ tailWord_1697137) baseStart_1697137 baseEnd_1697137 := by
    simpa [prefixWord, tailWord_1697137, baseEnd_1697137] using wordTrace_append hprefix tailTrace_1697137
  have hstable : (prefixWord ++ tailWord_1697137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697137).length < 2 ^ (prefixWord ++ tailWord_1697137).sum := by decide
  have hdescent : baseEnd_1697137 < baseStart_1697137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697154 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1697154 : Nat := 118140960795 + 1697154 * 2 ^ 59
def prefixEnd_1697154 : Nat := 4983230072969 + 3 ^ 40 * 1697154 * 2
def baseEnd_1697154 : Nat := 871455746700758110869937

theorem tailTrace_1697154 : CollatzResearch.WordTrace tailWord_1697154 prefixEnd_1697154 871455746700758110869937 := by
  unfold tailWord_1697154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475072923377095918026629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41266861129005589114737677 15475072923377095918026629)
  ·
    refine ⟨2901576173133205484629993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15475072923377095918026629 2901576173133205484629993)
    ·
      refine ⟨2176182129849904113472495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2901576173133205484629993 2176182129849904113472495)
      ·
        refine ⟨3264273194774856170208743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176182129849904113472495 3264273194774856170208743)
        ·
          refine ⟨4896409792162284255313115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3264273194774856170208743 4896409792162284255313115)
          ·
            refine ⟨7344614688243426382969673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4896409792162284255313115 7344614688243426382969673)
            ·
              refine ⟨5508461016182569787227255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7344614688243426382969673 5508461016182569787227255)
              ·
                refine ⟨8262691524273854680840883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508461016182569787227255 8262691524273854680840883)
                ·
                  refine ⟨12394037286410782021261325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8262691524273854680840883 12394037286410782021261325)
                  ·
                    refine ⟨4647763982404043257972997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12394037286410782021261325 4647763982404043257972997)
                    ·
                      refine ⟨871455746700758110869937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4647763982404043257972997 871455746700758110869937)
                      ·
                        rfl

theorem cell23_1697154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1697154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697154 prefixEnd_1697154 := by exact prefixLift 1697154
  have htrace : WordTrace (prefixWord ++ tailWord_1697154) baseStart_1697154 baseEnd_1697154 := by
    simpa [prefixWord, tailWord_1697154, baseEnd_1697154] using wordTrace_append hprefix tailTrace_1697154
  have hstable : (prefixWord ++ tailWord_1697154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697154).length < 2 ^ (prefixWord ++ tailWord_1697154).sum := by decide
  have hdescent : baseEnd_1697154 < baseStart_1697154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697160 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 8]
def baseStart_1697160 : Nat := 118140960795 + 1697160 * 2 ^ 59
def prefixEnd_1697160 : Nat := 4983230072969 + 3 ^ 40 * 1697160 * 2
def baseEnd_1697160 : Nat := 96828758620520565266101

theorem tailTrace_1697160 : CollatzResearch.WordTrace tailWord_1697160 prefixEnd_1697160 96828758620520565266101 := by
  unfold tailWord_1697160
  simp only [CollatzResearch.WordTrace]
  refine ⟨30950255265743323348412467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41267007020991097797883289 30950255265743323348412467)
  ·
    refine ⟨46425382898614985022618701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30950255265743323348412467 46425382898614985022618701)
    ·
      refine ⟨17409518586980619383482013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46425382898614985022618701 17409518586980619383482013)
      ·
        refine ⟨6528569470117732268805755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17409518586980619383482013 6528569470117732268805755)
        ·
          refine ⟨9792854205176598403208633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528569470117732268805755 9792854205176598403208633)
          ·
            refine ⟨7344640653882448802406475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9792854205176598403208633 7344640653882448802406475)
            ·
              refine ⟨11016960980823673203609713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344640653882448802406475 11016960980823673203609713)
              ·
                refine ⟨8262720735617754902707285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11016960980823673203609713 8262720735617754902707285)
                ·
                  refine ⟨96828758620520565266101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8262720735617754902707285 96828758620520565266101)
                  ·
                    rfl

theorem cell23_1697160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 8].length) (baseStart_1697160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697160 prefixEnd_1697160 := by exact prefixLift 1697160
  have htrace : WordTrace (prefixWord ++ tailWord_1697160) baseStart_1697160 baseEnd_1697160 := by
    simpa [prefixWord, tailWord_1697160, baseEnd_1697160] using wordTrace_append hprefix tailTrace_1697160
  have hstable : (prefixWord ++ tailWord_1697160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697160).length < 2 ^ (prefixWord ++ tailWord_1697160).sum := by decide
  have hdescent : baseEnd_1697160 < baseStart_1697160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697224 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 1, 5]
def baseStart_1697224 : Nat := 118140960795 + 1697224 * 2 ^ 59
def prefixEnd_1697224 : Nat := 4983230072969 + 3 ^ 40 * 1697224 * 2
def baseEnd_1697224 : Nat := 290497230115524278998205

theorem tailTrace_1697224 : CollatzResearch.WordTrace tailWord_1697224 prefixEnd_1697224 290497230115524278998205 := by
  unfold tailWord_1697224
  simp only [CollatzResearch.WordTrace]
  refine ⟨30951422401627392813577363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41268563202169857084769817 30951422401627392813577363)
  ·
    refine ⟨46427133602441089220366045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30951422401627392813577363 46427133602441089220366045)
    ·
      refine ⟨17410175100915408457637267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46427133602441089220366045 17410175100915408457637267)
      ·
        refine ⟨26115262651373112686455901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17410175100915408457637267 26115262651373112686455901)
        ·
          refine ⟨9793223494264917257420963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26115262651373112686455901 9793223494264917257420963)
          ·
            refine ⟨14689835241397375886131445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9793223494264917257420963 14689835241397375886131445)
            ·
              refine ⟨1377172053881003989324823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14689835241397375886131445 1377172053881003989324823)
              ·
                refine ⟨2065758080821505983987235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377172053881003989324823 2065758080821505983987235)
                ·
                  refine ⟨3098637121232258975980853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065758080821505983987235 3098637121232258975980853)
                  ·
                    refine ⟨290497230115524278998205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3098637121232258975980853 290497230115524278998205)
                    ·
                      rfl

theorem cell23_1697224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_1697224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697224 prefixEnd_1697224 := by exact prefixLift 1697224
  have htrace : WordTrace (prefixWord ++ tailWord_1697224) baseStart_1697224 baseEnd_1697224 := by
    simpa [prefixWord, tailWord_1697224, baseEnd_1697224] using wordTrace_append hprefix tailTrace_1697224
  have hstable : (prefixWord ++ tailWord_1697224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697224).length < 2 ^ (prefixWord ++ tailWord_1697224).sum := by decide
  have hdescent : baseEnd_1697224 < baseStart_1697224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697227 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 4]
def baseStart_1697227 : Nat := 118140960795 + 1697227 * 2 ^ 59
def prefixEnd_1697227 : Nat := 4983230072969 + 3 ^ 40 * 1697227 * 2
def baseEnd_1697227 : Nat := 871493230788536325257101

theorem tailTrace_1697227 : CollatzResearch.WordTrace tailWord_1697227 prefixEnd_1697227 871493230788536325257101 := by
  unfold tailWord_1697227
  simp only [CollatzResearch.WordTrace]
  refine ⟨61902954222243917139513935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41268636148162611426342623 61902954222243917139513935)
  ·
    refine ⟨92854431333365875709270903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61902954222243917139513935 92854431333365875709270903)
    ·
      refine ⟨139281647000048813563906355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92854431333365875709270903 139281647000048813563906355)
      ·
        refine ⟨208922470500073220345859533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139281647000048813563906355 208922470500073220345859533)
        ·
          refine ⟨78345926437527457629697325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208922470500073220345859533 78345926437527457629697325)
          ·
            refine ⟨29379722414072796611136497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78345926437527457629697325 29379722414072796611136497)
            ·
              refine ⟨22034791810554597458352373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29379722414072796611136497 22034791810554597458352373)
              ·
                refine ⟨2065761732239493511720535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22034791810554597458352373 2065761732239493511720535)
                ·
                  refine ⟨3098642598359240267580803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065761732239493511720535 3098642598359240267580803)
                  ·
                    refine ⟨4647963897538860401371205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3098642598359240267580803 4647963897538860401371205)
                    ·
                      refine ⟨871493230788536325257101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4647963897538860401371205 871493230788536325257101)
                      ·
                        rfl

theorem cell23_1697227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 4].length) (baseStart_1697227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697227 prefixEnd_1697227 := by exact prefixLift 1697227
  have htrace : WordTrace (prefixWord ++ tailWord_1697227) baseStart_1697227 baseEnd_1697227 := by
    simpa [prefixWord, tailWord_1697227, baseEnd_1697227] using wordTrace_append hprefix tailTrace_1697227
  have hstable : (prefixWord ++ tailWord_1697227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697227).length < 2 ^ (prefixWord ++ tailWord_1697227).sum := by decide
  have hdescent : baseEnd_1697227 < baseStart_1697227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
