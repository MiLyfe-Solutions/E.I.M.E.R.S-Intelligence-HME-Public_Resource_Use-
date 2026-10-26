import V185TrunkScan23Chunk0524

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3103094 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3103094 : Nat := 118140960795 + 3103094 * 2 ^ 59
def prefixEnd_3103094 : Nat := 4983230072969 + 3 ^ 40 * 3103094 * 2
def baseEnd_3103094 : Nat := 1593378738082987364154137

theorem tailTrace_3103094 : CollatzResearch.WordTrace tailWord_3103094 prefixEnd_3103094 1593378738082987364154137 := by
  unfold tailWord_3103094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7073696013751742444221271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75452757480018586071693557 7073696013751742444221271)
  ·
    refine ⟨10610544020627613666331907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7073696013751742444221271 10610544020627613666331907)
    ·
      refine ⟨15915816030941420499497861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10610544020627613666331907 15915816030941420499497861)
      ·
        refine ⟨2984215505801516343655849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15915816030941420499497861 2984215505801516343655849)
        ·
          refine ⟨2238161629351137257741887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2984215505801516343655849 2238161629351137257741887)
          ·
            refine ⟨3357242444026705886612831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238161629351137257741887 3357242444026705886612831)
            ·
              refine ⟨5035863666040058829919247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357242444026705886612831 5035863666040058829919247)
              ·
                refine ⟨7553795499060088244878871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035863666040058829919247 7553795499060088244878871)
                ·
                  refine ⟨11330693248590132367318307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7553795499060088244878871 11330693248590132367318307)
                  ·
                    refine ⟨16996039872885198550977461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11330693248590132367318307 16996039872885198550977461)
                    ·
                      refine ⟨1593378738082987364154137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16996039872885198550977461 1593378738082987364154137)
                      ·
                        rfl

theorem cell23_3103094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3103094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103094 prefixEnd_3103094 := by exact prefixLift 3103094
  have htrace : WordTrace (prefixWord ++ tailWord_3103094) baseStart_3103094 baseEnd_3103094 := by
    simpa [prefixWord, tailWord_3103094, baseEnd_3103094] using wordTrace_append hprefix tailTrace_3103094
  have hstable : (prefixWord ++ tailWord_3103094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103094).length < 2 ^ (prefixWord ++ tailWord_3103094).sum := by decide
  have hdescent : baseEnd_3103094 < baseStart_3103094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103107 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 3]
def baseStart_3103107 : Nat := 118140960795 + 3103107 * 2 ^ 59
def prefixEnd_3103107 : Nat := 4983230072969 + 3 ^ 40 * 3103107 * 2
def baseEnd_3103107 : Nat := 1593385413331495813291577

theorem tailTrace_3103107 : CollatzResearch.WordTrace tailWord_3103107 prefixEnd_3103107 1593385413331495813291577 := by
  unfold tailWord_3103107
  simp only [CollatzResearch.WordTrace]
  refine ⟨113179610368980782327763575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75453073579320521551842383 113179610368980782327763575)
  ·
    refine ⟨169769415553471173491645363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113179610368980782327763575 169769415553471173491645363)
    ·
      refine ⟨254654123330206760237468045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169769415553471173491645363 254654123330206760237468045)
      ·
        refine ⟨95495296248827535089050517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254654123330206760237468045 95495296248827535089050517)
        ·
          refine ⟨4476342011663790707299243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95495296248827535089050517 4476342011663790707299243)
          ·
            refine ⟨6714513017495686060948865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476342011663790707299243 6714513017495686060948865)
            ·
              refine ⟨5035884763121764545711649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6714513017495686060948865 5035884763121764545711649)
              ·
                refine ⟨3776913572341323409283737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5035884763121764545711649 3776913572341323409283737)
                ·
                  refine ⟨2832685179255992556962803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776913572341323409283737 2832685179255992556962803)
                  ·
                    refine ⟨4249027768883988835444205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2832685179255992556962803 4249027768883988835444205)
                    ·
                      refine ⟨1593385413331495813291577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4249027768883988835444205 1593385413331495813291577)
                      ·
                        rfl

theorem cell23_3103107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_3103107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103107 prefixEnd_3103107 := by exact prefixLift 3103107
  have htrace : WordTrace (prefixWord ++ tailWord_3103107) baseStart_3103107 baseEnd_3103107 := by
    simpa [prefixWord, tailWord_3103107, baseEnd_3103107] using wordTrace_append hprefix tailTrace_3103107
  have hstable : (prefixWord ++ tailWord_3103107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103107).length < 2 ^ (prefixWord ++ tailWord_3103107).sum := by decide
  have hdescent : baseEnd_3103107 < baseStart_3103107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103130 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2]
def baseStart_3103130 : Nat := 118140960795 + 3103130 * 2 ^ 59
def prefixEnd_3103130 : Nat := 4983230072969 + 3 ^ 40 * 3103130 * 2
def baseEnd_3103130 : Nat := 1593397223386549223303971

theorem tailTrace_3103130 : CollatzResearch.WordTrace tailWord_3103130 prefixEnd_3103130 1593397223386549223303971 := by
  unfold tailWord_3103130
  simp only [CollatzResearch.WordTrace]
  refine ⟨28295112311974364313962711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75453632831931638170567229 28295112311974364313962711)
  ·
    refine ⟨42442668467961546470944067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28295112311974364313962711 42442668467961546470944067)
    ·
      refine ⟨63664002701942319706416101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42442668467961546470944067 63664002701942319706416101)
      ·
        refine ⟨11937000506614184944953019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63664002701942319706416101 11937000506614184944953019)
        ·
          refine ⟨17905500759921277417429529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11937000506614184944953019 17905500759921277417429529)
          ·
            refine ⟨13429125569940958063072147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17905500759921277417429529 13429125569940958063072147)
            ·
              refine ⟨20143688354911437094608221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13429125569940958063072147 20143688354911437094608221)
              ·
                refine ⟨7553883133091788910478083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20143688354911437094608221 7553883133091788910478083)
                ·
                  refine ⟨11330824699637683365717125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7553883133091788910478083 11330824699637683365717125)
                  ·
                    refine ⟨2124529631182065631071961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11330824699637683365717125 2124529631182065631071961)
                    ·
                      refine ⟨1593397223386549223303971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124529631182065631071961 1593397223386549223303971)
                      ·
                        rfl

theorem cell23_3103130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_3103130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103130 prefixEnd_3103130 := by exact prefixLift 3103130
  have htrace : WordTrace (prefixWord ++ tailWord_3103130) baseStart_3103130 baseEnd_3103130 := by
    simpa [prefixWord, tailWord_3103130, baseEnd_3103130] using wordTrace_append hprefix tailTrace_3103130
  have hstable : (prefixWord ++ tailWord_3103130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103130).length < 2 ^ (prefixWord ++ tailWord_3103130).sum := by decide
  have hdescent : baseEnd_3103130 < baseStart_3103130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103136 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 9]
def baseStart_3103136 : Nat := 118140960795 + 3103136 * 2 ^ 59
def prefixEnd_3103136 : Nat := 4983230072969 + 3 ^ 40 * 3103136 * 2
def baseEnd_3103136 : Nat := 177044478252275133314327

theorem tailTrace_3103136 : CollatzResearch.WordTrace tailWord_3103136 prefixEnd_3103136 177044478252275133314327 := by
  unfold tailWord_3103136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56590334042937860140284631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75453778723917146853712841 56590334042937860140284631)
  ·
    refine ⟨84885501064406790210426947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56590334042937860140284631 84885501064406790210426947)
    ·
      refine ⟨127328251596610185315640421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84885501064406790210426947 127328251596610185315640421)
      ·
        refine ⟨23874047174364409746682579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127328251596610185315640421 23874047174364409746682579)
        ·
          refine ⟨35811070761546614620023869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23874047174364409746682579 35811070761546614620023869)
          ·
            refine ⟨13429151535579980482508951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35811070761546614620023869 13429151535579980482508951)
            ·
              refine ⟨20143727303369970723763427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13429151535579980482508951 20143727303369970723763427)
              ·
                refine ⟨30215590955054956085645141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20143727303369970723763427 30215590955054956085645141)
                ·
                  refine ⟨177044478252275133314327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30215590955054956085645141 177044478252275133314327)
                  ·
                    rfl

theorem cell23_3103136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 9].length) (baseStart_3103136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103136 prefixEnd_3103136 := by exact prefixLift 3103136
  have htrace : WordTrace (prefixWord ++ tailWord_3103136) baseStart_3103136 baseEnd_3103136 := by
    simpa [prefixWord, tailWord_3103136, baseEnd_3103136] using wordTrace_append hprefix tailTrace_3103136
  have hstable : (prefixWord ++ tailWord_3103136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103136).length < 2 ^ (prefixWord ++ tailWord_3103136).sum := by decide
  have hdescent : baseEnd_3103136 < baseStart_3103136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103164 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_3103164 : Nat := 118140960795 + 3103164 * 2 ^ 59
def prefixEnd_3103164 : Nat := 4983230072969 + 3 ^ 40 * 3103164 * 2
def baseEnd_3103164 : Nat := 1593414681728802090278815

theorem tailTrace_3103164 : CollatzResearch.WordTrace tailWord_3103164 prefixEnd_3103164 1593414681728802090278815 := by
  unfold tailWord_3103164
  simp only [CollatzResearch.WordTrace]
  refine ⟨56590844664887140531294273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75454459553182854041725697 56590844664887140531294273)
  ·
    refine ⟨42443133498665355398470705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56590844664887140531294273 42443133498665355398470705)
    ·
      refine ⟨31832350123999016548853029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42443133498665355398470705 31832350123999016548853029)
      ·
        refine ⟨5968565648249815602909943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31832350123999016548853029 5968565648249815602909943)
        ·
          refine ⟨8952848472374723404364915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5968565648249815602909943 8952848472374723404364915)
          ·
            refine ⟨13429272708562085106547373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8952848472374723404364915 13429272708562085106547373)
            ·
              refine ⟨5035977265710781914955265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13429272708562085106547373 5035977265710781914955265)
              ·
                refine ⟨3776982949283086436216449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5035977265710781914955265 3776982949283086436216449)
                ·
                  refine ⟨2832737211962314827162337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776982949283086436216449 2832737211962314827162337)
                  ·
                    refine ⟨2124552908971736120371753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2832737211962314827162337 2124552908971736120371753)
                    ·
                      refine ⟨1593414681728802090278815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124552908971736120371753 1593414681728802090278815)
                      ·
                        rfl

theorem cell23_3103164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_3103164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103164 prefixEnd_3103164 := by exact prefixLift 3103164
  have htrace : WordTrace (prefixWord ++ tailWord_3103164) baseStart_3103164 baseEnd_3103164 := by
    simpa [prefixWord, tailWord_3103164, baseEnd_3103164] using wordTrace_append hprefix tailTrace_3103164
  have hstable : (prefixWord ++ tailWord_3103164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103164).length < 2 ^ (prefixWord ++ tailWord_3103164).sum := by decide
  have hdescent : baseEnd_3103164 < baseStart_3103164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103310 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_3103310 : Nat := 118140960795 + 3103310 * 2 ^ 59
def prefixEnd_3103310 : Nat := 4983230072969 + 3 ^ 40 * 3103310 * 2
def baseEnd_3103310 : Nat := 1593489649904358519053143

theorem tailTrace_3103310 : CollatzResearch.WordTrace tailWord_3103310 prefixEnd_3103310 1593489649904358519053143 := by
  unfold tailWord_3103310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14148376798405668499675423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75458009591496898664935589 14148376798405668499675423)
  ·
    refine ⟨21222565197608502749513135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14148376798405668499675423 21222565197608502749513135)
    ·
      refine ⟨31833847796412754124269703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21222565197608502749513135 31833847796412754124269703)
      ·
        refine ⟨47750771694619131186404555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31833847796412754124269703 47750771694619131186404555)
        ·
          refine ⟨71626157541928696779606833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47750771694619131186404555 71626157541928696779606833)
          ·
            refine ⟨53719618156446522584705125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71626157541928696779606833 53719618156446522584705125)
            ·
              refine ⟨10072428404333722984632211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53719618156446522584705125 10072428404333722984632211)
              ·
                refine ⟨15108642606500584476948317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10072428404333722984632211 15108642606500584476948317)
                ·
                  refine ⟨5665740977437719178855619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15108642606500584476948317 5665740977437719178855619)
                  ·
                    refine ⟨8498611466156578768283429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5665740977437719178855619 8498611466156578768283429)
                    ·
                      refine ⟨1593489649904358519053143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8498611466156578768283429 1593489649904358519053143)
                      ·
                        rfl

theorem cell23_3103310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_3103310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103310 prefixEnd_3103310 := by exact prefixLift 3103310
  have htrace : WordTrace (prefixWord ++ tailWord_3103310) baseStart_3103310 baseEnd_3103310 := by
    simpa [prefixWord, tailWord_3103310, baseEnd_3103310] using wordTrace_append hprefix tailTrace_3103310
  have hstable : (prefixWord ++ tailWord_3103310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103310).length < 2 ^ (prefixWord ++ tailWord_3103310).sum := by decide
  have hdescent : baseEnd_3103310 < baseStart_3103310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103363 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 2, 7]
def baseStart_3103363 : Nat := 118140960795 + 3103363 * 2 ^ 59
def prefixEnd_3103363 : Nat := 4983230072969 + 3 ^ 40 * 3103363 * 2
def baseEnd_3103363 : Nat := 531172288126348937230133

theorem tailTrace_3103363 : CollatzResearch.WordTrace tailWord_3103363 prefixEnd_3103363 531172288126348937230133 := by
  unfold tailWord_3103363
  simp only [CollatzResearch.WordTrace]
  refine ⟨113188947456053338049082743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75459298304035558699388495 113188947456053338049082743)
  ·
    refine ⟨169783421184080007073624115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113188947456053338049082743 169783421184080007073624115)
    ·
      refine ⟨254675131776120010610436173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169783421184080007073624115 254675131776120010610436173)
      ·
        refine ⟨95503174416045003978913565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254675131776120010610436173 95503174416045003978913565)
        ·
          refine ⟨35813690406016876492092587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95503174416045003978913565 35813690406016876492092587)
          ·
            refine ⟨53720535609025314738138881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35813690406016876492092587 53720535609025314738138881)
            ·
              refine ⟨40290401706768986053604161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53720535609025314738138881 40290401706768986053604161)
              ·
                refine ⟨30217801280076739540203121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40290401706768986053604161 30217801280076739540203121)
                ·
                  refine ⟨22663350960057554655152341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30217801280076739540203121 22663350960057554655152341)
                  ·
                    refine ⟨531172288126348937230133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22663350960057554655152341 531172288126348937230133)
                    ·
                      rfl

theorem cell23_3103363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 7].length) (baseStart_3103363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103363 prefixEnd_3103363 := by exact prefixLift 3103363
  have htrace : WordTrace (prefixWord ++ tailWord_3103363) baseStart_3103363 baseEnd_3103363 := by
    simpa [prefixWord, tailWord_3103363, baseEnd_3103363] using wordTrace_append hprefix tailTrace_3103363
  have hstable : (prefixWord ++ tailWord_3103363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103363).length < 2 ^ (prefixWord ++ tailWord_3103363).sum := by decide
  have hdescent : baseEnd_3103363 < baseStart_3103363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103364 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_3103364 : Nat := 118140960795 + 3103364 * 2 ^ 59
def prefixEnd_3103364 : Nat := 4983230072969 + 3 ^ 40 * 3103364 * 2
def baseEnd_3103364 : Nat := 1593517377859701307777895

theorem tailTrace_3103364 : CollatzResearch.WordTrace tailWord_3103364 prefixEnd_3103364 1593517377859701307777895 := by
  unfold tailWord_3103364
  simp only [CollatzResearch.WordTrace]
  refine ⟨56594491964524857609934573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75459322619366476813246097 56594491964524857609934573)
  ·
    refine ⟨21222934486696821603725465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56594491964524857609934573 21222934486696821603725465)
    ·
      refine ⟨15917200865022616202794099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21222934486696821603725465 15917200865022616202794099)
      ·
        refine ⟨23875801297533924304191149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15917200865022616202794099 23875801297533924304191149)
        ·
          refine ⟨8953425486575221614071681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23875801297533924304191149 8953425486575221614071681)
          ·
            refine ⟨6715069114931416210553761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8953425486575221614071681 6715069114931416210553761)
            ·
              refine ⟨5036301836198562157915321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6715069114931416210553761 5036301836198562157915321)
              ·
                refine ⟨3777226377148921618436491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5036301836198562157915321 3777226377148921618436491)
                ·
                  refine ⟨5665839565723382427654737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777226377148921618436491 5665839565723382427654737)
                  ·
                    refine ⟨4249379674292536820741053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5665839565723382427654737 4249379674292536820741053)
                    ·
                      refine ⟨1593517377859701307777895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4249379674292536820741053 1593517377859701307777895)
                      ·
                        rfl

theorem cell23_3103364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_3103364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103364 prefixEnd_3103364 := by exact prefixLift 3103364
  have htrace : WordTrace (prefixWord ++ tailWord_3103364) baseStart_3103364 baseEnd_3103364 := by
    simpa [prefixWord, tailWord_3103364, baseEnd_3103364] using wordTrace_append hprefix tailTrace_3103364
  have hstable : (prefixWord ++ tailWord_3103364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103364).length < 2 ^ (prefixWord ++ tailWord_3103364).sum := by decide
  have hdescent : baseEnd_3103364 < baseStart_3103364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103378 : List Nat := [3, 2, 3, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_3103378 : Nat := 118140960795 + 3103378 * 2 ^ 59
def prefixEnd_3103378 : Nat := 4983230072969 + 3 ^ 40 * 3103378 * 2
def baseEnd_3103378 : Nat := 1593524566588864253002831

theorem tailTrace_3103378 : CollatzResearch.WordTrace tailWord_3103378 prefixEnd_3103378 1593524566588864253002831 := by
  unfold tailWord_3103378
  simp only [CollatzResearch.WordTrace]
  refine ⟨28297373637749748902719697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75459663033999330407252525 28297373637749748902719697)
  ·
    refine ⟨21223030228312311677039773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28297373637749748902719697 21223030228312311677039773)
    ·
      refine ⟨7958636335617116878889915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21223030228312311677039773 7958636335617116878889915)
      ·
        refine ⟨11937954503425675318334873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7958636335617116878889915 11937954503425675318334873)
        ·
          refine ⟨8953465877569256488751155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11937954503425675318334873 8953465877569256488751155)
          ·
            refine ⟨13430198816353884733126733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8953465877569256488751155 13430198816353884733126733)
            ·
              refine ⟨5036324556132706774922525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13430198816353884733126733 5036324556132706774922525)
              ·
                refine ⟨1888621708549765040595947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5036324556132706774922525 1888621708549765040595947)
                ·
                  refine ⟨2832932562824647560893921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888621708549765040595947 2832932562824647560893921)
                  ·
                    refine ⟨2124699422118485670670441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2832932562824647560893921 2124699422118485670670441)
                    ·
                      refine ⟨1593524566588864253002831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124699422118485670670441 1593524566588864253002831)
                      ·
                        rfl

theorem cell23_3103378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_3103378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103378 prefixEnd_3103378 := by exact prefixLift 3103378
  have htrace : WordTrace (prefixWord ++ tailWord_3103378) baseStart_3103378 baseEnd_3103378 := by
    simpa [prefixWord, tailWord_3103378, baseEnd_3103378] using wordTrace_append hprefix tailTrace_3103378
  have hstable : (prefixWord ++ tailWord_3103378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103378).length < 2 ^ (prefixWord ++ tailWord_3103378).sum := by decide
  have hdescent : baseEnd_3103378 < baseStart_3103378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103411 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 2, 1, 3]
def baseStart_3103411 : Nat := 118140960795 + 3103411 * 2 ^ 59
def prefixEnd_3103411 : Nat := 4983230072969 + 3 ^ 40 * 3103411 * 2
def baseEnd_3103411 : Nat := 1593541511450462623890179

theorem tailTrace_3103411 : CollatzResearch.WordTrace tailWord_3103411 prefixEnd_3103411 1593541511450462623890179 := by
  unfold tailWord_3103411
  simp only [CollatzResearch.WordTrace]
  refine ⟨113190698159879442246830087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75460465439919628164553391 113190698159879442246830087)
  ·
    refine ⟨169786047239819163370245131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113190698159879442246830087 169786047239819163370245131)
    ·
      refine ⟨254679070859728745055367697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169786047239819163370245131 254679070859728745055367697)
      ·
        refine ⟨191009303144796558791525773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254679070859728745055367697 191009303144796558791525773)
        ·
          refine ⟨71628488679298709546822165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191009303144796558791525773 71628488679298709546822165)
          ·
            refine ⟨3357585406842127010007289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71628488679298709546822165 3357585406842127010007289)
            ·
              refine ⟨2518189055131595257505467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3357585406842127010007289 2518189055131595257505467)
              ·
                refine ⟨3777283582697392886258201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518189055131595257505467 3777283582697392886258201)
                ·
                  refine ⟨2832962687023044664693651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3777283582697392886258201 2832962687023044664693651)
                  ·
                    refine ⟨4249444030534566997040477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2832962687023044664693651 4249444030534566997040477)
                    ·
                      refine ⟨1593541511450462623890179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4249444030534566997040477 1593541511450462623890179)
                      ·
                        rfl

theorem cell23_3103411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 1, 3].length) (baseStart_3103411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103411 prefixEnd_3103411 := by exact prefixLift 3103411
  have htrace : WordTrace (prefixWord ++ tailWord_3103411) baseStart_3103411 baseEnd_3103411 := by
    simpa [prefixWord, tailWord_3103411, baseEnd_3103411] using wordTrace_append hprefix tailTrace_3103411
  have hstable : (prefixWord ++ tailWord_3103411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103411).length < 2 ^ (prefixWord ++ tailWord_3103411).sum := by decide
  have hdescent : baseEnd_3103411 < baseStart_3103411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103417 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 1, 4, 2]
def baseStart_3103417 : Nat := 118140960795 + 3103417 * 2 ^ 59
def prefixEnd_3103417 : Nat := 4983230072969 + 3 ^ 40 * 3103417 * 2
def baseEnd_3103417 : Nat := 1593544592334389600415151

theorem tailTrace_3103417 : CollatzResearch.WordTrace tailWord_3103417 prefixEnd_3103417 1593544592334389600415151 := by
  unfold tailWord_3103417
  simp only [CollatzResearch.WordTrace]
  refine ⟨113190916997857705271548505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75460611331905136847699003 113190916997857705271548505)
  ·
    refine ⟨84893187748393278953661379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113190916997857705271548505 84893187748393278953661379)
    ·
      refine ⟨127339781622589918430492069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84893187748393278953661379 127339781622589918430492069)
      ·
        refine ⟨23876209054235609705717263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127339781622589918430492069 23876209054235609705717263)
        ·
          refine ⟨35814313581353414558575895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23876209054235609705717263 35814313581353414558575895)
          ·
            refine ⟨53721470372030121837863843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35814313581353414558575895 53721470372030121837863843)
            ·
              refine ⟨80582205558045182756795765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53721470372030121837863843 80582205558045182756795765)
              ·
                refine ⟨7554581771066735883449603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80582205558045182756795765 7554581771066735883449603)
                ·
                  refine ⟨11331872656600103825174405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554581771066735883449603 11331872656600103825174405)
                  ·
                    refine ⟨2124726123112519467220201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11331872656600103825174405 2124726123112519467220201)
                    ·
                      refine ⟨1593544592334389600415151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124726123112519467220201 1593544592334389600415151)
                      ·
                        rfl

theorem cell23_3103417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_3103417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103417 prefixEnd_3103417 := by exact prefixLift 3103417
  have htrace : WordTrace (prefixWord ++ tailWord_3103417) baseStart_3103417 baseEnd_3103417 := by
    simpa [prefixWord, tailWord_3103417, baseEnd_3103417] using wordTrace_append hprefix tailTrace_3103417
  have hstable : (prefixWord ++ tailWord_3103417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103417).length < 2 ^ (prefixWord ++ tailWord_3103417).sum := by decide
  have hdescent : baseEnd_3103417 < baseStart_3103417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103420 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3103420 : Nat := 118140960795 + 3103420 * 2 ^ 59
def prefixEnd_3103420 : Nat := 4983230072969 + 3 ^ 40 * 3103420 * 2
def baseEnd_3103420 : Nat := 1593546132776353088677637

theorem tailTrace_3103420 : CollatzResearch.WordTrace tailWord_3103420 prefixEnd_3103420 1593546132776353088677637 := by
  unfold tailWord_3103420
  simp only [CollatzResearch.WordTrace]
  refine ⟨56595513208423418391953857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75460684277897891189271809 56595513208423418391953857)
  ·
    refine ⟨42446634906317563793965393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56595513208423418391953857 42446634906317563793965393)
    ·
      refine ⟨31834976179738172845474045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42446634906317563793965393 31834976179738172845474045)
      ·
        refine ⟨11938116067401814817052767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31834976179738172845474045 11938116067401814817052767)
        ·
          refine ⟨17907174101102722225579151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11938116067401814817052767 17907174101102722225579151)
          ·
            refine ⟨26860761151654083338368727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17907174101102722225579151 26860761151654083338368727)
            ·
              refine ⟨40291141727481125007553091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26860761151654083338368727 40291141727481125007553091)
              ·
                refine ⟨60436712591221687511329637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40291141727481125007553091 60436712591221687511329637)
                ·
                  refine ⟨11331883610854066408374307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60436712591221687511329637 11331883610854066408374307)
                  ·
                    refine ⟨16997825416281099612561461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11331883610854066408374307 16997825416281099612561461)
                    ·
                      refine ⟨1593546132776353088677637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16997825416281099612561461 1593546132776353088677637)
                      ·
                        rfl

theorem cell23_3103420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3103420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103420 prefixEnd_3103420 := by exact prefixLift 3103420
  have htrace : WordTrace (prefixWord ++ tailWord_3103420) baseStart_3103420 baseEnd_3103420 := by
    simpa [prefixWord, tailWord_3103420, baseEnd_3103420] using wordTrace_append hprefix tailTrace_3103420
  have hstable : (prefixWord ++ tailWord_3103420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103420).length < 2 ^ (prefixWord ++ tailWord_3103420).sum := by decide
  have hdescent : baseEnd_3103420 < baseStart_3103420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103421 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_3103421 : Nat := 118140960795 + 3103421 * 2 ^ 59
def prefixEnd_3103421 : Nat := 4983230072969 + 3 ^ 40 * 3103421 * 2
def baseEnd_3103421 : Nat := 1593546646257007584765133

theorem tailTrace_3103421 : CollatzResearch.WordTrace tailWord_3103421 prefixEnd_3103421 1593546646257007584765133 := by
  unfold tailWord_3103421
  simp only [CollatzResearch.WordTrace]
  refine ⟨113191062889843213954694117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75460708593228809303129411 113191062889843213954694117)
  ·
    refine ⟨21223324291845602616505147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113191062889843213954694117 21223324291845602616505147)
    ·
      refine ⟨31834986437768403924757721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21223324291845602616505147 31834986437768403924757721)
      ·
        refine ⟨23876239828326302943568291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31834986437768403924757721 23876239828326302943568291)
        ·
          refine ⟨35814359742489454415352437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23876239828326302943568291 35814359742489454415352437)
          ·
            refine ⟨3357596225858386351439291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35814359742489454415352437 3357596225858386351439291)
            ·
              refine ⟨5036394338787579527158937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357596225858386351439291 5036394338787579527158937)
              ·
                refine ⟨3777295754090684645369203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5036394338787579527158937 3777295754090684645369203)
                ·
                  refine ⟨5665943631136026968053805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777295754090684645369203 5665943631136026968053805)
                  ·
                    refine ⟨2124728861676010113020177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5665943631136026968053805 2124728861676010113020177)
                    ·
                      refine ⟨1593546646257007584765133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124728861676010113020177 1593546646257007584765133)
                      ·
                        rfl

theorem cell23_3103421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_3103421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103421 prefixEnd_3103421 := by exact prefixLift 3103421
  have htrace : WordTrace (prefixWord ++ tailWord_3103421) baseStart_3103421 baseEnd_3103421 := by
    simpa [prefixWord, tailWord_3103421, baseEnd_3103421] using wordTrace_append hprefix tailTrace_3103421
  have hstable : (prefixWord ++ tailWord_3103421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103421).length < 2 ^ (prefixWord ++ tailWord_3103421).sum := by decide
  have hdescent : baseEnd_3103421 < baseStart_3103421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103434 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_3103434 : Nat := 118140960795 + 3103434 * 2 ^ 59
def prefixEnd_3103434 : Nat := 4983230072969 + 3 ^ 40 * 3103434 * 2
def baseEnd_3103434 : Nat := 1593553321505516033902573

theorem tailTrace_3103434 : CollatzResearch.WordTrace tailWord_3103434 prefixEnd_3103434 1593553321505516033902573 := by
  unfold tailWord_3103434
  simp only [CollatzResearch.WordTrace]
  refine ⟨28297884259699029293729339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75461024692530744783278237 28297884259699029293729339)
  ·
    refine ⟨42446826389548543940594009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28297884259699029293729339 42446826389548543940594009)
    ·
      refine ⟨31835119792161407955445507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42446826389548543940594009 31835119792161407955445507)
      ·
        refine ⟨47752679688242111933168261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31835119792161407955445507 47752679688242111933168261)
        ·
          refine ⟨8953627441545395987469049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47752679688242111933168261 8953627441545395987469049)
          ·
            refine ⟨6715220581159046990601787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8953627441545395987469049 6715220581159046990601787)
            ·
              refine ⟨10072830871738570485902681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6715220581159046990601787 10072830871738570485902681)
              ·
                refine ⟨7554623153803927864427011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10072830871738570485902681 7554623153803927864427011)
                ·
                  refine ⟨11331934730705891796640517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554623153803927864427011 11331934730705891796640517)
                  ·
                    refine ⟨2124737762007354711870097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11331934730705891796640517 2124737762007354711870097)
                    ·
                      refine ⟨1593553321505516033902573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124737762007354711870097 1593553321505516033902573)
                      ·
                        rfl

theorem cell23_3103434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_3103434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103434 prefixEnd_3103434 := by exact prefixLift 3103434
  have htrace : WordTrace (prefixWord ++ tailWord_3103434) baseStart_3103434 baseEnd_3103434 := by
    simpa [prefixWord, tailWord_3103434, baseEnd_3103434] using wordTrace_append hprefix tailTrace_3103434
  have hstable : (prefixWord ++ tailWord_3103434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103434).length < 2 ^ (prefixWord ++ tailWord_3103434).sum := by decide
  have hdescent : baseEnd_3103434 < baseStart_3103434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103507 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 4, 4, 2]
def baseStart_3103507 : Nat := 118140960795 + 3103507 * 2 ^ 59
def prefixEnd_3103507 : Nat := 4983230072969 + 3 ^ 40 * 3103507 * 2
def baseEnd_3103507 : Nat := 1593590805593294248289737

theorem tailTrace_3103507 : CollatzResearch.WordTrace tailWord_3103507 prefixEnd_3103507 1593590805593294248289737 := by
  unfold tailWord_3103507
  simp only [CollatzResearch.WordTrace]
  refine ⟨113194199567531650642324775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75462799711687767094883183 113194199567531650642324775)
  ·
    refine ⟨169791299351297475963487163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113194199567531650642324775 169791299351297475963487163)
    ·
      refine ⟨254686949026946213945230745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169791299351297475963487163 254686949026946213945230745)
      ·
        refine ⟨191015211770209660458923059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254686949026946213945230745 191015211770209660458923059)
        ·
          refine ⟨286522817655314490688384589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191015211770209660458923059 286522817655314490688384589)
          ·
            refine ⟨107446056620742934008144221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286522817655314490688384589 107446056620742934008144221)
            ·
              refine ⟨40292271232778600253054083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107446056620742934008144221 40292271232778600253054083)
              ·
                refine ⟨60438406849167900379581125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40292271232778600253054083 60438406849167900379581125)
                ·
                  refine ⟨11332201284218981321171461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60438406849167900379581125 11332201284218981321171461)
                  ·
                    refine ⟨2124787740791058997719649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11332201284218981321171461 2124787740791058997719649)
                    ·
                      refine ⟨1593590805593294248289737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124787740791058997719649 1593590805593294248289737)
                      ·
                        rfl

theorem cell23_3103507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 4, 2].length) (baseStart_3103507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103507 prefixEnd_3103507 := by exact prefixLift 3103507
  have htrace : WordTrace (prefixWord ++ tailWord_3103507) baseStart_3103507 baseEnd_3103507 := by
    simpa [prefixWord, tailWord_3103507, baseEnd_3103507] using wordTrace_append hprefix tailTrace_3103507
  have hstable : (prefixWord ++ tailWord_3103507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103507).length < 2 ^ (prefixWord ++ tailWord_3103507).sum := by decide
  have hdescent : baseEnd_3103507 < baseStart_3103507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103551 : List Nat := [1, 1, 2, 2, 5, 1, 3, 3, 1, 4]
def baseStart_3103551 : Nat := 118140960795 + 3103551 * 2 ^ 59
def prefixEnd_3103551 : Nat := 4983230072969 + 3 ^ 40 * 3103551 * 2
def baseEnd_3103551 : Nat := 531204466247364025379845

theorem tailTrace_3103551 : CollatzResearch.WordTrace tailWord_3103551 prefixEnd_3103551 531204466247364025379845 := by
  unfold tailWord_3103551
  simp only [CollatzResearch.WordTrace]
  refine ⟨113195804379372246156926507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75463869586248164104617671 113195804379372246156926507)
  ·
    refine ⟨169793706569058369235389761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113195804379372246156926507 169793706569058369235389761)
    ·
      refine ⟨127345279926793776926542321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169793706569058369235389761 127345279926793776926542321)
      ·
        refine ⟨95508959945095332694906741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127345279926793776926542321 95508959945095332694906741)
        ·
          refine ⟨8953964994852687440147507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95508959945095332694906741 8953964994852687440147507)
          ·
            refine ⟨13430947492279031160221261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8953964994852687440147507 13430947492279031160221261)
            ·
              refine ⟨5036605309604636685082973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13430947492279031160221261 5036605309604636685082973)
              ·
                refine ⟨1888726991101738756906115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5036605309604636685082973 1888726991101738756906115)
                ·
                  refine ⟨2833090486652608135359173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888726991101738756906115 2833090486652608135359173)
                  ·
                    refine ⟨531204466247364025379845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833090486652608135359173 531204466247364025379845)
                    ·
                      rfl

theorem cell23_3103551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 4].length) (baseStart_3103551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103551 prefixEnd_3103551 := by exact prefixLift 3103551
  have htrace : WordTrace (prefixWord ++ tailWord_3103551) baseStart_3103551 baseEnd_3103551 := by
    simpa [prefixWord, tailWord_3103551, baseEnd_3103551] using wordTrace_append hprefix tailTrace_3103551
  have hstable : (prefixWord ++ tailWord_3103551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103551).length < 2 ^ (prefixWord ++ tailWord_3103551).sum := by decide
  have hdescent : baseEnd_3103551 < baseStart_3103551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103558 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3103558 : Nat := 118140960795 + 3103558 * 2 ^ 59
def prefixEnd_3103558 : Nat := 4983230072969 + 3 ^ 40 * 3103558 * 2
def baseEnd_3103558 : Nat := 1593616993106673548752003

theorem tailTrace_3103558 : CollatzResearch.WordTrace tailWord_3103558 prefixEnd_3103558 1593616993106673548752003 := by
  unfold tailWord_3103558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537376865323340198513479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75464039793564590901620885 3537376865323340198513479)
  ·
    refine ⟨5306065297985010297770219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3537376865323340198513479 5306065297985010297770219)
    ·
      refine ⟨7959097946977515446655329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5306065297985010297770219 7959097946977515446655329)
      ·
        refine ⟨5969323460233136584991497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7959097946977515446655329 5969323460233136584991497)
        ·
          refine ⟨4476992595174852438743623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5969323460233136584991497 4476992595174852438743623)
          ·
            refine ⟨6715488892762278658115435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476992595174852438743623 6715488892762278658115435)
            ·
              refine ⟨10073233339143417987173153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6715488892762278658115435 10073233339143417987173153)
              ·
                refine ⟨7554925004357563490379865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10073233339143417987173153 7554925004357563490379865)
                ·
                  refine ⟨5666193753268172617784899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7554925004357563490379865 5666193753268172617784899)
                  ·
                    refine ⟨8499290629902258926677349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5666193753268172617784899 8499290629902258926677349)
                    ·
                      refine ⟨1593616993106673548752003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8499290629902258926677349 1593616993106673548752003)
                      ·
                        rfl

theorem cell23_3103558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3103558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103558 prefixEnd_3103558 := by exact prefixLift 3103558
  have htrace : WordTrace (prefixWord ++ tailWord_3103558) baseStart_3103558 baseEnd_3103558 := by
    simpa [prefixWord, tailWord_3103558, baseEnd_3103558] using wordTrace_append hprefix tailTrace_3103558
  have hstable : (prefixWord ++ tailWord_3103558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103558).length < 2 ^ (prefixWord ++ tailWord_3103558).sum := by decide
  have hdescent : baseEnd_3103558 < baseStart_3103558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103567 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 9, 2]
def baseStart_3103567 : Nat := 118140960795 + 3103567 * 2 ^ 59
def prefixEnd_3103567 : Nat := 4983230072969 + 3 ^ 40 * 3103567 * 2
def baseEnd_3103567 : Nat := 1593621614432564013539461

theorem tailTrace_3103567 : CollatzResearch.WordTrace tailWord_3103567 prefixEnd_3103567 1593621614432564013539461 := by
  unfold tailWord_3103567
  simp only [CollatzResearch.WordTrace]
  refine ⟨113196387947314280889508955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75464258631542853926339303 113196387947314280889508955)
  ·
    refine ⟨169794581920971421334263433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113196387947314280889508955 169794581920971421334263433)
    ·
      refine ⟨127345936440728566000697575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169794581920971421334263433 127345936440728566000697575)
      ·
        refine ⟨191018904661092849001046363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127345936440728566000697575 191018904661092849001046363)
        ·
          refine ⟨286528356991639273501569545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191018904661092849001046363 286528356991639273501569545)
          ·
            refine ⟨214896267743729455126177159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286528356991639273501569545 214896267743729455126177159)
            ·
              refine ⟨322344401615594182689265739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214896267743729455126177159 322344401615594182689265739)
              ·
                refine ⟨483516602423391274033898609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322344401615594182689265739 483516602423391274033898609)
                ·
                  refine ⟨362637451817543455525423957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483516602423391274033898609 362637451817543455525423957)
                  ·
                    refine ⟨2124828819243418684719281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 362637451817543455525423957 2124828819243418684719281)
                    ·
                      refine ⟨1593621614432564013539461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124828819243418684719281 1593621614432564013539461)
                      ·
                        rfl

theorem cell23_3103567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 9, 2].length) (baseStart_3103567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103567 prefixEnd_3103567 := by exact prefixLift 3103567
  have htrace : WordTrace (prefixWord ++ tailWord_3103567) baseStart_3103567 baseEnd_3103567 := by
    simpa [prefixWord, tailWord_3103567, baseEnd_3103567] using wordTrace_append hprefix tailTrace_3103567
  have hstable : (prefixWord ++ tailWord_3103567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103567).length < 2 ^ (prefixWord ++ tailWord_3103567).sum := by decide
  have hdescent : baseEnd_3103567 < baseStart_3103567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103584 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 4, 3, 2]
def baseStart_3103584 : Nat := 118140960795 + 3103584 * 2 ^ 59
def prefixEnd_3103584 : Nat := 4983230072969 + 3 ^ 40 * 3103584 * 2
def baseEnd_3103584 : Nat := 1593630343603690447026883

theorem tailTrace_3103584 : CollatzResearch.WordTrace tailWord_3103584 prefixEnd_3103584 1593630343603690447026883 := by
  unfold tailWord_3103584
  simp only [CollatzResearch.WordTrace]
  refine ⟨56598503994126346396438903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75464671992168461861918537 56598503994126346396438903)
  ·
    refine ⟨84897755991189519594658355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56598503994126346396438903 84897755991189519594658355)
    ·
      refine ⟨127346633986784279391987533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84897755991189519594658355 127346633986784279391987533)
      ·
        refine ⟨47754987745044104771995325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127346633986784279391987533 47754987745044104771995325)
        ·
          refine ⟨17908120404391539289498247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47754987745044104771995325 17908120404391539289498247)
          ·
            refine ⟨26862180606587308934247371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17908120404391539289498247 26862180606587308934247371)
            ·
              refine ⟨40293270909880963401371057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26862180606587308934247371 40293270909880963401371057)
              ·
                refine ⟨30219953182410722551028293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40293270909880963401371057 30219953182410722551028293)
                ·
                  refine ⟨5666241221702010478317805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30219953182410722551028293 5666241221702010478317805)
                  ·
                    refine ⟨2124840458138253929369177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5666241221702010478317805 2124840458138253929369177)
                    ·
                      refine ⟨1593630343603690447026883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124840458138253929369177 1593630343603690447026883)
                      ·
                        rfl

theorem cell23_3103584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_3103584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103584 prefixEnd_3103584 := by exact prefixLift 3103584
  have htrace : WordTrace (prefixWord ++ tailWord_3103584) baseStart_3103584 baseEnd_3103584 := by
    simpa [prefixWord, tailWord_3103584, baseEnd_3103584] using wordTrace_append hprefix tailTrace_3103584
  have hstable : (prefixWord ++ tailWord_3103584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103584).length < 2 ^ (prefixWord ++ tailWord_3103584).sum := by decide
  have hdescent : baseEnd_3103584 < baseStart_3103584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103601 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 2, 3, 2]
def baseStart_3103601 : Nat := 118140960795 + 3103601 * 2 ^ 59
def prefixEnd_3103601 : Nat := 4983230072969 + 3 ^ 40 * 3103601 * 2
def baseEnd_3103601 : Nat := 1593639072774816880514305

theorem tailTrace_3103601 : CollatzResearch.WordTrace tailWord_3103601 prefixEnd_3103601 1593639072774816880514305 := by
  unfold tailWord_3103601
  simp only [CollatzResearch.WordTrace]
  refine ⟨113197628029191104696246657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75465085352794069797497771 113197628029191104696246657)
  ·
    refine ⟨84898221021893328522184993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113197628029191104696246657 84898221021893328522184993)
    ·
      refine ⟨63673665766419996391638745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84898221021893328522184993 63673665766419996391638745)
      ·
        refine ⟨47755249324814997293729059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63673665766419996391638745 47755249324814997293729059)
        ·
          refine ⟨71632873987222495940593589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47755249324814997293729059 71632873987222495940593589)
          ·
            refine ⟨6715581936302108994430649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71632873987222495940593589 6715581936302108994430649)
            ·
              refine ⟨5036686452226581745822987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6715581936302108994430649 5036686452226581745822987)
              ·
                refine ⟨7555029678339872618734481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036686452226581745822987 7555029678339872618734481)
                ·
                  refine ⟨5666272258754904464050861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7555029678339872618734481 5666272258754904464050861)
                  ·
                    refine ⟨2124852097033089174019073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5666272258754904464050861 2124852097033089174019073)
                    ·
                      refine ⟨1593639072774816880514305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124852097033089174019073 1593639072774816880514305)
                      ·
                        rfl

theorem cell23_3103601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_3103601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103601 prefixEnd_3103601 := by exact prefixLift 3103601
  have htrace : WordTrace (prefixWord ++ tailWord_3103601) baseStart_3103601 baseEnd_3103601 := by
    simpa [prefixWord, tailWord_3103601, baseEnd_3103601] using wordTrace_append hprefix tailTrace_3103601
  have hstable : (prefixWord ++ tailWord_3103601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103601).length < 2 ^ (prefixWord ++ tailWord_3103601).sum := by decide
  have hdescent : baseEnd_3103601 < baseStart_3103601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103607 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 6, 4]
def baseStart_3103607 : Nat := 118140960795 + 3103607 * 2 ^ 59
def prefixEnd_3103607 : Nat := 4983230072969 + 3 ^ 40 * 3103607 * 2
def baseEnd_3103607 : Nat := 531214051219581285679759

theorem tailTrace_3103607 : CollatzResearch.WordTrace tailWord_3103607 prefixEnd_3103607 531214051219581285679759 := by
  unfold tailWord_3103607
  simp only [CollatzResearch.WordTrace]
  refine ⟨113197846867169367720965075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75465231244779578480643383 113197846867169367720965075)
  ·
    refine ⟨169796770300754051581447613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113197846867169367720965075 169796770300754051581447613)
    ·
      refine ⟨63673788862782769343042855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169796770300754051581447613 63673788862782769343042855)
      ·
        refine ⟨95510683294174154014564283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63673788862782769343042855 95510683294174154014564283)
        ·
          refine ⟨143266024941261231021846425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95510683294174154014564283 143266024941261231021846425)
          ·
            refine ⟨107449518705945923266384819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143266024941261231021846425 107449518705945923266384819)
            ·
              refine ⟨161174278058918884899577229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107449518705945923266384819 161174278058918884899577229)
              ·
                refine ⟨60440354272094581837341461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161174278058918884899577229 60440354272094581837341461)
                ·
                  refine ⟨2833141606504433523625381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60440354272094581837341461 2833141606504433523625381)
                  ·
                    refine ⟨531214051219581285679759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833141606504433523625381 531214051219581285679759)
                    ·
                      rfl

theorem cell23_3103607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_3103607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103607 prefixEnd_3103607 := by exact prefixLift 3103607
  have htrace : WordTrace (prefixWord ++ tailWord_3103607) baseStart_3103607 baseEnd_3103607 := by
    simpa [prefixWord, tailWord_3103607, baseEnd_3103607] using wordTrace_append hprefix tailTrace_3103607
  have hstable : (prefixWord ++ tailWord_3103607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103607).length < 2 ^ (prefixWord ++ tailWord_3103607).sum := by decide
  have hdescent : baseEnd_3103607 < baseStart_3103607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103625 : List Nat := [1, 2, 1, 1, 5, 4, 2, 2, 1, 1, 3]
def baseStart_3103625 : Nat := 118140960795 + 3103625 * 2 ^ 59
def prefixEnd_3103625 : Nat := 4983230072969 + 3 ^ 40 * 3103625 * 2
def baseEnd_3103625 : Nat := 1593651396310524786614195

theorem tailTrace_3103625 : CollatzResearch.WordTrace tailWord_3103625 prefixEnd_3103625 1593651396310524786614195 := by
  unfold tailWord_3103625
  simp only [CollatzResearch.WordTrace]
  refine ⟨113198503381104156795120329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75465668920736104530080219 113198503381104156795120329)
  ·
    refine ⟨84898877535828117596340247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113198503381104156795120329 84898877535828117596340247)
    ·
      refine ⟨127348316303742176394510371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84898877535828117596340247 127348316303742176394510371)
      ·
        refine ⟨191022474455613264591765557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127348316303742176394510371 191022474455613264591765557)
        ·
          refine ⟨17908356980213743555478021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191022474455613264591765557 17908356980213743555478021)
          ·
            refine ⟨3357816933790076916652129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17908356980213743555478021 3357816933790076916652129)
            ·
              refine ⟨2518362700342557687489097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3357816933790076916652129 2518362700342557687489097)
              ·
                refine ⟨1888772025256918265616823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518362700342557687489097 1888772025256918265616823)
                ·
                  refine ⟨2833158037885377398425235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888772025256918265616823 2833158037885377398425235)
                  ·
                    refine ⟨4249737056828066097637853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2833158037885377398425235 4249737056828066097637853)
                    ·
                      refine ⟨1593651396310524786614195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4249737056828066097637853 1593651396310524786614195)
                      ·
                        rfl

theorem cell23_3103625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 1, 3].length) (baseStart_3103625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103625 prefixEnd_3103625 := by exact prefixLift 3103625
  have htrace : WordTrace (prefixWord ++ tailWord_3103625) baseStart_3103625 baseEnd_3103625 := by
    simpa [prefixWord, tailWord_3103625, baseEnd_3103625] using wordTrace_append hprefix tailTrace_3103625
  have hstable : (prefixWord ++ tailWord_3103625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103625).length < 2 ^ (prefixWord ++ tailWord_3103625).sum := by decide
  have hdescent : baseEnd_3103625 < baseStart_3103625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103637 : List Nat := [1, 3, 2, 1, 1, 4, 3, 8]
def baseStart_3103637 : Nat := 118140960795 + 3103637 * 2 ^ 59
def prefixEnd_3103637 : Nat := 4983230072969 + 3 ^ 40 * 3103637 * 2
def baseEnd_3103637 : Nat := 59024354002902916283857

theorem tailTrace_3103637 : CollatzResearch.WordTrace tailWord_3103637 prefixEnd_3103637 59024354002902916283857 := by
  unfold tailWord_3103637
  simp only [CollatzResearch.WordTrace]
  refine ⟨113198941057060682844557165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75465960704707121896371443 113198941057060682844557165)
  ·
    refine ⟨42449602896397756066708937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113198941057060682844557165 42449602896397756066708937)
    ·
      refine ⟨31837202172298317050031703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42449602896397756066708937 31837202172298317050031703)
      ·
        refine ⟨47755803258447475575047555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31837202172298317050031703 47755803258447475575047555)
        ·
          refine ⟨71633704887671213362571333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47755803258447475575047555 71633704887671213362571333)
          ·
            refine ⟨13431319666438352505482125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71633704887671213362571333 13431319666438352505482125)
            ·
              refine ⟨5036744874914382189555797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13431319666438352505482125 5036744874914382189555797)
              ·
                refine ⟨59024354002902916283857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5036744874914382189555797 59024354002902916283857)
                ·
                  rfl

theorem cell23_3103637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 8].length) (baseStart_3103637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103637 prefixEnd_3103637 := by exact prefixLift 3103637
  have htrace : WordTrace (prefixWord ++ tailWord_3103637) baseStart_3103637 baseEnd_3103637 := by
    simpa [prefixWord, tailWord_3103637, baseEnd_3103637] using wordTrace_append hprefix tailTrace_3103637
  have hstable : (prefixWord ++ tailWord_3103637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103637).length < 2 ^ (prefixWord ++ tailWord_3103637).sum := by decide
  have hdescent : baseEnd_3103637 < baseStart_3103637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103665 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 1, 1, 4]
def baseStart_3103665 : Nat := 118140960795 + 3103665 * 2 ^ 59
def prefixEnd_3103665 : Nat := 4983230072969 + 3 ^ 40 * 3103665 * 2
def baseEnd_3103665 : Nat := 1593671935536704630114011

theorem tailTrace_3103665 : CollatzResearch.WordTrace tailWord_3103665 prefixEnd_3103665 1593671935536704630114011 := by
  unfold tailWord_3103665
  simp only [CollatzResearch.WordTrace]
  refine ⟨113199962300959243626576449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75466641533972829084384299 113199962300959243626576449)
  ·
    refine ⟨84899971725719432719932337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113199962300959243626576449 84899971725719432719932337)
    ·
      refine ⟨63674978794289574539949253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84899971725719432719932337 63674978794289574539949253)
      ·
        refine ⟨11939058523929295226240485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63674978794289574539949253 11939058523929295226240485)
        ·
          refine ⟨2238573473236742854920091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11939058523929295226240485 2238573473236742854920091)
          ·
            refine ⟨3357860209855114282380137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238573473236742854920091 3357860209855114282380137)
            ·
              refine ⟨2518395157391335711785103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3357860209855114282380137 2518395157391335711785103)
              ·
                refine ⟨3777592736087003567677655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518395157391335711785103 3777592736087003567677655)
                ·
                  refine ⟨5666389104130505351516483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777592736087003567677655 5666389104130505351516483)
                  ·
                    refine ⟨8499583656195758027274725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5666389104130505351516483 8499583656195758027274725)
                    ·
                      refine ⟨1593671935536704630114011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8499583656195758027274725 1593671935536704630114011)
                      ·
                        rfl

theorem cell23_3103665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_3103665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103665 prefixEnd_3103665 := by exact prefixLift 3103665
  have htrace : WordTrace (prefixWord ++ tailWord_3103665) baseStart_3103665 baseEnd_3103665 := by
    simpa [prefixWord, tailWord_3103665, baseEnd_3103665] using wordTrace_append hprefix tailTrace_3103665
  have hstable : (prefixWord ++ tailWord_3103665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103665).length < 2 ^ (prefixWord ++ tailWord_3103665).sum := by decide
  have hdescent : baseEnd_3103665 < baseStart_3103665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103687 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_3103687 : Nat := 118140960795 + 3103687 * 2 ^ 59
def prefixEnd_3103687 : Nat := 4983230072969 + 3 ^ 40 * 3103687 * 2
def baseEnd_3103687 : Nat := 1593683232111103544038909

theorem tailTrace_3103687 : CollatzResearch.WordTrace tailWord_3103687 prefixEnd_3103687 1593683232111103544038909 := by
  unfold tailWord_3103687
  simp only [CollatzResearch.WordTrace]
  refine ⟨113200764706879541383877315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75467176471253027589251543 113200764706879541383877315)
  ·
    refine ⟨169801147060319312075815973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113200764706879541383877315 169801147060319312075815973)
    ·
      refine ⟨31837715073809871014215495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169801147060319312075815973 31837715073809871014215495)
      ·
        refine ⟨47756572610714806521323243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31837715073809871014215495 47756572610714806521323243)
        ·
          refine ⟨71634858916072209781984865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47756572610714806521323243 71634858916072209781984865)
          ·
            refine ⟨53726144187054157336488649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71634858916072209781984865 53726144187054157336488649)
            ·
              refine ⟨40294608140290618002366487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53726144187054157336488649 40294608140290618002366487)
              ·
                refine ⟨60441912210435927003549731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40294608140290618002366487 60441912210435927003549731)
                ·
                  refine ⟨90662868315653890505324597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60441912210435927003549731 90662868315653890505324597)
                  ·
                    refine ⟨8499643904592552234874181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90662868315653890505324597 8499643904592552234874181)
                    ·
                      refine ⟨1593683232111103544038909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8499643904592552234874181 1593683232111103544038909)
                      ·
                        rfl

theorem cell23_3103687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_3103687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103687 prefixEnd_3103687 := by exact prefixLift 3103687
  have htrace : WordTrace (prefixWord ++ tailWord_3103687) baseStart_3103687 baseEnd_3103687 := by
    simpa [prefixWord, tailWord_3103687, baseEnd_3103687] using wordTrace_append hprefix tailTrace_3103687
  have hstable : (prefixWord ++ tailWord_3103687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103687).length < 2 ^ (prefixWord ++ tailWord_3103687).sum := by decide
  have hdescent : baseEnd_3103687 < baseStart_3103687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103697 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 2, 6]
def baseStart_3103697 : Nat := 118140960795 + 3103697 * 2 ^ 59
def prefixEnd_3103697 : Nat := 4983230072969 + 3 ^ 40 * 3103697 * 2
def baseEnd_3103697 : Nat := 531229455639216168304621

theorem tailTrace_3103697 : CollatzResearch.WordTrace tailWord_3103697 prefixEnd_3103697 531229455639216168304621 := by
  unfold tailWord_3103697
  simp only [CollatzResearch.WordTrace]
  refine ⟨113201129436843313091741345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75467419624562208727827563 113201129436843313091741345)
  ·
    refine ⟨84900847077632484818806009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113201129436843313091741345 84900847077632484818806009)
    ·
      refine ⟨63675635308224363614104507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84900847077632484818806009 63675635308224363614104507)
      ·
        refine ⟨95513452962336545421156761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63675635308224363614104507 95513452962336545421156761)
        ·
          refine ⟨71635089721752409065867571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95513452962336545421156761 71635089721752409065867571)
          ·
            refine ⟨107452634582628613598801357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71635089721752409065867571 107452634582628613598801357)
            ·
              refine ⟨40294737968485730099550509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107452634582628613598801357 40294737968485730099550509)
              ·
                refine ⟨15110526738182148787331441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40294737968485730099550509 15110526738182148787331441)
                ·
                  refine ⟨11332895053636611590498581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15110526738182148787331441 11332895053636611590498581)
                  ·
                    refine ⟨531229455639216168304621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11332895053636611590498581 531229455639216168304621)
                    ·
                      rfl

theorem cell23_3103697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_3103697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103697 prefixEnd_3103697 := by exact prefixLift 3103697
  have htrace : WordTrace (prefixWord ++ tailWord_3103697) baseStart_3103697 baseEnd_3103697 := by
    simpa [prefixWord, tailWord_3103697, baseEnd_3103697] using wordTrace_append hprefix tailTrace_3103697
  have hstable : (prefixWord ++ tailWord_3103697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103697).length < 2 ^ (prefixWord ++ tailWord_3103697).sum := by decide
  have hdescent : baseEnd_3103697 < baseStart_3103697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103698 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3103698 : Nat := 118140960795 + 3103698 * 2 ^ 59
def prefixEnd_3103698 : Nat := 4983230072969 + 3 ^ 40 * 3103698 * 2
def baseEnd_3103698 : Nat := 1593688880398303001001359

theorem tailTrace_3103698 : CollatzResearch.WordTrace tailWord_3103698 prefixEnd_3103698 1593688880398303001001359 := by
  unfold tailWord_3103698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28300291477459922565631937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75467443939893126841685165 28300291477459922565631937)
  ·
    refine ⟨21225218608094941924223953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28300291477459922565631937 21225218608094941924223953)
    ·
      refine ⟨15918913956071206443167965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21225218608094941924223953 15918913956071206443167965)
      ·
        refine ⟨5969592733526702416187987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15918913956071206443167965 5969592733526702416187987)
        ·
          refine ⟨8954389100290053624281981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969592733526702416187987 8954389100290053624281981)
          ·
            refine ⟨3357895912608770109105743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8954389100290053624281981 3357895912608770109105743)
            ·
              refine ⟨5036843868913155163658615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357895912608770109105743 5036843868913155163658615)
              ·
                refine ⟨7555265803369732745487923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036843868913155163658615 7555265803369732745487923)
                ·
                  refine ⟨11332898705054599118231885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7555265803369732745487923 11332898705054599118231885)
                  ·
                    refine ⟨4249837014395474669336957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11332898705054599118231885 4249837014395474669336957)
                    ·
                      refine ⟨1593688880398303001001359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4249837014395474669336957 1593688880398303001001359)
                      ·
                        rfl

theorem cell23_3103698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3103698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103698 prefixEnd_3103698 := by exact prefixLift 3103698
  have htrace : WordTrace (prefixWord ++ tailWord_3103698) baseStart_3103698 baseEnd_3103698 := by
    simpa [prefixWord, tailWord_3103698, baseEnd_3103698] using wordTrace_append hprefix tailTrace_3103698
  have hstable : (prefixWord ++ tailWord_3103698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103698).length < 2 ^ (prefixWord ++ tailWord_3103698).sum := by decide
  have hdescent : baseEnd_3103698 < baseStart_3103698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103737 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3103737 : Nat := 118140960795 + 3103737 * 2 ^ 59
def prefixEnd_3103737 : Nat := 4983230072969 + 3 ^ 40 * 3103737 * 2
def baseEnd_3103737 : Nat := 1593708906143828348413679

theorem tailTrace_3103737 : CollatzResearch.WordTrace tailWord_3103737 prefixEnd_3103737 1593708906143828348413679 := by
  unfold tailWord_3103737
  simp only [CollatzResearch.WordTrace]
  refine ⟨113202588356698399923197465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75468392237798933282131643 113202588356698399923197465)
  ·
    refine ⟨84901941267523799942398099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113202588356698399923197465 84901941267523799942398099)
    ·
      refine ⟨127352911901285699913597149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84901941267523799942398099 127352911901285699913597149)
      ·
        refine ⟨47757341962982137467598931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127352911901285699913597149 47757341962982137467598931)
        ·
          refine ⟨71636012944473206201398397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47757341962982137467598931 71636012944473206201398397)
          ·
            refine ⟨26863504854177452325524399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71636012944473206201398397 26863504854177452325524399)
            ·
              refine ⟨40295257281266178488286599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26863504854177452325524399 40295257281266178488286599)
              ·
                refine ⟨60442885921899267732429899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40295257281266178488286599 60442885921899267732429899)
                ·
                  refine ⟨90664328882848901598644849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60442885921899267732429899 90664328882848901598644849)
                  ·
                    refine ⟨67998246662136676198983637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90664328882848901598644849 67998246662136676198983637)
                    ·
                      refine ⟨1593708906143828348413679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67998246662136676198983637 1593708906143828348413679)
                      ·
                        rfl

theorem cell23_3103737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3103737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103737 prefixEnd_3103737 := by exact prefixLift 3103737
  have htrace : WordTrace (prefixWord ++ tailWord_3103737) baseStart_3103737 baseEnd_3103737 := by
    simpa [prefixWord, tailWord_3103737, baseEnd_3103737] using wordTrace_append hprefix tailTrace_3103737
  have hstable : (prefixWord ++ tailWord_3103737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103737).length < 2 ^ (prefixWord ++ tailWord_3103737).sum := by decide
  have hdescent : baseEnd_3103737 < baseStart_3103737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103755 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 2, 2, 2]
def baseStart_3103755 : Nat := 118140960795 + 3103755 * 2 ^ 59
def prefixEnd_3103755 : Nat := 4983230072969 + 3 ^ 40 * 3103755 * 2
def baseEnd_3103755 : Nat := 1593718148795609277988597

theorem tailTrace_3103755 : CollatzResearch.WordTrace tailWord_3103755 prefixEnd_3103755 1593718148795609277988597 := by
  unfold tailWord_3103755
  simp only [CollatzResearch.WordTrace]
  refine ⟨113203244870633188997352719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75468829913755459331568479 113203244870633188997352719)
  ·
    refine ⟨169804867305949783496029079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113203244870633188997352719 169804867305949783496029079)
    ·
      refine ⟨254707300958924675244043619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169804867305949783496029079 254707300958924675244043619)
      ·
        refine ⟨382060951438387012866065429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254707300958924675244043619 382060951438387012866065429)
        ·
          refine ⟨17909107098674391228096817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 382060951438387012866065429 17909107098674391228096817)
          ·
            refine ⟨13431830324005793421072613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17909107098674391228096817 13431830324005793421072613)
            ·
              refine ⟨2518468185751086266451115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13431830324005793421072613 2518468185751086266451115)
              ·
                refine ⟨3777702278626629399676673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518468185751086266451115 3777702278626629399676673)
                ·
                  refine ⟨2833276708969972049757505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3777702278626629399676673 2833276708969972049757505)
                  ·
                    refine ⟨2124957531727479037318129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2833276708969972049757505 2124957531727479037318129)
                    ·
                      refine ⟨1593718148795609277988597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124957531727479037318129 1593718148795609277988597)
                      ·
                        rfl

theorem cell23_3103755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 2, 2].length) (baseStart_3103755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103755 prefixEnd_3103755 := by exact prefixLift 3103755
  have htrace : WordTrace (prefixWord ++ tailWord_3103755) baseStart_3103755 baseEnd_3103755 := by
    simpa [prefixWord, tailWord_3103755, baseEnd_3103755] using wordTrace_append hprefix tailTrace_3103755
  have hstable : (prefixWord ++ tailWord_3103755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103755).length < 2 ^ (prefixWord ++ tailWord_3103755).sum := by decide
  have hdescent : baseEnd_3103755 < baseStart_3103755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103798 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_3103798 : Nat := 118140960795 + 3103798 * 2 ^ 59
def prefixEnd_3103798 : Nat := 4983230072969 + 3 ^ 40 * 3103798 * 2
def baseEnd_3103798 : Nat := 1593740228463752609750899

theorem tailTrace_3103798 : CollatzResearch.WordTrace tailWord_3103798 prefixEnd_3103798 1593740228463752609750899 := by
  unfold tailWord_3103798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075300825592337958823003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75469875472984938227445365 7075300825592337958823003)
  ·
    refine ⟨10612951238388506938234505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7075300825592337958823003 10612951238388506938234505)
    ·
      refine ⟨7959713428791380203675879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10612951238388506938234505 7959713428791380203675879)
      ·
        refine ⟨11939570143187070305513819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7959713428791380203675879 11939570143187070305513819)
        ·
          refine ⟨17909355214780605458270729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11939570143187070305513819 17909355214780605458270729)
          ·
            refine ⟨13432016411085454093703047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17909355214780605458270729 13432016411085454093703047)
            ·
              refine ⟨20148024616628181140554571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13432016411085454093703047 20148024616628181140554571)
              ·
                refine ⟨30222036924942271710831857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20148024616628181140554571 30222036924942271710831857)
                ·
                  refine ⟨22666527693706703783123893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30222036924942271710831857 22666527693706703783123893)
                  ·
                    refine ⟨2124986971285003479667865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22666527693706703783123893 2124986971285003479667865)
                    ·
                      refine ⟨1593740228463752609750899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124986971285003479667865 1593740228463752609750899)
                      ·
                        rfl

theorem cell23_3103798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_3103798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103798 prefixEnd_3103798 := by exact prefixLift 3103798
  have htrace : WordTrace (prefixWord ++ tailWord_3103798) baseStart_3103798 baseEnd_3103798 := by
    simpa [prefixWord, tailWord_3103798, baseEnd_3103798] using wordTrace_append hprefix tailTrace_3103798
  have hstable : (prefixWord ++ tailWord_3103798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103798).length < 2 ^ (prefixWord ++ tailWord_3103798).sum := by decide
  have hdescent : baseEnd_3103798 < baseStart_3103798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103811 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 2, 4, 2]
def baseStart_3103811 : Nat := 118140960795 + 3103811 * 2 ^ 59
def prefixEnd_3103811 : Nat := 4983230072969 + 3 ^ 40 * 3103811 * 2
def baseEnd_3103811 : Nat := 1593746903712261058888339

theorem tailTrace_3103811 : CollatzResearch.WordTrace tailWord_3103811 prefixEnd_3103811 1593746903712261058888339 := by
  unfold tailWord_3103811
  simp only [CollatzResearch.WordTrace]
  refine ⟨113205287358430310561391287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75470191572286873707594191 113205287358430310561391287)
  ·
    refine ⟨169807931037645465842086931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113205287358430310561391287 169807931037645465842086931)
    ·
      refine ⟨254711896556468198763130397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169807931037645465842086931 254711896556468198763130397)
      ·
        refine ⟨95516961208675574536173899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254711896556468198763130397 95516961208675574536173899)
        ·
          refine ⟨143275441813013361804260849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95516961208675574536173899 143275441813013361804260849)
          ·
            refine ⟨107456581359760021353195637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143275441813013361804260849 107456581359760021353195637)
            ·
              refine ⟨10074054502477502001862091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107456581359760021353195637 10074054502477502001862091)
              ·
                refine ⟨15111081753716253002793137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10074054502477502001862091 15111081753716253002793137)
                ·
                  refine ⟨11333311315287189752094853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15111081753716253002793137 11333311315287189752094853)
                  ·
                    refine ⟨2124995871616348078517785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11333311315287189752094853 2124995871616348078517785)
                    ·
                      refine ⟨1593746903712261058888339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124995871616348078517785 1593746903712261058888339)
                      ·
                        rfl

theorem cell23_3103811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_3103811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103811 prefixEnd_3103811 := by exact prefixLift 3103811
  have htrace : WordTrace (prefixWord ++ tailWord_3103811) baseStart_3103811 baseEnd_3103811 := by
    simpa [prefixWord, tailWord_3103811, baseEnd_3103811] using wordTrace_append hprefix tailTrace_3103811
  have hstable : (prefixWord ++ tailWord_3103811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103811).length < 2 ^ (prefixWord ++ tailWord_3103811).sum := by decide
  have hdescent : baseEnd_3103811 < baseStart_3103811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103864 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 5, 5]
def baseStart_3103864 : Nat := 118140960795 + 3103864 * 2 ^ 59
def prefixEnd_3103864 : Nat := 4983230072969 + 3 ^ 40 * 3103864 * 2
def baseEnd_3103864 : Nat := 531258039395649783841865

theorem tailTrace_3103864 : CollatzResearch.WordTrace tailWord_3103864 prefixEnd_3103864 531258039395649783841865 := by
  unfold tailWord_3103864
  simp only [CollatzResearch.WordTrace]
  refine ⟨56603610213619150306535323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75471480284825533742047097 56603610213619150306535323)
  ·
    refine ⟨84905415320428725459802985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56603610213619150306535323 84905415320428725459802985)
    ·
      refine ⟨63679061490321544094852239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84905415320428725459802985 63679061490321544094852239)
      ·
        refine ⟨95518592235482316142278359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63679061490321544094852239 95518592235482316142278359)
        ·
          refine ⟨143277888353223474213417539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95518592235482316142278359 143277888353223474213417539)
          ·
            refine ⟨214916832529835211320126309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143277888353223474213417539 214916832529835211320126309)
            ·
              refine ⟨40296906099344102122523683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214916832529835211320126309 40296906099344102122523683)
              ·
                refine ⟨60445359149016153183785525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40296906099344102122523683 60445359149016153183785525)
                ·
                  refine ⟨5666752420220264360979893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60445359149016153183785525 5666752420220264360979893)
                  ·
                    refine ⟨531258039395649783841865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5666752420220264360979893 531258039395649783841865)
                    ·
                      rfl

theorem cell23_3103864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_3103864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103864 prefixEnd_3103864 := by exact prefixLift 3103864
  have htrace : WordTrace (prefixWord ++ tailWord_3103864) baseStart_3103864 baseEnd_3103864 := by
    simpa [prefixWord, tailWord_3103864, baseEnd_3103864] using wordTrace_append hprefix tailTrace_3103864
  have hstable : (prefixWord ++ tailWord_3103864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103864).length < 2 ^ (prefixWord ++ tailWord_3103864).sum := by decide
  have hdescent : baseEnd_3103864 < baseStart_3103864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103881 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 1, 5]
def baseStart_3103881 : Nat := 118140960795 + 3103881 * 2 ^ 59
def prefixEnd_3103881 : Nat := 4983230072969 + 3 ^ 40 * 3103881 * 2
def baseEnd_3103881 : Nat := 531260949119358595004339

theorem tailTrace_3103881 : CollatzResearch.WordTrace tailWord_3103881 prefixEnd_3103881 531260949119358595004339 := by
  unfold tailWord_3103881
  simp only [CollatzResearch.WordTrace]
  refine ⟨113207840468176712516439497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75471893645451141677626331 113207840468176712516439497)
  ·
    refine ⟨84905880351132534387329623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113207840468176712516439497 84905880351132534387329623)
    ·
      refine ⟨127358820526698801580994435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84905880351132534387329623 127358820526698801580994435)
      ·
        refine ⟨191038230790048202371491653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127358820526698801580994435 191038230790048202371491653)
        ·
          refine ⟨35819668273134037944654685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191038230790048202371491653 35819668273134037944654685)
          ·
            refine ⟨13432375602425264229245507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35819668273134037944654685 13432375602425264229245507)
            ·
              refine ⟨20148563403637896343868261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13432375602425264229245507 20148563403637896343868261)
              ·
                refine ⟨3777855638182105564475299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20148563403637896343868261 3777855638182105564475299)
                ·
                  refine ⟨5666783457273158346712949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777855638182105564475299 5666783457273158346712949)
                  ·
                    refine ⟨531260949119358595004339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5666783457273158346712949 531260949119358595004339)
                    ·
                      rfl

theorem cell23_3103881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 5].length) (baseStart_3103881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103881 prefixEnd_3103881 := by exact prefixLift 3103881
  have htrace : WordTrace (prefixWord ++ tailWord_3103881) baseStart_3103881 baseEnd_3103881 := by
    simpa [prefixWord, tailWord_3103881, baseEnd_3103881] using wordTrace_append hprefix tailTrace_3103881
  have hstable : (prefixWord ++ tailWord_3103881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103881).length < 2 ^ (prefixWord ++ tailWord_3103881).sum := by decide
  have hdescent : baseEnd_3103881 < baseStart_3103881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103884 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3103884 : Nat := 118140960795 + 3103884 * 2 ^ 59
def prefixEnd_3103884 : Nat := 4983230072969 + 3 ^ 40 * 3103884 * 2
def baseEnd_3103884 : Nat := 1593784387800039273275503

theorem tailTrace_3103884 : CollatzResearch.WordTrace tailWord_3103884 prefixEnd_3103884 1593784387800039273275503 := by
  unfold tailWord_3103884
  simp only [CollatzResearch.WordTrace]
  refine ⟨56603974943582922014399353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75471966591443896019199137 56603974943582922014399353)
  ·
    refine ⟨42452981207687191510799515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56603974943582922014399353 42452981207687191510799515)
    ·
      refine ⟨63679471811530787266199273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42452981207687191510799515 63679471811530787266199273)
      ·
        refine ⟨47759603858648090449649455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63679471811530787266199273 47759603858648090449649455)
        ·
          refine ⟨71639405787972135674474183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47759603858648090449649455 71639405787972135674474183)
          ·
            refine ⟨107459108681958203511711275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71639405787972135674474183 107459108681958203511711275)
            ·
              refine ⟨161188663022937305267566913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107459108681958203511711275 161188663022937305267566913)
              ·
                refine ⟨120891497267202978950675185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161188663022937305267566913 120891497267202978950675185)
                ·
                  refine ⟨90668622950402234213006389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120891497267202978950675185 90668622950402234213006389)
                  ·
                    refine ⟨8500183401600209457469349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90668622950402234213006389 8500183401600209457469349)
                    ·
                      refine ⟨1593784387800039273275503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8500183401600209457469349 1593784387800039273275503)
                      ·
                        rfl

theorem cell23_3103884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3103884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103884 prefixEnd_3103884 := by exact prefixLift 3103884
  have htrace : WordTrace (prefixWord ++ tailWord_3103884) baseStart_3103884 baseEnd_3103884 := by
    simpa [prefixWord, tailWord_3103884, baseEnd_3103884] using wordTrace_append hprefix tailTrace_3103884
  have hstable : (prefixWord ++ tailWord_3103884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103884).length < 2 ^ (prefixWord ++ tailWord_3103884).sum := by decide
  have hdescent : baseEnd_3103884 < baseStart_3103884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103898 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_3103898 : Nat := 118140960795 + 3103898 * 2 ^ 59
def prefixEnd_3103898 : Nat := 4983230072969 + 3 ^ 40 * 3103898 * 2
def baseEnd_3103898 : Nat := 531263858843067406166813

theorem tailTrace_3103898 : CollatzResearch.WordTrace tailWord_3103898 prefixEnd_3103898 531263858843067406166813 := by
  unfold tailWord_3103898
  simp only [CollatzResearch.WordTrace]
  refine ⟨28302115127278781104952087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75472307006076749613205565 28302115127278781104952087)
  ·
    refine ⟨42453172690918171657428131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28302115127278781104952087 42453172690918171657428131)
    ·
      refine ⟨63679759036377257486142197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42453172690918171657428131 63679759036377257486142197)
      ·
        refine ⟨5969977409660367889325831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63679759036377257486142197 5969977409660367889325831)
        ·
          refine ⟨8954966114490551833988747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969977409660367889325831 8954966114490551833988747)
          ·
            refine ⟨13432449171735827750983121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8954966114490551833988747 13432449171735827750983121)
            ·
              refine ⟨10074336878801870813237341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13432449171735827750983121 10074336878801870813237341)
              ·
                refine ⟨3777876329550701554964003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10074336878801870813237341 3777876329550701554964003)
                ·
                  refine ⟨5666814494326052332446005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777876329550701554964003 5666814494326052332446005)
                  ·
                    refine ⟨531263858843067406166813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5666814494326052332446005 531263858843067406166813)
                    ·
                      rfl

theorem cell23_3103898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_3103898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103898 prefixEnd_3103898 := by exact prefixLift 3103898
  have htrace : WordTrace (prefixWord ++ tailWord_3103898) baseStart_3103898 baseEnd_3103898 := by
    simpa [prefixWord, tailWord_3103898, baseEnd_3103898] using wordTrace_append hprefix tailTrace_3103898
  have hstable : (prefixWord ++ tailWord_3103898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103898).length < 2 ^ (prefixWord ++ tailWord_3103898).sum := by decide
  have hdescent : baseEnd_3103898 < baseStart_3103898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103949 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3103949 : Nat := 118140960795 + 3103949 * 2 ^ 59
def prefixEnd_3103949 : Nat := 4983230072969 + 3 ^ 40 * 3103949 * 2
def baseEnd_3103949 : Nat := 531272588014193839654235

theorem tailTrace_3103949 : CollatzResearch.WordTrace tailWord_3103949 prefixEnd_3103949 531272588014193839654235 := by
  unfold tailWord_3103949
  simp only [CollatzResearch.WordTrace]
  refine ⟨113210320631930360129914901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75473547087953573419943267 113210320631930360129914901)
  ·
    refine ⟨5306733779621735631089761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113210320631930360129914901 5306733779621735631089761)
    ·
      refine ⟨3980050334716301723317321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5306733779621735631089761 3980050334716301723317321)
      ·
        refine ⟨2985037751037226292487991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3980050334716301723317321 2985037751037226292487991)
        ·
          refine ⟨4477556626555839438731987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2985037751037226292487991 4477556626555839438731987)
          ·
            refine ⟨6716334939833759158097981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477556626555839438731987 6716334939833759158097981)
            ·
              refine ⟨2518625602437659684286743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6716334939833759158097981 2518625602437659684286743)
              ·
                refine ⟨3777938403656489526430115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518625602437659684286743 3777938403656489526430115)
                ·
                  refine ⟨5666907605484734289645173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777938403656489526430115 5666907605484734289645173)
                  ·
                    refine ⟨531272588014193839654235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5666907605484734289645173 531272588014193839654235)
                    ·
                      rfl

theorem cell23_3103949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3103949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103949 prefixEnd_3103949 := by exact prefixLift 3103949
  have htrace : WordTrace (prefixWord ++ tailWord_3103949) baseStart_3103949 baseEnd_3103949 := by
    simpa [prefixWord, tailWord_3103949, baseEnd_3103949] using wordTrace_append hprefix tailTrace_3103949
  have hstable : (prefixWord ++ tailWord_3103949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103949).length < 2 ^ (prefixWord ++ tailWord_3103949).sum := by decide
  have hdescent : baseEnd_3103949 < baseStart_3103949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103958 : List Nat := [5, 2, 1, 2, 2, 11]
def baseStart_3103958 : Nat := 118140960795 + 3103958 * 2 ^ 59
def prefixEnd_3103958 : Nat := 4983230072969 + 3 ^ 40 * 3103958 * 2
def baseEnd_3103958 : Nat := 6558939857483423801441

theorem tailTrace_3103958 : CollatzResearch.WordTrace tailWord_3103958 prefixEnd_3103958 6558939857483423801441 := by
  unfold tailWord_3103958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075665555556109666687033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75473765925931836444661685 7075665555556109666687033)
  ·
    refine ⟨5306749166667082250015275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7075665555556109666687033 5306749166667082250015275)
    ·
      refine ⟨7960123750000623375022913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5306749166667082250015275 7960123750000623375022913)
      ·
        refine ⟨5970092812500467531267185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7960123750000623375022913 5970092812500467531267185)
        ·
          refine ⟨4477569609375350648450389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5970092812500467531267185 4477569609375350648450389)
          ·
            refine ⟨6558939857483423801441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4477569609375350648450389 6558939857483423801441)
            ·
              rfl

theorem cell23_3103958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 11].length) (baseStart_3103958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103958 prefixEnd_3103958 := by exact prefixLift 3103958
  have htrace : WordTrace (prefixWord ++ tailWord_3103958) baseStart_3103958 baseEnd_3103958 := by
    simpa [prefixWord, tailWord_3103958, baseEnd_3103958] using wordTrace_append hprefix tailTrace_3103958
  have hstable : (prefixWord ++ tailWord_3103958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103958).length < 2 ^ (prefixWord ++ tailWord_3103958).sum := by decide
  have hdescent : baseEnd_3103958 < baseStart_3103958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103969 : List Nat := [1, 2, 3, 1, 3, 2, 4, 2, 1, 2, 2]
def baseStart_3103969 : Nat := 118140960795 + 3103969 * 2 ^ 59
def prefixEnd_3103969 : Nat := 4983230072969 + 3 ^ 40 * 3103969 * 2
def baseEnd_3103969 : Nat := 1593828033655671440712613

theorem tailTrace_3103969 : CollatzResearch.WordTrace tailWord_3103969 prefixEnd_3103969 1593828033655671440712613 := by
  unfold tailWord_3103969
  simp only [CollatzResearch.WordTrace]
  refine ⟨113211050091857903545642961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75474033394571935697095307 113211050091857903545642961)
  ·
    refine ⟨84908287568893427659232221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113211050091857903545642961 84908287568893427659232221)
    ·
      refine ⟨31840607838335035372212083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84908287568893427659232221 31840607838335035372212083)
      ·
        refine ⟨47760911757502553058318125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31840607838335035372212083 47760911757502553058318125)
        ·
          refine ⟨17910341909063457396869297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47760911757502553058318125 17910341909063457396869297)
          ·
            refine ⟨13432756431797593047651973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17910341909063457396869297 13432756431797593047651973)
            ·
              refine ⟨2518641830962048696434745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13432756431797593047651973 2518641830962048696434745)
              ·
                refine ⟨1888981373221536522326059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518641830962048696434745 1888981373221536522326059)
                ·
                  refine ⟨2833472059832304783489089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888981373221536522326059 2833472059832304783489089)
                  ·
                    refine ⟨2125104044874228587616817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2833472059832304783489089 2125104044874228587616817)
                    ·
                      refine ⟨1593828033655671440712613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125104044874228587616817 1593828033655671440712613)
                      ·
                        rfl

theorem cell23_3103969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_3103969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103969 prefixEnd_3103969 := by exact prefixLift 3103969
  have htrace : WordTrace (prefixWord ++ tailWord_3103969) baseStart_3103969 baseEnd_3103969 := by
    simpa [prefixWord, tailWord_3103969, baseEnd_3103969] using wordTrace_append hprefix tailTrace_3103969
  have hstable : (prefixWord ++ tailWord_3103969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103969).length < 2 ^ (prefixWord ++ tailWord_3103969).sum := by decide
  have hdescent : baseEnd_3103969 < baseStart_3103969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103975 : List Nat := [1, 1, 5, 3, 3, 1, 1, 8]
def baseStart_3103975 : Nat := 118140960795 + 3103975 * 2 ^ 59
def prefixEnd_3103975 : Nat := 4983230072969 + 3 ^ 40 * 3103975 * 2
def baseEnd_3103975 : Nat := 59030782019985126564355

theorem tailTrace_3103975 : CollatzResearch.WordTrace tailWord_3103975 prefixEnd_3103975 59030782019985126564355 := by
  unfold tailWord_3103975
  simp only [CollatzResearch.WordTrace]
  refine ⟨113211268929836166570361379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75474179286557444380240919 113211268929836166570361379)
  ·
    refine ⟨169816903394754249855542069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113211268929836166570361379 169816903394754249855542069)
    ·
      refine ⟨15920334693258210923957069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169816903394754249855542069 15920334693258210923957069)
      ·
        refine ⟨5970125509971829096483901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15920334693258210923957069 5970125509971829096483901)
        ·
          refine ⟨2238797066239435911181463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5970125509971829096483901 2238797066239435911181463)
          ·
            refine ⟨3358195599359153866772195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238797066239435911181463 3358195599359153866772195)
            ·
              refine ⟨5037293399038730800158293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3358195599359153866772195 5037293399038730800158293)
              ·
                refine ⟨59030782019985126564355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5037293399038730800158293 59030782019985126564355)
                ·
                  rfl

theorem cell23_3103975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 8].length) (baseStart_3103975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103975 prefixEnd_3103975 := by exact prefixLift 3103975
  have htrace : WordTrace (prefixWord ++ tailWord_3103975) baseStart_3103975 baseEnd_3103975 := by
    simpa [prefixWord, tailWord_3103975, baseEnd_3103975] using wordTrace_append hprefix tailTrace_3103975
  have hstable : (prefixWord ++ tailWord_3103975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103975).length < 2 ^ (prefixWord ++ tailWord_3103975).sum := by decide
  have hdescent : baseEnd_3103975 < baseStart_3103975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104012 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 1, 3, 2]
def baseStart_3104012 : Nat := 118140960795 + 3104012 * 2 ^ 59
def prefixEnd_3104012 : Nat := 4983230072969 + 3 ^ 40 * 3104012 * 2
def baseEnd_3104012 : Nat := 1593850113323814772474915

theorem tailTrace_3104012 : CollatzResearch.WordTrace tailWord_3104012 prefixEnd_3104012 1593850113323814772474915 := by
  unfold tailWord_3104012
  simp only [CollatzResearch.WordTrace]
  refine ⟨56606309215351060944729145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75475078953801414592972193 56606309215351060944729145)
  ·
    refine ⟨42454731911513295708546859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56606309215351060944729145 42454731911513295708546859)
    ·
      refine ⟨63682097867269943562820289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42454731911513295708546859 63682097867269943562820289)
      ·
        refine ⟨47761573400452457672115217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63682097867269943562820289 47761573400452457672115217)
        ·
          refine ⟨35821180050339343254086413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47761573400452457672115217 35821180050339343254086413)
          ·
            refine ⟨13432942518877253720282405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35821180050339343254086413 13432942518877253720282405)
            ·
              refine ⟨2518676722289485072552951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13432942518877253720282405 2518676722289485072552951)
              ·
                refine ⟨3778015083434227608829427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518676722289485072552951 3778015083434227608829427)
                ·
                  refine ⟨5667022625151341413244141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3778015083434227608829427 5667022625151341413244141)
                  ·
                    refine ⟨2125133484431753029966553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5667022625151341413244141 2125133484431753029966553)
                    ·
                      refine ⟨1593850113323814772474915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125133484431753029966553 1593850113323814772474915)
                      ·
                        rfl

theorem cell23_3104012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_3104012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104012 prefixEnd_3104012 := by exact prefixLift 3104012
  have htrace : WordTrace (prefixWord ++ tailWord_3104012) baseStart_3104012 baseEnd_3104012 := by
    simpa [prefixWord, tailWord_3104012, baseEnd_3104012] using wordTrace_append hprefix tailTrace_3104012
  have hstable : (prefixWord ++ tailWord_3104012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104012).length < 2 ^ (prefixWord ++ tailWord_3104012).sum := by decide
  have hdescent : baseEnd_3104012 < baseStart_3104012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104041 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 3]
def baseStart_3104041 : Nat := 118140960795 + 3104041 * 2 ^ 59
def prefixEnd_3104041 : Nat := 4983230072969 + 3 ^ 40 * 3104041 * 2
def baseEnd_3104041 : Nat := 1593865004262795159012281

theorem tailTrace_3104041 : CollatzResearch.WordTrace tailWord_3104041 prefixEnd_3104041 1593865004262795159012281 := by
  unfold tailWord_3104041
  simp only [CollatzResearch.WordTrace]
  refine ⟨113213676147597059842263977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75475784098398039894842651 113213676147597059842263977)
  ·
    refine ⟨84910257110697794881697983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113213676147597059842263977 84910257110697794881697983)
    ·
      refine ⟨127365385666046692322546975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84910257110697794881697983 127365385666046692322546975)
      ·
        refine ⟨191048078499070038483820463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127365385666046692322546975 191048078499070038483820463)
        ·
          refine ⟨286572117748605057725730695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191048078499070038483820463 286572117748605057725730695)
          ·
            refine ⟨429858176622907586588596043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286572117748605057725730695 429858176622907586588596043)
            ·
              refine ⟨644787264934361379882894065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429858176622907586588596043 644787264934361379882894065)
              ·
                refine ⟨483590448700771034912170549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644787264934361379882894065 483590448700771034912170549)
                ·
                  refine ⟨45336604565697284523015989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 483590448700771034912170549 45336604565697284523015989)
                  ·
                    refine ⟨4250306678034120424032749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45336604565697284523015989 4250306678034120424032749)
                    ·
                      refine ⟨1593865004262795159012281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4250306678034120424032749 1593865004262795159012281)
                      ·
                        rfl

theorem cell23_3104041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_3104041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104041 prefixEnd_3104041 := by exact prefixLift 3104041
  have htrace : WordTrace (prefixWord ++ tailWord_3104041) baseStart_3104041 baseEnd_3104041 := by
    simpa [prefixWord, tailWord_3104041, baseEnd_3104041] using wordTrace_append hprefix tailTrace_3104041
  have hstable : (prefixWord ++ tailWord_3104041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104041).length < 2 ^ (prefixWord ++ tailWord_3104041).sum := by decide
  have hdescent : baseEnd_3104041 < baseStart_3104041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104042 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_3104042 : Nat := 118140960795 + 3104042 * 2 ^ 59
def prefixEnd_3104042 : Nat := 4983230072969 + 3 ^ 40 * 3104042 * 2
def baseEnd_3104042 : Nat := 1593865517743449655099777

theorem tailTrace_3104042 : CollatzResearch.WordTrace tailWord_3104042 prefixEnd_3104042 1593865517743449655099777 := by
  unfold tailWord_3104042
  simp only [CollatzResearch.WordTrace]
  refine ⟨28303428155148359253262595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75475808413728958008700253 28303428155148359253262595)
  ·
    refine ⟨42455142232722538879893893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28303428155148359253262595 42455142232722538879893893)
    ·
      refine ⟨7960339168635476039980105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42455142232722538879893893 7960339168635476039980105)
      ·
        refine ⟨5970254376476607029985079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7960339168635476039980105 5970254376476607029985079)
        ·
          refine ⟨8955381564714910544977619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970254376476607029985079 8955381564714910544977619)
          ·
            refine ⟨13433072347072365817466429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8955381564714910544977619 13433072347072365817466429)
            ·
              refine ⟨5037402130152137181549911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13433072347072365817466429 5037402130152137181549911)
              ·
                refine ⟨7556103195228205772324867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5037402130152137181549911 7556103195228205772324867)
                ·
                  refine ⟨11334154792842308658487301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7556103195228205772324867 11334154792842308658487301)
                  ·
                    refine ⟨2125154023657932873466369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11334154792842308658487301 2125154023657932873466369)
                    ·
                      refine ⟨1593865517743449655099777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125154023657932873466369 1593865517743449655099777)
                      ·
                        rfl

theorem cell23_3104042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_3104042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104042 prefixEnd_3104042 := by exact prefixLift 3104042
  have htrace : WordTrace (prefixWord ++ tailWord_3104042) baseStart_3104042 baseEnd_3104042 := by
    simpa [prefixWord, tailWord_3104042, baseEnd_3104042] using wordTrace_append hprefix tailTrace_3104042
  have hstable : (prefixWord ++ tailWord_3104042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104042).length < 2 ^ (prefixWord ++ tailWord_3104042).sum := by decide
  have hdescent : baseEnd_3104042 < baseStart_3104042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104078 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_3104078 : Nat := 118140960795 + 3104078 * 2 ^ 59
def prefixEnd_3104078 : Nat := 4983230072969 + 3 ^ 40 * 3104078 * 2
def baseEnd_3104078 : Nat := 531294667682337171416537

theorem tailTrace_3104078 : CollatzResearch.WordTrace tailWord_3104078 prefixEnd_3104078 531294667682337171416537 := by
  unfold tailWord_3104078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14151878206057876895170111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75476683765642010107573925 14151878206057876895170111)
  ·
    refine ⟨21227817309086815342755167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14151878206057876895170111 21227817309086815342755167)
    ·
      refine ⟨31841725963630223014132751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21227817309086815342755167 31841725963630223014132751)
      ·
        refine ⟨47762588945445334521199127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31841725963630223014132751 47762588945445334521199127)
        ·
          refine ⟨71643883418168001781798691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47762588945445334521199127 71643883418168001781798691)
          ·
            refine ⟨107465825127252002672698037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71643883418168001781798691 107465825127252002672698037)
            ·
              refine ⟨10074921105679875250565441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107465825127252002672698037 10074921105679875250565441)
              ·
                refine ⟨7556190829259906437924081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10074921105679875250565441 7556190829259906437924081)
                ·
                  refine ⟨5667143121944929828443061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7556190829259906437924081 5667143121944929828443061)
                  ·
                    refine ⟨531294667682337171416537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5667143121944929828443061 531294667682337171416537)
                    ·
                      rfl

theorem cell23_3104078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_3104078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104078 prefixEnd_3104078 := by exact prefixLift 3104078
  have htrace : WordTrace (prefixWord ++ tailWord_3104078) baseStart_3104078 baseEnd_3104078 := by
    simpa [prefixWord, tailWord_3104078, baseEnd_3104078] using wordTrace_append hprefix tailTrace_3104078
  have hstable : (prefixWord ++ tailWord_3104078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104078).length < 2 ^ (prefixWord ++ tailWord_3104078).sum := by decide
  have hdescent : baseEnd_3104078 < baseStart_3104078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104093 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3104093 : Nat := 118140960795 + 3104093 * 2 ^ 59
def prefixEnd_3104093 : Nat := 4983230072969 + 3 ^ 40 * 3104093 * 2
def baseEnd_3104093 : Nat := 1593891705256828955562043

theorem tailTrace_3104093 : CollatzResearch.WordTrace tailWord_3104093 prefixEnd_3104093 1593891705256828955562043 := by
  unfold tailWord_3104093
  simp only [CollatzResearch.WordTrace]
  refine ⟨113215572743408672723156933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75477048495605781815437955 113215572743408672723156933)
  ·
    refine ⟨21227919889389126135591925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113215572743408672723156933 21227919889389126135591925)
    ·
      refine ⟨1990117489630230575211743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21227919889389126135591925 1990117489630230575211743)
      ·
        refine ⟨2985176234445345862817615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990117489630230575211743 2985176234445345862817615)
        ·
          refine ⟨4477764351668018794226423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2985176234445345862817615 4477764351668018794226423)
          ·
            refine ⟨6716646527502028191339635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477764351668018794226423 6716646527502028191339635)
            ·
              refine ⟨10074969791253042287009453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716646527502028191339635 10074969791253042287009453)
              ·
                refine ⟨3778113671719890857628545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10074969791253042287009453 3778113671719890857628545)
                ·
                  refine ⟨2833585253789918143221409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3778113671719890857628545 2833585253789918143221409)
                  ·
                    refine ⟨2125188940342438607416057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2833585253789918143221409 2125188940342438607416057)
                    ·
                      refine ⟨1593891705256828955562043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125188940342438607416057 1593891705256828955562043)
                      ·
                        rfl

theorem cell23_3104093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3104093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104093 prefixEnd_3104093 := by exact prefixLift 3104093
  have htrace : WordTrace (prefixWord ++ tailWord_3104093) baseStart_3104093 baseEnd_3104093 := by
    simpa [prefixWord, tailWord_3104093, baseEnd_3104093] using wordTrace_append hprefix tailTrace_3104093
  have hstable : (prefixWord ++ tailWord_3104093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104093).length < 2 ^ (prefixWord ++ tailWord_3104093).sum := by decide
  have hdescent : baseEnd_3104093 < baseStart_3104093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104121 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 10]
def baseStart_3104121 : Nat := 118140960795 + 3104121 * 2 ^ 59
def prefixEnd_3104121 : Nat := 4983230072969 + 3 ^ 40 * 3104121 * 2
def baseEnd_3104121 : Nat := 177100675857239427334657

theorem tailTrace_3104121 : CollatzResearch.WordTrace tailWord_3104121 prefixEnd_3104121 177100675857239427334657 := by
  unfold tailWord_3104121
  simp only [CollatzResearch.WordTrace]
  refine ⟨113216593987307233505176217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75477729324871489003450811 113216593987307233505176217)
  ·
    refine ⟨84912445490480425128882163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113216593987307233505176217 84912445490480425128882163)
    ·
      refine ⟨127368668235720637693323245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84912445490480425128882163 127368668235720637693323245)
      ·
        refine ⟨47763250588395239134996217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127368668235720637693323245 47763250588395239134996217)
        ·
          refine ⟨35822437941296429351247163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47763250588395239134996217 35822437941296429351247163)
          ·
            refine ⟨53733656911944644026870745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35822437941296429351247163 53733656911944644026870745)
            ·
              refine ⟨40300242683958483020153059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53733656911944644026870745 40300242683958483020153059)
              ·
                refine ⟨60450364025937724530229589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40300242683958483020153059 60450364025937724530229589)
                ·
                  refine ⟨177100675857239427334657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 60450364025937724530229589 177100675857239427334657)
                  ·
                    rfl

theorem cell23_3104121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 10].length) (baseStart_3104121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104121 prefixEnd_3104121 := by exact prefixLift 3104121
  have htrace : WordTrace (prefixWord ++ tailWord_3104121) baseStart_3104121 baseEnd_3104121 := by
    simpa [prefixWord, tailWord_3104121, baseEnd_3104121] using wordTrace_append hprefix tailTrace_3104121
  have hstable : (prefixWord ++ tailWord_3104121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104121).length < 2 ^ (prefixWord ++ tailWord_3104121).sum := by decide
  have hdescent : baseEnd_3104121 < baseStart_3104121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104135 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_3104135 : Nat := 118140960795 + 3104135 * 2 ^ 59
def prefixEnd_3104135 : Nat := 4983230072969 + 3 ^ 40 * 3104135 * 2
def baseEnd_3104135 : Nat := 1593913271444317791236849

theorem tailTrace_3104135 : CollatzResearch.WordTrace tailWord_3104135 prefixEnd_3104135 1593913271444317791236849 := by
  unfold tailWord_3104135
  simp only [CollatzResearch.WordTrace]
  refine ⟨113217104609256513896185859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75478069739504342597457239 113217104609256513896185859)
  ·
    refine ⟨169825656913884770844278789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113217104609256513896185859 169825656913884770844278789)
    ·
      refine ⟨31842310671353394533302273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169825656913884770844278789 31842310671353394533302273)
      ·
        refine ⟨23881733003515045899976705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31842310671353394533302273 23881733003515045899976705)
        ·
          refine ⟨17911299752636284424982529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23881733003515045899976705 17911299752636284424982529)
          ·
            refine ⟨13433474814477213318736897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17911299752636284424982529 13433474814477213318736897)
            ·
              refine ⟨10075106110857909989052673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13433474814477213318736897 10075106110857909989052673)
              ·
                refine ⟨7556329583143432491789505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10075106110857909989052673 7556329583143432491789505)
                ·
                  refine ⟨5667247187357574368842129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7556329583143432491789505 5667247187357574368842129)
                  ·
                    refine ⟨4250435390518180776631597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5667247187357574368842129 4250435390518180776631597)
                    ·
                      refine ⟨1593913271444317791236849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4250435390518180776631597 1593913271444317791236849)
                      ·
                        rfl

theorem cell23_3104135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_3104135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104135 prefixEnd_3104135 := by exact prefixLift 3104135
  have htrace : WordTrace (prefixWord ++ tailWord_3104135) baseStart_3104135 baseEnd_3104135 := by
    simpa [prefixWord, tailWord_3104135, baseEnd_3104135] using wordTrace_append hprefix tailTrace_3104135
  have hstable : (prefixWord ++ tailWord_3104135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104135).length < 2 ^ (prefixWord ++ tailWord_3104135).sum := by decide
  have hdescent : baseEnd_3104135 < baseStart_3104135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104171 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 10]
def baseStart_3104171 : Nat := 118140960795 + 3104171 * 2 ^ 59
def prefixEnd_3104171 : Nat := 4983230072969 + 3 ^ 40 * 3104171 * 2
def baseEnd_3104171 : Nat := 1593931756747879650386683

theorem tailTrace_3104171 : CollatzResearch.WordTrace tailWord_3104171 prefixEnd_3104171 1593931756747879650386683 := by
  unfold tailWord_3104171
  simp only [CollatzResearch.WordTrace]
  refine ⟨113218417637126092044496367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75478945091417394696330911 113218417637126092044496367)
  ·
    refine ⟨169827626455689138066744551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113218417637126092044496367 169827626455689138066744551)
    ·
      refine ⟨254741439683533707100116827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169827626455689138066744551 254741439683533707100116827)
      ·
        refine ⟨382112159525300560650175241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254741439683533707100116827 382112159525300560650175241)
        ·
          refine ⟨286584119643975420487631431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382112159525300560650175241 286584119643975420487631431)
          ·
            refine ⟨429876179465963130731447147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286584119643975420487631431 429876179465963130731447147)
            ·
              refine ⟨644814269198944696097170721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429876179465963130731447147 644814269198944696097170721)
              ·
                refine ⟨483610701899208522072878041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644814269198944696097170721 483610701899208522072878041)
                ·
                  refine ⟨362708026424406391554658531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483610701899208522072878041 362708026424406391554658531)
                  ·
                    refine ⟨544062039636609587331987797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 362708026424406391554658531 544062039636609587331987797)
                    ·
                      refine ⟨1593931756747879650386683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 544062039636609587331987797 1593931756747879650386683)
                      ·
                        rfl

theorem cell23_3104171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_3104171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104171 prefixEnd_3104171 := by exact prefixLift 3104171
  have htrace : WordTrace (prefixWord ++ tailWord_3104171) baseStart_3104171 baseEnd_3104171 := by
    simpa [prefixWord, tailWord_3104171, baseEnd_3104171] using wordTrace_append hprefix tailTrace_3104171
  have hstable : (prefixWord ++ tailWord_3104171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104171).length < 2 ^ (prefixWord ++ tailWord_3104171).sum := by decide
  have hdescent : baseEnd_3104171 < baseStart_3104171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104208 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_3104208 : Nat := 118140960795 + 3104208 * 2 ^ 59
def prefixEnd_3104208 : Nat := 4983230072969 + 3 ^ 40 * 3104208 * 2
def baseEnd_3104208 : Nat := 1593950755532096005624013

theorem tailTrace_3104208 : CollatzResearch.WordTrace tailWord_3104208 prefixEnd_3104208 1593950755532096005624013 := by
  unfold tailWord_3104208
  simp only [CollatzResearch.WordTrace]
  refine ⟨56609883568996023681796639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75479844758661364909062185 56609883568996023681796639)
  ·
    refine ⟨84914825353494035522694959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56609883568996023681796639 84914825353494035522694959)
    ·
      refine ⟨127372238030241053284042439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84914825353494035522694959 127372238030241053284042439)
      ·
        refine ⟨191058357045361579926063659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127372238030241053284042439 191058357045361579926063659)
        ·
          refine ⟨286587535568042369889095489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191058357045361579926063659 286587535568042369889095489)
          ·
            refine ⟨214940651676031777416821617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286587535568042369889095489 214940651676031777416821617)
            ·
              refine ⟨161205488757023833062616213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214940651676031777416821617 161205488757023833062616213)
              ·
                refine ⟨7556507285485492174810135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161205488757023833062616213 7556507285485492174810135)
                ·
                  refine ⟨11334760928228238262215203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7556507285485492174810135 11334760928228238262215203)
                  ·
                    refine ⟨17002141392342357393322805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11334760928228238262215203 17002141392342357393322805)
                    ·
                      refine ⟨1593950755532096005624013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17002141392342357393322805 1593950755532096005624013)
                      ·
                        rfl

theorem cell23_3104208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_3104208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104208 prefixEnd_3104208 := by exact prefixLift 3104208
  have htrace : WordTrace (prefixWord ++ tailWord_3104208) baseStart_3104208 baseEnd_3104208 := by
    simpa [prefixWord, tailWord_3104208, baseEnd_3104208] using wordTrace_append hprefix tailTrace_3104208
  have hstable : (prefixWord ++ tailWord_3104208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104208).length < 2 ^ (prefixWord ++ tailWord_3104208).sum := by decide
  have hdescent : baseEnd_3104208 < baseStart_3104208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104215 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 2, 4]
def baseStart_3104215 : Nat := 118140960795 + 3104215 * 2 ^ 59
def prefixEnd_3104215 : Nat := 4983230072969 + 3 ^ 40 * 3104215 * 2
def baseEnd_3104215 : Nat := 531318116632225826078827

theorem tailTrace_3104215 : CollatzResearch.WordTrace tailWord_3104215 prefixEnd_3104215 531318116632225826078827 := by
  unfold tailWord_3104215
  simp only [CollatzResearch.WordTrace]
  refine ⟨113220022448966687559098099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75480014965977791706065399 113220022448966687559098099)
  ·
    refine ⟨169830033673450031338647149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113220022448966687559098099 169830033673450031338647149)
    ·
      refine ⟨63686262627543761751992681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169830033673450031338647149 63686262627543761751992681)
      ·
        refine ⟨47764696970657821313994511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63686262627543761751992681 47764696970657821313994511)
        ·
          refine ⟨71647045455986731970991767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47764696970657821313994511 71647045455986731970991767)
          ·
            refine ⟨107470568183980097956487651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71647045455986731970991767 107470568183980097956487651)
            ·
              refine ⟨161205852275970146934731477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107470568183980097956487651 161205852275970146934731477)
              ·
                refine ⟨3778262162718050318782769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161205852275970146934731477 3778262162718050318782769)
                ·
                  refine ⟨2833696622038537739087077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3778262162718050318782769 2833696622038537739087077)
                  ·
                    refine ⟨531318116632225826078827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833696622038537739087077 531318116632225826078827)
                    ·
                      rfl

theorem cell23_3104215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_3104215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104215 prefixEnd_3104215 := by exact prefixLift 3104215
  have htrace : WordTrace (prefixWord ++ tailWord_3104215) baseStart_3104215 baseEnd_3104215 := by
    simpa [prefixWord, tailWord_3104215, baseEnd_3104215] using wordTrace_append hprefix tailTrace_3104215
  have hstable : (prefixWord ++ tailWord_3104215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104215).length < 2 ^ (prefixWord ++ tailWord_3104215).sum := by decide
  have hdescent : baseEnd_3104215 < baseStart_3104215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104242 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3104242 : Nat := 118140960795 + 3104242 * 2 ^ 59
def prefixEnd_3104242 : Nat := 4983230072969 + 3 ^ 40 * 3104242 * 2
def baseEnd_3104242 : Nat := 1593968213874348872598857

theorem tailTrace_3104242 : CollatzResearch.WordTrace tailWord_3104242 prefixEnd_3104242 1593968213874348872598857 := by
  unfold tailWord_3104242
  simp only [CollatzResearch.WordTrace]
  refine ⟨28305251804967217792582745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75480671479912580780220653 28305251804967217792582745)
  ·
    refine ⟨21228938853725413344437059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28305251804967217792582745 21228938853725413344437059)
    ·
      refine ⟨31843408280588120016655589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21228938853725413344437059 31843408280588120016655589)
      ·
        refine ⟨5970639052610272503122923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31843408280588120016655589 5970639052610272503122923)
        ·
          refine ⟨8955958578915408754684385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970639052610272503122923 8955958578915408754684385)
          ·
            refine ⟨6716968934186556566013289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8955958578915408754684385 6716968934186556566013289)
            ·
              refine ⟨5037726700639917424509967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6716968934186556566013289 5037726700639917424509967)
              ·
                refine ⟨7556590050959876136764951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5037726700639917424509967 7556590050959876136764951)
                ·
                  refine ⟨11334885076439814205147427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7556590050959876136764951 11334885076439814205147427)
                  ·
                    refine ⟨17002327614659721307721141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11334885076439814205147427 17002327614659721307721141)
                    ·
                      refine ⟨1593968213874348872598857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17002327614659721307721141 1593968213874348872598857)
                      ·
                        rfl

theorem cell23_3104242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3104242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104242 prefixEnd_3104242 := by exact prefixLift 3104242
  have htrace : WordTrace (prefixWord ++ tailWord_3104242) baseStart_3104242 baseEnd_3104242 := by
    simpa [prefixWord, tailWord_3104242, baseEnd_3104242] using wordTrace_append hprefix tailTrace_3104242
  have hstable : (prefixWord ++ tailWord_3104242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104242).length < 2 ^ (prefixWord ++ tailWord_3104242).sum := by decide
  have hdescent : baseEnd_3104242 < baseStart_3104242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104245 : List Nat := [1, 3, 5, 1, 1, 1, 11]
def baseStart_3104245 : Nat := 118140960795 + 3104245 * 2 ^ 59
def prefixEnd_3104245 : Nat := 4983230072969 + 3 ^ 40 * 3104245 * 2
def baseEnd_3104245 : Nat := 19678638942176695813103

theorem tailTrace_3104245 : CollatzResearch.WordTrace tailWord_3104245 prefixEnd_3104245 19678638942176695813103 := by
  unfold tailWord_3104245
  simp only [CollatzResearch.WordTrace]
  refine ⟨113221116638858002682690189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75480744425905335121793459 113221116638858002682690189)
  ·
    refine ⟨42457918739571751006008821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113221116638858002682690189 42457918739571751006008821)
    ·
      refine ⟨3980429881834851656813327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42457918739571751006008821 3980429881834851656813327)
      ·
        refine ⟨5970644822752277485219991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980429881834851656813327 5970644822752277485219991)
        ·
          refine ⟨8955967234128416227829987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970644822752277485219991 8955967234128416227829987)
          ·
            refine ⟨13433950851192624341744981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8955967234128416227829987 13433950851192624341744981)
            ·
              refine ⟨19678638942176695813103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13433950851192624341744981 19678638942176695813103)
              ·
                rfl

theorem cell23_3104245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 11].length) (baseStart_3104245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104245 prefixEnd_3104245 := by exact prefixLift 3104245
  have htrace : WordTrace (prefixWord ++ tailWord_3104245) baseStart_3104245 baseEnd_3104245 := by
    simpa [prefixWord, tailWord_3104245, baseEnd_3104245] using wordTrace_append hprefix tailTrace_3104245
  have hstable : (prefixWord ++ tailWord_3104245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104245).length < 2 ^ (prefixWord ++ tailWord_3104245).sum := by decide
  have hdescent : baseEnd_3104245 < baseStart_3104245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104325 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_3104325 : Nat := 118140960795 + 3104325 * 2 ^ 59
def prefixEnd_3104325 : Nat := 4983230072969 + 3 ^ 40 * 3104325 * 2
def baseEnd_3104325 : Nat := 1594010832768672047860975

theorem tailTrace_3104325 : CollatzResearch.WordTrace tailWord_3104325 prefixEnd_3104325 1594010832768672047860975 := by
  unfold tailWord_3104325
  simp only [CollatzResearch.WordTrace]
  refine ⟨113224034478568176345602429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75482689652378784230401619 113224034478568176345602429)
  ·
    refine ⟨42459012929463066129600911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113224034478568176345602429 42459012929463066129600911)
    ·
      refine ⟨63688519394194599194401367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42459012929463066129600911 63688519394194599194401367)
      ·
        refine ⟨95532779091291898791602051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63688519394194599194401367 95532779091291898791602051)
        ·
          refine ⟨143299168636937848187403077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95532779091291898791602051 143299168636937848187403077)
          ·
            refine ⟨26868594119425846535138077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143299168636937848187403077 26868594119425846535138077)
            ·
              refine ⟨10075722794784692450676779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26868594119425846535138077 10075722794784692450676779)
              ·
                refine ⟨15113584192177038676015169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10075722794784692450676779 15113584192177038676015169)
                ·
                  refine ⟨11335188144132779007011377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15113584192177038676015169 11335188144132779007011377)
                  ·
                    refine ⟨8501391108099584255258533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11335188144132779007011377 8501391108099584255258533)
                    ·
                      refine ⟨1594010832768672047860975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8501391108099584255258533 1594010832768672047860975)
                      ·
                        rfl

theorem cell23_3104325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_3104325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104325 prefixEnd_3104325 := by exact prefixLift 3104325
  have htrace : WordTrace (prefixWord ++ tailWord_3104325) baseStart_3104325 baseEnd_3104325 := by
    simpa [prefixWord, tailWord_3104325, baseEnd_3104325] using wordTrace_append hprefix tailTrace_3104325
  have hstable : (prefixWord ++ tailWord_3104325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104325).length < 2 ^ (prefixWord ++ tailWord_3104325).sum := by decide
  have hdescent : baseEnd_3104325 < baseStart_3104325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104362 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3104362 : Nat := 118140960795 + 3104362 * 2 ^ 59
def prefixEnd_3104362 : Nat := 4983230072969 + 3 ^ 40 * 3104362 * 2
def baseEnd_3104362 : Nat := 1594029831552888403098305

theorem tailTrace_3104362 : CollatzResearch.WordTrace tailWord_3104362 prefixEnd_3104362 1594029831552888403098305 := by
  unfold tailWord_3104362
  simp only [CollatzResearch.WordTrace]
  refine ⟨28306345994858532916174835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75483589319622754443132893 28306345994858532916174835)
  ·
    refine ⟨42459518992287799374262253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28306345994858532916174835 42459518992287799374262253)
    ·
      refine ⟨15922319622107924765348345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42459518992287799374262253 15922319622107924765348345)
      ·
        refine ⟨11941739716580943574011259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15922319622107924765348345 11941739716580943574011259)
        ·
          refine ⟨17912609574871415361016889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11941739716580943574011259 17912609574871415361016889)
          ·
            refine ⟨13434457181153561520762667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17912609574871415361016889 13434457181153561520762667)
            ·
              refine ⟨20151685771730342281144001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13434457181153561520762667 20151685771730342281144001)
              ·
                refine ⟨15113764328797756710858001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20151685771730342281144001 15113764328797756710858001)
                ·
                  refine ⟨11335323246598317533143501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15113764328797756710858001 11335323246598317533143501)
                  ·
                    refine ⟨4250746217474369074928813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11335323246598317533143501 4250746217474369074928813)
                    ·
                      refine ⟨1594029831552888403098305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4250746217474369074928813 1594029831552888403098305)
                      ·
                        rfl

theorem cell23_3104362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3104362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104362 prefixEnd_3104362 := by exact prefixLift 3104362
  have htrace : WordTrace (prefixWord ++ tailWord_3104362) baseStart_3104362 baseEnd_3104362 := by
    simpa [prefixWord, tailWord_3104362, baseEnd_3104362] using wordTrace_append hprefix tailTrace_3104362
  have hstable : (prefixWord ++ tailWord_3104362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104362).length < 2 ^ (prefixWord ++ tailWord_3104362).sum := by decide
  have hdescent : baseEnd_3104362 < baseStart_3104362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104442 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 6]
def baseStart_3104442 : Nat := 118140960795 + 3104442 * 2 ^ 59
def prefixEnd_3104442 : Nat := 4983230072969 + 3 ^ 40 * 3104442 * 2
def baseEnd_3104442 : Nat := 177118990000583121121993

theorem tailTrace_3104442 : CollatzResearch.WordTrace tailWord_3104442 prefixEnd_3104442 177118990000583121121993 := by
  unfold tailWord_3104442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28307075454786076331902895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75485534546096203551741053 28307075454786076331902895)
  ·
    refine ⟨42460613182179114497854343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28307075454786076331902895 42460613182179114497854343)
    ·
      refine ⟨63690919773268671746781515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42460613182179114497854343 63690919773268671746781515)
      ·
        refine ⟨95536379659903007620172273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63690919773268671746781515 95536379659903007620172273)
        ·
          refine ⟨71652284744927255715129205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95536379659903007620172273 71652284744927255715129205)
          ·
            refine ⟨6717401694836930223293363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71652284744927255715129205 6717401694836930223293363)
            ·
              refine ⟨10076102542255395334940045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717401694836930223293363 10076102542255395334940045)
              ·
                refine ⟨3778538453345773250602517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10076102542255395334940045 3778538453345773250602517)
                ·
                  refine ⟨177118990000583121121993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3778538453345773250602517 177118990000583121121993)
                  ·
                    rfl

theorem cell23_3104442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_3104442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104442 prefixEnd_3104442 := by exact prefixLift 3104442
  have htrace : WordTrace (prefixWord ++ tailWord_3104442) baseStart_3104442 baseEnd_3104442 := by
    simpa [prefixWord, tailWord_3104442, baseEnd_3104442] using wordTrace_append hprefix tailTrace_3104442
  have hstable : (prefixWord ++ tailWord_3104442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104442).length < 2 ^ (prefixWord ++ tailWord_3104442).sum := by decide
  have hdescent : baseEnd_3104442 < baseStart_3104442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104476 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 6]
def baseStart_3104476 : Nat := 118140960795 + 3104476 * 2 ^ 59
def prefixEnd_3104476 : Nat := 4983230072969 + 3 ^ 40 * 3104476 * 2
def baseEnd_3104476 : Nat := 177120929816388995230309

theorem tailTrace_3104476 : CollatzResearch.WordTrace tailWord_3104476 prefixEnd_3104476 177120929816388995230309 := by
  unfold tailWord_3104476
  simp only [CollatzResearch.WordTrace]
  refine ⟨56614770950510564567174641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75486361267347419422899521 56614770950510564567174641)
  ·
    refine ⟨42461078212882923425380981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56614770950510564567174641 42461078212882923425380981)
    ·
      refine ⟨3980726082457774071129467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42461078212882923425380981 3980726082457774071129467)
      ·
        refine ⟨5971089123686661106694201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980726082457774071129467 5971089123686661106694201)
        ·
          refine ⟨4478316842764995830020651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5971089123686661106694201 4478316842764995830020651)
          ·
            refine ⟨6717475264147493745030977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478316842764995830020651 6717475264147493745030977)
            ·
              refine ⟨5038106448110620308773233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6717475264147493745030977 5038106448110620308773233)
              ·
                refine ⟨3778579836082965231579925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5038106448110620308773233 3778579836082965231579925)
                ·
                  refine ⟨177120929816388995230309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3778579836082965231579925 177120929816388995230309)
                  ·
                    rfl

theorem cell23_3104476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_3104476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104476 prefixEnd_3104476 := by exact prefixLift 3104476
  have htrace : WordTrace (prefixWord ++ tailWord_3104476) baseStart_3104476 baseEnd_3104476 := by
    simpa [prefixWord, tailWord_3104476, baseEnd_3104476] using wordTrace_append hprefix tailTrace_3104476
  have hstable : (prefixWord ++ tailWord_3104476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104476).length < 2 ^ (prefixWord ++ tailWord_3104476).sum := by decide
  have hdescent : baseEnd_3104476 < baseStart_3104476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104479 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 2, 3, 2]
def baseStart_3104479 : Nat := 118140960795 + 3104479 * 2 ^ 59
def prefixEnd_3104479 : Nat := 4983230072969 + 3 ^ 40 * 3104479 * 2
def baseEnd_3104479 : Nat := 1594089908789464445335267

theorem tailTrace_3104479 : CollatzResearch.WordTrace tailWord_3104479 prefixEnd_3104479 1594089908789464445335267 := by
  unfold tailWord_3104479
  simp only [CollatzResearch.WordTrace]
  refine ⟨113229651320010260646708491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75486434213340173764472327 113229651320010260646708491)
  ·
    refine ⟨169844476980015390970062737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113229651320010260646708491 169844476980015390970062737)
    ·
      refine ⟨127383357735011543227547053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169844476980015390970062737 127383357735011543227547053)
      ·
        refine ⟨47768759150629328710330145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127383357735011543227547053 47768759150629328710330145)
        ·
          refine ⟨35826569362971996532747609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47768759150629328710330145 35826569362971996532747609)
          ·
            refine ⟨26869927022228997399560707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35826569362971996532747609 26869927022228997399560707)
            ·
              refine ⟨40304890533343496099341061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26869927022228997399560707 40304890533343496099341061)
              ·
                refine ⟨7557166975001905518626449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40304890533343496099341061 7557166975001905518626449)
                ·
                  refine ⟨5667875231251429138969837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7557166975001905518626449 5667875231251429138969837)
                  ·
                    refine ⟨2125453211719285927113689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5667875231251429138969837 2125453211719285927113689)
                    ·
                      refine ⟨1594089908789464445335267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125453211719285927113689 1594089908789464445335267)
                      ·
                        rfl

theorem cell23_3104479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_3104479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104479 prefixEnd_3104479 := by exact prefixLift 3104479
  have htrace : WordTrace (prefixWord ++ tailWord_3104479) baseStart_3104479 baseEnd_3104479 := by
    simpa [prefixWord, tailWord_3104479, baseEnd_3104479] using wordTrace_append hprefix tailTrace_3104479
  have hstable : (prefixWord ++ tailWord_3104479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104479).length < 2 ^ (prefixWord ++ tailWord_3104479).sum := by decide
  have hdescent : baseEnd_3104479 < baseStart_3104479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104492 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_3104492 : Nat := 118140960795 + 3104492 * 2 ^ 59
def prefixEnd_3104492 : Nat := 4983230072969 + 3 ^ 40 * 3104492 * 2
def baseEnd_3104492 : Nat := 1594096584037972894472707

theorem tailTrace_3104492 : CollatzResearch.WordTrace tailWord_3104492 prefixEnd_3104492 1594096584037972894472707 := by
  unfold tailWord_3104492
  simp only [CollatzResearch.WordTrace]
  refine ⟨56615062734481581933465865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75486750312642109244621153 56615062734481581933465865)
  ·
    refine ⟨42461297050861186450099399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56615062734481581933465865 42461297050861186450099399)
    ·
      refine ⟨63691945576291779675149099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42461297050861186450099399 63691945576291779675149099)
      ·
        refine ⟨95537918364437669512723649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63691945576291779675149099 95537918364437669512723649)
        ·
          refine ⟨71653438773328252134542737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95537918364437669512723649 71653438773328252134542737)
          ·
            refine ⟨53740079079996189100907053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71653438773328252134542737 53740079079996189100907053)
            ·
              refine ⟨20152529654998570912840145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53740079079996189100907053 20152529654998570912840145)
              ·
                refine ⟨15114397241248928184630109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20152529654998570912840145 15114397241248928184630109)
                ·
                  refine ⟨5667898965468348069236291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15114397241248928184630109 5667898965468348069236291)
                  ·
                    refine ⟨8501848448202522103854437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5667898965468348069236291 8501848448202522103854437)
                    ·
                      refine ⟨1594096584037972894472707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8501848448202522103854437 1594096584037972894472707)
                      ·
                        rfl

theorem cell23_3104492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_3104492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104492 prefixEnd_3104492 := by exact prefixLift 3104492
  have htrace : WordTrace (prefixWord ++ tailWord_3104492) baseStart_3104492 baseEnd_3104492 := by
    simpa [prefixWord, tailWord_3104492, baseEnd_3104492] using wordTrace_append hprefix tailTrace_3104492
  have hstable : (prefixWord ++ tailWord_3104492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104492).length < 2 ^ (prefixWord ++ tailWord_3104492).sum := by decide
  have hdescent : baseEnd_3104492 < baseStart_3104492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104515 : List Nat := [1, 1, 1, 3, 2, 2, 2, 11]
def baseStart_3104515 : Nat := 118140960795 + 3104515 * 2 ^ 59
def prefixEnd_3104515 : Nat := 4983230072969 + 3 ^ 40 * 3104515 * 2
def baseEnd_3104515 : Nat := 59041051633075048314263

theorem tailTrace_3104515 : CollatzResearch.WordTrace tailWord_3104515 prefixEnd_3104515 59041051633075048314263 := by
  unfold tailWord_3104515
  simp only [CollatzResearch.WordTrace]
  refine ⟨113230964347879838795018999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75487309565253225863345999 113230964347879838795018999)
  ·
    refine ⟨169846446521819758192528499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113230964347879838795018999 169846446521819758192528499)
    ·
      refine ⟨254769669782729637288792749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169846446521819758192528499 254769669782729637288792749)
      ·
        refine ⟨95538626168523613983297281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254769669782729637288792749 95538626168523613983297281)
        ·
          refine ⟨71653969626392710487472961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95538626168523613983297281 71653969626392710487472961)
          ·
            refine ⟨53740477219794532865604721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71653969626392710487472961 53740477219794532865604721)
            ·
              refine ⟨40305357914845899649203541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53740477219794532865604721 40305357914845899649203541)
              ·
                refine ⟨59041051633075048314263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 40305357914845899649203541 59041051633075048314263)
                ·
                  rfl

theorem cell23_3104515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 11].length) (baseStart_3104515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104515 prefixEnd_3104515 := by exact prefixLift 3104515
  have htrace : WordTrace (prefixWord ++ tailWord_3104515) baseStart_3104515 baseEnd_3104515 := by
    simpa [prefixWord, tailWord_3104515, baseEnd_3104515] using wordTrace_append hprefix tailTrace_3104515
  have hstable : (prefixWord ++ tailWord_3104515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104515).length < 2 ^ (prefixWord ++ tailWord_3104515).sum := by decide
  have hdescent : baseEnd_3104515 < baseStart_3104515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104526 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_3104526 : Nat := 118140960795 + 3104526 * 2 ^ 59
def prefixEnd_3104526 : Nat := 4983230072969 + 3 ^ 40 * 3104526 * 2
def baseEnd_3104526 : Nat := 1594114042380225761447551

theorem tailTrace_3104526 : CollatzResearch.WordTrace tailWord_3104526 prefixEnd_3104526 1594114042380225761447551 := by
  unfold tailWord_3104526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14153920693854998459208679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75487577033893325115779621 14153920693854998459208679)
  ·
    refine ⟨21230881040782497688813019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14153920693854998459208679 21230881040782497688813019)
    ·
      refine ⟨31846321561173746533219529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21230881040782497688813019 31846321561173746533219529)
      ·
        refine ⟨23884741170880309899914647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31846321561173746533219529 23884741170880309899914647)
        ·
          refine ⟨35827111756320464849871971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23884741170880309899914647 35827111756320464849871971)
          ·
            refine ⟨53740667634480697274807957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35827111756320464849871971 53740667634480697274807957)
            ·
              refine ⟨2519093795366282684756623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53740667634480697274807957 2519093795366282684756623)
              ·
                refine ⟨3778640693049424027134935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2519093795366282684756623 3778640693049424027134935)
                ·
                  refine ⟨5667961039574136040702403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3778640693049424027134935 5667961039574136040702403)
                  ·
                    refine ⟨8501941559361204061053605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5667961039574136040702403 8501941559361204061053605)
                    ·
                      refine ⟨1594114042380225761447551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8501941559361204061053605 1594114042380225761447551)
                      ·
                        rfl

theorem cell23_3104526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_3104526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104526 prefixEnd_3104526 := by exact prefixLift 3104526
  have htrace : WordTrace (prefixWord ++ tailWord_3104526) baseStart_3104526 baseEnd_3104526 := by
    simpa [prefixWord, tailWord_3104526, baseEnd_3104526] using wordTrace_append hprefix tailTrace_3104526
  have hstable : (prefixWord ++ tailWord_3104526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104526).length < 2 ^ (prefixWord ++ tailWord_3104526).sum := by decide
  have hdescent : baseEnd_3104526 < baseStart_3104526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104543 : List Nat := [1, 1, 2, 4, 2, 1, 1, 6, 1, 2, 2]
def baseStart_3104543 : Nat := 118140960795 + 3104543 * 2 ^ 59
def prefixEnd_3104543 : Nat := 4983230072969 + 3 ^ 40 * 3104543 * 2
def baseEnd_3104543 : Nat := 1594122771551352194934973

theorem tailTrace_3104543 : CollatzResearch.WordTrace tailWord_3104543 prefixEnd_3104543 1594122771551352194934973 := by
  unfold tailWord_3104543
  simp only [CollatzResearch.WordTrace]
  refine ⟨113231985591778399577038283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75487990394518933051358855 113231985591778399577038283)
  ·
    refine ⟨169847978387667599365557425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113231985591778399577038283 169847978387667599365557425)
    ·
      refine ⟨127385983790750699524168069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169847978387667599365557425 127385983790750699524168069)
      ·
        refine ⟨23884871960765756160781513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127385983790750699524168069 23884871960765756160781513)
        ·
          refine ⟨17913653970574317120586135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23884871960765756160781513 17913653970574317120586135)
          ·
            refine ⟨26870480955861475680879203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17913653970574317120586135 26870480955861475680879203)
            ·
              refine ⟨40305721433792213521318805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26870480955861475680879203 40305721433792213521318805)
              ·
                refine ⟨1889330692209010008811819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40305721433792213521318805 1889330692209010008811819)
                ·
                  refine ⟨2833996038313515013217729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889330692209010008811819 2833996038313515013217729)
                  ·
                    refine ⟨2125497028735136259913297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2833996038313515013217729 2125497028735136259913297)
                    ·
                      refine ⟨1594122771551352194934973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125497028735136259913297 1594122771551352194934973)
                      ·
                        rfl

theorem cell23_3104543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_3104543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104543 prefixEnd_3104543 := by exact prefixLift 3104543
  have htrace : WordTrace (prefixWord ++ tailWord_3104543) baseStart_3104543 baseEnd_3104543 := by
    simpa [prefixWord, tailWord_3104543, baseEnd_3104543] using wordTrace_append hprefix tailTrace_3104543
  have hstable : (prefixWord ++ tailWord_3104543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104543).length < 2 ^ (prefixWord ++ tailWord_3104543).sum := by decide
  have hdescent : baseEnd_3104543 < baseStart_3104543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104566 : List Nat := [5, 1, 2, 2, 1, 1, 4, 7]
def baseStart_3104566 : Nat := 118140960795 + 3104566 * 2 ^ 59
def prefixEnd_3104566 : Nat := 4983230072969 + 3 ^ 40 * 3104566 * 2
def baseEnd_3104566 : Nat := 59042021540977985368421

theorem tailTrace_3104566 : CollatzResearch.WordTrace tailWord_3104566 prefixEnd_3104566 59042021540977985368421 := by
  unfold tailWord_3104566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7077051529418442156570347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75488549647130049670083701 7077051529418442156570347)
  ·
    refine ⟨10615577294127663234855521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7077051529418442156570347 10615577294127663234855521)
    ·
      refine ⟨7961682970595747426141641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10615577294127663234855521 7961682970595747426141641)
      ·
        refine ⟨5971262227946810569606231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7961682970595747426141641 5971262227946810569606231)
        ·
          refine ⟨8956893341920215854409347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5971262227946810569606231 8956893341920215854409347)
          ·
            refine ⟨13435340012880323781614021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8956893341920215854409347 13435340012880323781614021)
            ·
              refine ⟨2519126252415060709052629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13435340012880323781614021 2519126252415060709052629)
              ·
                refine ⟨59042021540977985368421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2519126252415060709052629 59042021540977985368421)
                ·
                  rfl

theorem cell23_3104566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_3104566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104566 prefixEnd_3104566 := by exact prefixLift 3104566
  have htrace : WordTrace (prefixWord ++ tailWord_3104566) baseStart_3104566 baseEnd_3104566 := by
    simpa [prefixWord, tailWord_3104566, baseEnd_3104566] using wordTrace_append hprefix tailTrace_3104566
  have hstable : (prefixWord ++ tailWord_3104566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104566).length < 2 ^ (prefixWord ++ tailWord_3104566).sum := by decide
  have hdescent : baseEnd_3104566 < baseStart_3104566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104572 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_3104572 : Nat := 118140960795 + 3104572 * 2 ^ 59
def prefixEnd_3104572 : Nat := 4983230072969 + 3 ^ 40 * 3104572 * 2
def baseEnd_3104572 : Nat := 1594137662490332581472339

theorem tailTrace_3104572 : CollatzResearch.WordTrace tailWord_3104572 prefixEnd_3104572 1594137662490332581472339 := by
  unfold tailWord_3104572
  simp only [CollatzResearch.WordTrace]
  refine ⟨56616521654336668764921985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75488695539115558353229313 56616521654336668764921985)
  ·
    refine ⟨42462391240752501573691489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56616521654336668764921985 42462391240752501573691489)
    ·
      refine ⟨31846793430564376180268617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42462391240752501573691489 31846793430564376180268617)
      ·
        refine ⟨23885095072923282135201463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31846793430564376180268617 23885095072923282135201463)
        ·
          refine ⟨35827642609384923202802195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23885095072923282135201463 35827642609384923202802195)
          ·
            refine ⟨53741463914077384804203293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35827642609384923202802195 53741463914077384804203293)
            ·
              refine ⟨20153048967779019301576235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53741463914077384804203293 20153048967779019301576235)
              ·
                refine ⟨30229573451668528952364353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20153048967779019301576235 30229573451668528952364353)
                ·
                  refine ⟨22672180088751396714273265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30229573451668528952364353 22672180088751396714273265)
                  ·
                    refine ⟨17004135066563547535704949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22672180088751396714273265 17004135066563547535704949)
                    ·
                      refine ⟨1594137662490332581472339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17004135066563547535704949 1594137662490332581472339)
                      ·
                        rfl

theorem cell23_3104572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_3104572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104572 prefixEnd_3104572 := by exact prefixLift 3104572
  have htrace : WordTrace (prefixWord ++ tailWord_3104572) baseStart_3104572 baseEnd_3104572 := by
    simpa [prefixWord, tailWord_3104572, baseEnd_3104572] using wordTrace_append hprefix tailTrace_3104572
  have hstable : (prefixWord ++ tailWord_3104572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104572).length < 2 ^ (prefixWord ++ tailWord_3104572).sum := by decide
  have hdescent : baseEnd_3104572 < baseStart_3104572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104586 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_3104586 : Nat := 118140960795 + 3104586 * 2 ^ 59
def prefixEnd_3104586 : Nat := 4983230072969 + 3 ^ 40 * 3104586 * 2
def baseEnd_3104586 : Nat := 1594144851219495526697275

theorem tailTrace_3104586 : CollatzResearch.WordTrace tailWord_3104586 prefixEnd_3104586 1594144851219495526697275 := by
  unfold tailWord_3104586
  simp only [CollatzResearch.WordTrace]
  refine ⟨28308388482655654480213403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75489035953748411947235741 28308388482655654480213403)
  ·
    refine ⟨42462582723983481720320105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28308388482655654480213403 42462582723983481720320105)
    ·
      refine ⟨31846937042987611290240079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42462582723983481720320105 31846937042987611290240079)
      ·
        refine ⟨47770405564481416935360119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31846937042987611290240079 47770405564481416935360119)
        ·
          refine ⟨71655608346722125403040179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47770405564481416935360119 71655608346722125403040179)
          ·
            refine ⟨107483412520083188104560269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71655608346722125403040179 107483412520083188104560269)
            ·
              refine ⟨40306279695031195539210101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107483412520083188104560269 40306279695031195539210101)
              ·
                refine ⟨3778713721409174581800947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40306279695031195539210101 3778713721409174581800947)
                ·
                  refine ⟨5668070582113761872701421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3778713721409174581800947 5668070582113761872701421)
                  ·
                    refine ⟨2125526468292660702263033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5668070582113761872701421 2125526468292660702263033)
                    ·
                      refine ⟨1594144851219495526697275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125526468292660702263033 1594144851219495526697275)
                      ·
                        rfl

theorem cell23_3104586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_3104586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104586 prefixEnd_3104586 := by exact prefixLift 3104586
  have htrace : WordTrace (prefixWord ++ tailWord_3104586) baseStart_3104586 baseEnd_3104586 := by
    simpa [prefixWord, tailWord_3104586, baseEnd_3104586] using wordTrace_append hprefix tailTrace_3104586
  have hstable : (prefixWord ++ tailWord_3104586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104586).length < 2 ^ (prefixWord ++ tailWord_3104586).sum := by decide
  have hdescent : baseEnd_3104586 < baseStart_3104586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104602 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_3104602 : Nat := 118140960795 + 3104602 * 2 ^ 59
def prefixEnd_3104602 : Nat := 4983230072969 + 3 ^ 40 * 3104602 * 2
def baseEnd_3104602 : Nat := 1594153066909967464097201

theorem tailTrace_3104602 : CollatzResearch.WordTrace tailWord_3104602 prefixEnd_3104602 1594153066909967464097201 := by
  unfold tailWord_3104602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28308534374641163163359015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75489424999043101768957373 28308534374641163163359015)
  ·
    refine ⟨42462801561961744745038523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28308534374641163163359015 42462801561961744745038523)
    ·
      refine ⟨63694202342942617117557785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42462801561961744745038523 63694202342942617117557785)
      ·
        refine ⟨47770651757206962838168339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63694202342942617117557785 47770651757206962838168339)
        ·
          refine ⟨71655977635810444257252509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47770651757206962838168339 71655977635810444257252509)
          ·
            refine ⟨26870991613428916596469691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71655977635810444257252509 26870991613428916596469691)
            ·
              refine ⟨40306487420143374894704537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26870991613428916596469691 40306487420143374894704537)
              ·
                refine ⟨30229865565107531171028403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40306487420143374894704537 30229865565107531171028403)
                ·
                  refine ⟨45344798347661296756542605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30229865565107531171028403 45344798347661296756542605)
                  ·
                    refine ⟨17004299380372986283703477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45344798347661296756542605 17004299380372986283703477)
                    ·
                      refine ⟨1594153066909967464097201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17004299380372986283703477 1594153066909967464097201)
                      ·
                        rfl

theorem cell23_3104602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_3104602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104602 prefixEnd_3104602 := by exact prefixLift 3104602
  have htrace : WordTrace (prefixWord ++ tailWord_3104602) baseStart_3104602 baseEnd_3104602 := by
    simpa [prefixWord, tailWord_3104602, baseEnd_3104602] using wordTrace_append hprefix tailTrace_3104602
  have hstable : (prefixWord ++ tailWord_3104602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104602).length < 2 ^ (prefixWord ++ tailWord_3104602).sum := by decide
  have hdescent : baseEnd_3104602 < baseStart_3104602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104610 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_3104610 : Nat := 118140960795 + 3104610 * 2 ^ 59
def prefixEnd_3104610 : Nat := 4983230072969 + 3 ^ 40 * 3104610 * 2
def baseEnd_3104610 : Nat := 1594157174755203432797165

theorem tailTrace_3104610 : CollatzResearch.WordTrace tailWord_3104610 prefixEnd_3104610 1594157174755203432797165 := by
  unfold tailWord_3104610
  simp only [CollatzResearch.WordTrace]
  refine ⟨28308607320633917504931821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75489619521690446679818189 28308607320633917504931821)
  ·
    refine ⟨10615727745237719064349433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28308607320633917504931821 10615727745237719064349433)
    ·
      refine ⟨7961795808928289298262075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10615727745237719064349433 7961795808928289298262075)
      ·
        refine ⟨11942693713392433947393113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7961795808928289298262075 11942693713392433947393113)
        ·
          refine ⟨8957020285044325460544835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11942693713392433947393113 8957020285044325460544835)
          ·
            refine ⟨13435530427566488190817253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8957020285044325460544835 13435530427566488190817253)
            ·
              refine ⟨2519161955168716535778235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13435530427566488190817253 2519161955168716535778235)
              ·
                refine ⟨3778742932753074803667353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2519161955168716535778235 3778742932753074803667353)
                ·
                  refine ⟨2834057199564806102750515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3778742932753074803667353 2834057199564806102750515)
                  ·
                    refine ⟨4251085799347209154125773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834057199564806102750515 4251085799347209154125773)
                    ·
                      refine ⟨1594157174755203432797165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4251085799347209154125773 1594157174755203432797165)
                      ·
                        rfl

theorem cell23_3104610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_3104610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104610 prefixEnd_3104610 := by exact prefixLift 3104610
  have htrace : WordTrace (prefixWord ++ tailWord_3104610) baseStart_3104610 baseEnd_3104610 := by
    simpa [prefixWord, tailWord_3104610, baseEnd_3104610] using wordTrace_append hprefix tailTrace_3104610
  have hstable : (prefixWord ++ tailWord_3104610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104610).length < 2 ^ (prefixWord ++ tailWord_3104610).sum := by decide
  have hdescent : baseEnd_3104610 < baseStart_3104610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104616 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_3104616 : Nat := 118140960795 + 3104616 * 2 ^ 59
def prefixEnd_3104616 : Nat := 4983230072969 + 3 ^ 40 * 3104616 * 2
def baseEnd_3104616 : Nat := 1594160255639130409322137

theorem tailTrace_3104616 : CollatzResearch.WordTrace tailWord_3104616 prefixEnd_3104616 1594160255639130409322137 := by
  unfold tailWord_3104616
  simp only [CollatzResearch.WordTrace]
  refine ⟨56617324060256966522222851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75489765413675955362963801 56617324060256966522222851)
  ·
    refine ⟨84925986090385449783334277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56617324060256966522222851 84925986090385449783334277)
    ·
      refine ⟨15923622391947271834375177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84925986090385449783334277 15923622391947271834375177)
      ·
        refine ⟨11942716793960453875781383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15923622391947271834375177 11942716793960453875781383)
        ·
          refine ⟨17914075190940680813672075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11942716793960453875781383 17914075190940680813672075)
          ·
            refine ⟨26871112786411021220508113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17914075190940680813672075 26871112786411021220508113)
            ·
              refine ⟨20153334589808265915381085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26871112786411021220508113 20153334589808265915381085)
              ·
                refine ⟨7557500471178099718267907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20153334589808265915381085 7557500471178099718267907)
                ·
                  refine ⟨11336250706767149577401861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7557500471178099718267907 11336250706767149577401861)
                  ·
                    refine ⟨2125547007518840545762849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11336250706767149577401861 2125547007518840545762849)
                    ·
                      refine ⟨1594160255639130409322137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125547007518840545762849 1594160255639130409322137)
                      ·
                        rfl

theorem cell23_3104616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_3104616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104616 prefixEnd_3104616 := by exact prefixLift 3104616
  have htrace : WordTrace (prefixWord ++ tailWord_3104616) baseStart_3104616 baseEnd_3104616 := by
    simpa [prefixWord, tailWord_3104616, baseEnd_3104616] using wordTrace_append hprefix tailTrace_3104616
  have hstable : (prefixWord ++ tailWord_3104616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104616).length < 2 ^ (prefixWord ++ tailWord_3104616).sum := by decide
  have hdescent : baseEnd_3104616 < baseStart_3104616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104639 : List Nat := [1, 1, 2, 2, 1, 1, 3, 7, 5]
def baseStart_3104639 : Nat := 118140960795 + 3104639 * 2 ^ 59
def prefixEnd_3104639 : Nat := 4983230072969 + 3 ^ 40 * 3104639 * 2
def baseEnd_3104639 : Nat := 177130229521575979926059

theorem tailTrace_3104639 : CollatzResearch.WordTrace tailWord_3104639 prefixEnd_3104639 177130229521575979926059 := by
  unfold tailWord_3104639
  simp only [CollatzResearch.WordTrace]
  refine ⟨113235486999430607972532971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75490324666287071981688647 113235486999430607972532971)
  ·
    refine ⟨169853230499145911958799457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113235486999430607972532971 169853230499145911958799457)
    ·
      refine ⟨127389922874359433969099593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169853230499145911958799457 127389922874359433969099593)
      ·
        refine ⟨95542442155769575476824695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127389922874359433969099593 95542442155769575476824695)
        ·
          refine ⟨143313663233654363215237043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95542442155769575476824695 143313663233654363215237043)
          ·
            refine ⟨214970494850481544822855565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143313663233654363215237043 214970494850481544822855565)
            ·
              refine ⟨80613935568930579308570837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214970494850481544822855565 80613935568930579308570837)
              ·
                refine ⟨1889389114896810452544629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80613935568930579308570837 1889389114896810452544629)
                ·
                  refine ⟨177130229521575979926059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1889389114896810452544629 177130229521575979926059)
                  ·
                    rfl

theorem cell23_3104639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 5].length) (baseStart_3104639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104639 prefixEnd_3104639 := by exact prefixLift 3104639
  have htrace : WordTrace (prefixWord ++ tailWord_3104639) baseStart_3104639 baseEnd_3104639 := by
    simpa [prefixWord, tailWord_3104639, baseEnd_3104639] using wordTrace_append hprefix tailTrace_3104639
  have hstable : (prefixWord ++ tailWord_3104639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104639).length < 2 ^ (prefixWord ++ tailWord_3104639).sum := by decide
  have hdescent : baseEnd_3104639 < baseStart_3104639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104649 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 3]
def baseStart_3104649 : Nat := 118140960795 + 3104649 * 2 ^ 59
def prefixEnd_3104649 : Nat := 4983230072969 + 3 ^ 40 * 3104649 * 2
def baseEnd_3104649 : Nat := 1594177200500728780209485

theorem tailTrace_3104649 : CollatzResearch.WordTrace tailWord_3104649 prefixEnd_3104649 1594177200500728780209485 := by
  unfold tailWord_3104649
  simp only [CollatzResearch.WordTrace]
  refine ⟨113235851729394379680397001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75490567819596253120264667 113235851729394379680397001)
  ·
    refine ⟨84926888797045784760297751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113235851729394379680397001 84926888797045784760297751)
    ·
      refine ⟨127390333195568677140446627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84926888797045784760297751 127390333195568677140446627)
      ·
        refine ⟨191085499793353015710669941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127390333195568677140446627 191085499793353015710669941)
        ·
          refine ⟨17914265605626845222875307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191085499793353015710669941 17914265605626845222875307)
          ·
            refine ⟨26871398408440267834312961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17914265605626845222875307 26871398408440267834312961)
            ·
              refine ⟨20153548806330200875734721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26871398408440267834312961 20153548806330200875734721)
              ·
                refine ⟨15115161604747650656801041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20153548806330200875734721 15115161604747650656801041)
                ·
                  refine ⟨11336371203560737992600781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15115161604747650656801041 11336371203560737992600781)
                  ·
                    refine ⟨4251139201335276747225293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11336371203560737992600781 4251139201335276747225293)
                    ·
                      refine ⟨1594177200500728780209485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4251139201335276747225293 1594177200500728780209485)
                      ·
                        rfl

theorem cell23_3104649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_3104649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104649 prefixEnd_3104649 := by exact prefixLift 3104649
  have htrace : WordTrace (prefixWord ++ tailWord_3104649) baseStart_3104649 baseEnd_3104649 := by
    simpa [prefixWord, tailWord_3104649, baseEnd_3104649] using wordTrace_append hprefix tailTrace_3104649
  have hstable : (prefixWord ++ tailWord_3104649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104649).length < 2 ^ (prefixWord ++ tailWord_3104649).sum := by decide
  have hdescent : baseEnd_3104649 < baseStart_3104649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104652 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_3104652 : Nat := 118140960795 + 3104652 * 2 ^ 59
def prefixEnd_3104652 : Nat := 4983230072969 + 3 ^ 40 * 3104652 * 2
def baseEnd_3104652 : Nat := 531392913647564089490657

theorem tailTrace_3104652 : CollatzResearch.WordTrace tailWord_3104652 prefixEnd_3104652 531392913647564089490657 := by
  unfold tailWord_3104652
  simp only [CollatzResearch.WordTrace]
  refine ⟨56617980574191755596378105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75490640765589007461837473 56617980574191755596378105)
  ·
    refine ⟨42463485430643816697283579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56617980574191755596378105 42463485430643816697283579)
    ·
      refine ⟨63695228145965725045925369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42463485430643816697283579 63695228145965725045925369)
      ·
        refine ⟨47771421109474293784444027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63695228145965725045925369 47771421109474293784444027)
        ·
          refine ⟨71657131664211440676666041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47771421109474293784444027 71657131664211440676666041)
          ·
            refine ⟨53742848748158580507499531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71657131664211440676666041 53742848748158580507499531)
            ·
              refine ⟨80614273122237870761249297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53742848748158580507499531 80614273122237870761249297)
              ·
                refine ⟨60460704841678403070936973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80614273122237870761249297 60460704841678403070936973)
                ·
                  refine ⟨22672764315629401151601365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60460704841678403070936973 22672764315629401151601365)
                  ·
                    refine ⟨531392913647564089490657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22672764315629401151601365 531392913647564089490657)
                    ·
                      rfl

theorem cell23_3104652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_3104652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104652 prefixEnd_3104652 := by exact prefixLift 3104652
  have htrace : WordTrace (prefixWord ++ tailWord_3104652) baseStart_3104652 baseEnd_3104652 := by
    simpa [prefixWord, tailWord_3104652, baseEnd_3104652] using wordTrace_append hprefix tailTrace_3104652
  have hstable : (prefixWord ++ tailWord_3104652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104652).length < 2 ^ (prefixWord ++ tailWord_3104652).sum := by decide
  have hdescent : baseEnd_3104652 < baseStart_3104652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104666 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3104666 : Nat := 118140960795 + 3104666 * 2 ^ 59
def prefixEnd_3104666 : Nat := 4983230072969 + 3 ^ 40 * 3104666 * 2
def baseEnd_3104666 : Nat := 1594185929671855213696907

theorem tailTrace_3104666 : CollatzResearch.WordTrace tailWord_3104666 prefixEnd_3104666 1594185929671855213696907 := by
  unfold tailWord_3104666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28309117942583197895941463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75490981180221861055843901 28309117942583197895941463)
  ·
    refine ⟨42463676913874796843912195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28309117942583197895941463 42463676913874796843912195)
    ·
      refine ⟨63695515370812195265868293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42463676913874796843912195 63695515370812195265868293)
      ·
        refine ⟨11942909132027286612350305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63695515370812195265868293 11942909132027286612350305)
        ·
          refine ⟨8957181849020464959262729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11942909132027286612350305 8957181849020464959262729)
          ·
            refine ⟨6717886386765348719447047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8957181849020464959262729 6717886386765348719447047)
            ·
              refine ⟨10076829580148023079170571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717886386765348719447047 10076829580148023079170571)
              ·
                refine ⟨15115244370222034618755857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10076829580148023079170571 15115244370222034618755857)
                ·
                  refine ⟨11336433277666525964066893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15115244370222034618755857 11336433277666525964066893)
                  ·
                    refine ⟨4251162479124947236525085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11336433277666525964066893 4251162479124947236525085)
                    ·
                      refine ⟨1594185929671855213696907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4251162479124947236525085 1594185929671855213696907)
                      ·
                        rfl

theorem cell23_3104666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3104666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104666 prefixEnd_3104666 := by exact prefixLift 3104666
  have htrace : WordTrace (prefixWord ++ tailWord_3104666) baseStart_3104666 baseEnd_3104666 := by
    simpa [prefixWord, tailWord_3104666, baseEnd_3104666] using wordTrace_append hprefix tailTrace_3104666
  have hstable : (prefixWord ++ tailWord_3104666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104666).length < 2 ^ (prefixWord ++ tailWord_3104666).sum := by decide
  have hdescent : baseEnd_3104666 < baseStart_3104666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104716 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_3104716 : Nat := 118140960795 + 3104716 * 2 ^ 59
def prefixEnd_3104716 : Nat := 4983230072969 + 3 ^ 40 * 3104716 * 2
def baseEnd_3104716 : Nat := 531403867901526672690559

theorem tailTrace_3104716 : CollatzResearch.WordTrace tailWord_3104716 prefixEnd_3104716 531403867901526672690559 := by
  unfold tailWord_3104716
  simp only [CollatzResearch.WordTrace]
  refine ⟨56619147710075825061543001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75492196946767766748724001 56619147710075825061543001)
  ·
    refine ⟨42464360782556868796157251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56619147710075825061543001 42464360782556868796157251)
    ·
      refine ⟨63696541173835303194235877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42464360782556868796157251 63696541173835303194235877)
      ·
        refine ⟨11943101470094119348919227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63696541173835303194235877 11943101470094119348919227)
        ·
          refine ⟨17914652205141179023378841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11943101470094119348919227 17914652205141179023378841)
          ·
            refine ⟨13435989153855884267534131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17914652205141179023378841 13435989153855884267534131)
            ·
              refine ⟨20153983730783826401301197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13435989153855884267534131 20153983730783826401301197)
              ·
                refine ⟨7557743899043934900487949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20153983730783826401301197 7557743899043934900487949)
                ·
                  refine ⟨2834153962141475587682981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7557743899043934900487949 2834153962141475587682981)
                  ·
                    refine ⟨531403867901526672690559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834153962141475587682981 531403867901526672690559)
                    ·
                      rfl

theorem cell23_3104716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_3104716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104716 prefixEnd_3104716 := by exact prefixLift 3104716
  have htrace : WordTrace (prefixWord ++ tailWord_3104716) baseStart_3104716 baseEnd_3104716 := by
    simpa [prefixWord, tailWord_3104716, baseEnd_3104716] using wordTrace_append hprefix tailTrace_3104716
  have hstable : (prefixWord ++ tailWord_3104716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104716).length < 2 ^ (prefixWord ++ tailWord_3104716).sum := by decide
  have hdescent : baseEnd_3104716 < baseStart_3104716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104750 : List Nat := [4, 1, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3104750 : Nat := 118140960795 + 3104750 * 2 ^ 59
def prefixEnd_3104750 : Nat := 4983230072969 + 3 ^ 40 * 3104750 * 2
def baseEnd_3104750 : Nat := 531409687348944295015507

theorem tailTrace_3104750 : CollatzResearch.WordTrace tailWord_3104750 prefixEnd_3104750 531409687348944295015507 := by
  unfold tailWord_3104750
  simp only [CollatzResearch.WordTrace]
  refine ⟨14154941937753559241227963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75493023668018982619882469 14154941937753559241227963)
  ·
    refine ⟨21232412906630338861841945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14154941937753559241227963 21232412906630338861841945)
    ·
      refine ⟨15924309679972754146381459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21232412906630338861841945 15924309679972754146381459)
      ·
        refine ⟨23886464519959131219572189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15924309679972754146381459 23886464519959131219572189)
        ·
          refine ⟨8957424194984674207339571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23886464519959131219572189 8957424194984674207339571)
          ·
            refine ⟨13436136292477011311009357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8957424194984674207339571 13436136292477011311009357)
            ·
              refine ⟨5038551109678879241628509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13436136292477011311009357 5038551109678879241628509)
              ·
                refine ⟨1889456666129579715610691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5038551109678879241628509 1889456666129579715610691)
                ·
                  refine ⟨2834184999194369573416037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889456666129579715610691 2834184999194369573416037)
                  ·
                    refine ⟨531409687348944295015507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834184999194369573416037 531409687348944295015507)
                    ·
                      rfl

theorem cell23_3104750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3104750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104750 prefixEnd_3104750 := by exact prefixLift 3104750
  have htrace : WordTrace (prefixWord ++ tailWord_3104750) baseStart_3104750 baseEnd_3104750 := by
    simpa [prefixWord, tailWord_3104750, baseEnd_3104750] using wordTrace_append hprefix tailTrace_3104750
  have hstable : (prefixWord ++ tailWord_3104750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104750).length < 2 ^ (prefixWord ++ tailWord_3104750).sum := by decide
  have hdescent : baseEnd_3104750 < baseStart_3104750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104773 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 3]
def baseStart_3104773 : Nat := 118140960795 + 3104773 * 2 ^ 59
def prefixEnd_3104773 : Nat := 4983230072969 + 3 ^ 40 * 3104773 * 2
def baseEnd_3104773 : Nat := 1594240872101886295058915

theorem tailTrace_3104773 : CollatzResearch.WordTrace tailWord_3104773 prefixEnd_3104773 1594240872101886295058915 := by
  unfold tailWord_3104773
  simp only [CollatzResearch.WordTrace]
  refine ⟨113240374380945148857910973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75493582920630099238607315 113240374380945148857910973)
  ·
    refine ⟨42465140392854430821716615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113240374380945148857910973 42465140392854430821716615)
    ·
      refine ⟨63697710589281646232574923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42465140392854430821716615 63697710589281646232574923)
      ·
        refine ⟨95546565883922469348862385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63697710589281646232574923 95546565883922469348862385)
        ·
          refine ⟨71659924412941852011646789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95546565883922469348862385 71659924412941852011646789)
          ·
            refine ⟨13436235827426597252183773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71659924412941852011646789 13436235827426597252183773)
            ·
              refine ⟨5038588435284973969568915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13436235827426597252183773 5038588435284973969568915)
              ·
                refine ⟨7557882652927460954353373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038588435284973969568915 7557882652927460954353373)
                ·
                  refine ⟨2834205994847797857882515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7557882652927460954353373 2834205994847797857882515)
                  ·
                    refine ⟨4251308992271696786823773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834205994847797857882515 4251308992271696786823773)
                    ·
                      refine ⟨1594240872101886295058915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4251308992271696786823773 1594240872101886295058915)
                      ·
                        rfl

theorem cell23_3104773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_3104773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104773 prefixEnd_3104773 := by exact prefixLift 3104773
  have htrace : WordTrace (prefixWord ++ tailWord_3104773) baseStart_3104773 baseEnd_3104773 := by
    simpa [prefixWord, tailWord_3104773, baseEnd_3104773] using wordTrace_append hprefix tailTrace_3104773
  have hstable : (prefixWord ++ tailWord_3104773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104773).length < 2 ^ (prefixWord ++ tailWord_3104773).sum := by decide
  have hdescent : baseEnd_3104773 < baseStart_3104773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104810 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3104810 : Nat := 118140960795 + 3104810 * 2 ^ 59
def prefixEnd_3104810 : Nat := 4983230072969 + 3 ^ 40 * 3104810 * 2
def baseEnd_3104810 : Nat := 531419956962034216765415

theorem tailTrace_3104810 : CollatzResearch.WordTrace tailWord_3104810 prefixEnd_3104810 531419956962034216765415 := by
  unfold tailWord_3104810
  simp only [CollatzResearch.WordTrace]
  refine ⟨28310430970452776044251971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75494482587874069451338589 28310430970452776044251971)
  ·
    refine ⟨42465646455679164066377957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28310430970452776044251971 42465646455679164066377957)
    ·
      refine ⟨7962308710439843262445867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42465646455679164066377957 7962308710439843262445867)
      ·
        refine ⟨11943463065659764893668801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7962308710439843262445867 11943463065659764893668801)
        ·
          refine ⟨8957597299244823670251601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11943463065659764893668801 8957597299244823670251601)
          ·
            refine ⟨6718197974433617752688701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8957597299244823670251601 6718197974433617752688701)
            ·
              refine ⟨2519324240412606657258263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6718197974433617752688701 2519324240412606657258263)
              ·
                refine ⟨3778986360618909985887395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2519324240412606657258263 3778986360618909985887395)
                ·
                  refine ⟨5668479540928364978831093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3778986360618909985887395 5668479540928364978831093)
                  ·
                    refine ⟨531419956962034216765415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5668479540928364978831093 531419956962034216765415)
                    ·
                      rfl

theorem cell23_3104810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3104810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104810 prefixEnd_3104810 := by exact prefixLift 3104810
  have htrace : WordTrace (prefixWord ++ tailWord_3104810) baseStart_3104810 baseEnd_3104810 := by
    simpa [prefixWord, tailWord_3104810, baseEnd_3104810] using wordTrace_append hprefix tailTrace_3104810
  have hstable : (prefixWord ++ tailWord_3104810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104810).length < 2 ^ (prefixWord ++ tailWord_3104810).sum := by decide
  have hdescent : baseEnd_3104810 < baseStart_3104810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104816 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 5]
def baseStart_3104816 : Nat := 118140960795 + 3104816 * 2 ^ 59
def prefixEnd_3104816 : Nat := 4983230072969 + 3 ^ 40 * 3104816 * 2
def baseEnd_3104816 : Nat := 1594262951770029626821217

theorem tailTrace_3104816 : CollatzResearch.WordTrace tailWord_3104816 prefixEnd_3104816 1594262951770029626821217 := by
  unfold tailWord_3104816
  simp only [CollatzResearch.WordTrace]
  refine ⟨56620971359894683600863151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75494628479859578134484201 56620971359894683600863151)
  ·
    refine ⟨84931457039842025401294727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56620971359894683600863151 84931457039842025401294727)
    ·
      refine ⟨127397185559763038101942091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84931457039842025401294727 127397185559763038101942091)
      ·
        refine ⟨191095778339644557152913137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127397185559763038101942091 191095778339644557152913137)
        ·
          refine ⟨143321833754733417864684853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191095778339644557152913137 143321833754733417864684853)
          ·
            refine ⟨13436421914506257924814205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143321833754733417864684853 13436421914506257924814205)
            ·
              refine ⟨5038658217939846721805327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13436421914506257924814205 5038658217939846721805327)
              ·
                refine ⟨7557987326909770082707991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038658217939846721805327 7557987326909770082707991)
                ·
                  refine ⟨11336980990364655124061987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7557987326909770082707991 11336980990364655124061987)
                  ·
                    refine ⟨17005471485546982686092981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11336980990364655124061987 17005471485546982686092981)
                    ·
                      refine ⟨1594262951770029626821217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17005471485546982686092981 1594262951770029626821217)
                      ·
                        rfl

theorem cell23_3104816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_3104816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104816 prefixEnd_3104816 := by exact prefixLift 3104816
  have htrace : WordTrace (prefixWord ++ tailWord_3104816) baseStart_3104816 baseEnd_3104816 := by
    simpa [prefixWord, tailWord_3104816, baseEnd_3104816] using wordTrace_append hprefix tailTrace_3104816
  have hstable : (prefixWord ++ tailWord_3104816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104816).length < 2 ^ (prefixWord ++ tailWord_3104816).sum := by decide
  have hdescent : baseEnd_3104816 < baseStart_3104816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104824 : List Nat := [2, 1, 2, 1, 6, 2, 2, 2, 1, 1, 3]
def baseStart_3104824 : Nat := 118140960795 + 3104824 * 2 ^ 59
def prefixEnd_3104824 : Nat := 4983230072969 + 3 ^ 40 * 3104824 * 2
def baseEnd_3104824 : Nat := 1594267059615265595521181

theorem tailTrace_3104824 : CollatzResearch.WordTrace tailWord_3104824 prefixEnd_3104824 1594267059615265595521181 := by
  unfold tailWord_3104824
  simp only [CollatzResearch.WordTrace]
  refine ⟨56621117251880192284008763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75494823002506923045345017 56621117251880192284008763)
  ·
    refine ⟨84931675877820288426013145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56621117251880192284008763 84931675877820288426013145)
    ·
      refine ⟨63698756908365216319509859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84931675877820288426013145 63698756908365216319509859)
      ·
        refine ⟨95548135362547824479264789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63698756908365216319509859 95548135362547824479264789)
        ·
          refine ⟨4478818845119429272465537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95548135362547824479264789 4478818845119429272465537)
          ·
            refine ⟨3359114133839571954349153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4478818845119429272465537 3359114133839571954349153)
            ·
              refine ⟨2519335600379678965761865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3359114133839571954349153 2519335600379678965761865)
              ·
                refine ⟨1889501700284759224321399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519335600379678965761865 1889501700284759224321399)
                ·
                  refine ⟨2834252550427138836482099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889501700284759224321399 2834252550427138836482099)
                  ·
                    refine ⟨4251378825640708254723149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834252550427138836482099 4251378825640708254723149)
                    ·
                      refine ⟨1594267059615265595521181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4251378825640708254723149 1594267059615265595521181)
                      ·
                        rfl

theorem cell23_3104824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 1, 3].length) (baseStart_3104824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104824 prefixEnd_3104824 := by exact prefixLift 3104824
  have htrace : WordTrace (prefixWord ++ tailWord_3104824) baseStart_3104824 baseEnd_3104824 := by
    simpa [prefixWord, tailWord_3104824, baseEnd_3104824] using wordTrace_append hprefix tailTrace_3104824
  have hstable : (prefixWord ++ tailWord_3104824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104824).length < 2 ^ (prefixWord ++ tailWord_3104824).sum := by decide
  have hdescent : baseEnd_3104824 < baseStart_3104824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104833 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3104833 : Nat := 118140960795 + 3104833 * 2 ^ 59
def prefixEnd_3104833 : Nat := 4983230072969 + 3 ^ 40 * 3104833 * 2
def baseEnd_3104833 : Nat := 1594271680941156060308639

theorem tailTrace_3104833 : CollatzResearch.WordTrace tailWord_3104833 prefixEnd_3104833 1594271680941156060308639 := by
  unfold tailWord_3104833
  simp only [CollatzResearch.WordTrace]
  refine ⟨113242562760727779105095153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75495041840485186070063435 113242562760727779105095153)
  ·
    refine ⟨84931922070545834328821365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113242562760727779105095153 84931922070545834328821365)
    ·
      refine ⟨7962367694113671968327003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84931922070545834328821365 7962367694113671968327003)
      ·
        refine ⟨11943551541170507952490505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7962367694113671968327003 11943551541170507952490505)
        ·
          refine ⟨8957663655877880964367879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11943551541170507952490505 8957663655877880964367879)
          ·
            refine ⟨13436495483816821446551819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8957663655877880964367879 13436495483816821446551819)
            ·
              refine ⟨20154743225725232169827729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13436495483816821446551819 20154743225725232169827729)
              ·
                refine ⟨15116057419293924127370797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20154743225725232169827729 15116057419293924127370797)
                ·
                  refine ⟨5668521532235221547764049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15116057419293924127370797 5668521532235221547764049)
                  ·
                    refine ⟨4251391149176416160823037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5668521532235221547764049 4251391149176416160823037)
                    ·
                      refine ⟨1594271680941156060308639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4251391149176416160823037 1594271680941156060308639)
                      ·
                        rfl

theorem cell23_3104833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3104833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104833 prefixEnd_3104833 := by exact prefixLift 3104833
  have htrace : WordTrace (prefixWord ++ tailWord_3104833) baseStart_3104833 baseEnd_3104833 := by
    simpa [prefixWord, tailWord_3104833, baseEnd_3104833] using wordTrace_append hprefix tailTrace_3104833
  have hstable : (prefixWord ++ tailWord_3104833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104833).length < 2 ^ (prefixWord ++ tailWord_3104833).sum := by decide
  have hdescent : baseEnd_3104833 < baseStart_3104833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104849 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 4, 7]
def baseStart_3104849 : Nat := 118140960795 + 3104849 * 2 ^ 59
def prefixEnd_3104849 : Nat := 4983230072969 + 3 ^ 40 * 3104849 * 2
def baseEnd_3104849 : Nat := 531426632210542665902855

theorem tailTrace_3104849 : CollatzResearch.WordTrace tailWord_3104849 prefixEnd_3104849 531426632210542665902855 := by
  unfold tailWord_3104849
  simp only [CollatzResearch.WordTrace]
  refine ⟨113243146328669813837677601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75495430885779875891785067 113243146328669813837677601)
  ·
    refine ⟨84932359746502360378258201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113243146328669813837677601 84932359746502360378258201)
    ·
      refine ⟨63699269809876770283693651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84932359746502360378258201 63699269809876770283693651)
      ·
        refine ⟨95548904714815155425540477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63699269809876770283693651 95548904714815155425540477)
        ·
          refine ⟨35830839268055683284577679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95548904714815155425540477 35830839268055683284577679)
          ·
            refine ⟨53746258902083524926866519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35830839268055683284577679 53746258902083524926866519)
            ·
              refine ⟨80619388353125287390299779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53746258902083524926866519 80619388353125287390299779)
              ·
                refine ⟨120929082529687931085449669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80619388353125287390299779 120929082529687931085449669)
                ·
                  refine ⟨22674202974316487078521813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120929082529687931085449669 22674202974316487078521813)
                  ·
                    refine ⟨531426632210542665902855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22674202974316487078521813 531426632210542665902855)
                    ·
                      rfl

theorem cell23_3104849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_3104849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104849 prefixEnd_3104849 := by exact prefixLift 3104849
  have htrace : WordTrace (prefixWord ++ tailWord_3104849) baseStart_3104849 baseEnd_3104849 := by
    simpa [prefixWord, tailWord_3104849, baseEnd_3104849] using wordTrace_append hprefix tailTrace_3104849
  have hstable : (prefixWord ++ tailWord_3104849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104849).length < 2 ^ (prefixWord ++ tailWord_3104849).sum := by decide
  have hdescent : baseEnd_3104849 < baseStart_3104849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104880 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 2, 1, 3]
def baseStart_3104880 : Nat := 118140960795 + 3104880 * 2 ^ 59
def prefixEnd_3104880 : Nat := 4983230072969 + 3 ^ 40 * 3104880 * 2
def baseEnd_3104880 : Nat := 1594295814531917376420923

theorem tailTrace_3104880 : CollatzResearch.WordTrace tailWord_3104880 prefixEnd_3104880 1594295814531917376420923 := by
  unfold tailWord_3104880
  simp only [CollatzResearch.WordTrace]
  refine ⟨56622138495778753066028047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75496184661038337421370729 56622138495778753066028047)
  ·
    refine ⟨84933207743668129599042071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56622138495778753066028047 84933207743668129599042071)
    ·
      refine ⟨127399811615502194398563107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84933207743668129599042071 127399811615502194398563107)
      ·
        refine ⟨191099717423253291597844661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127399811615502194398563107 191099717423253291597844661)
        ·
          refine ⟨17915598508429996087297937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191099717423253291597844661 17915598508429996087297937)
          ·
            refine ⟨13436698881322497065473453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17915598508429996087297937 13436698881322497065473453)
            ·
              refine ⟨5038762080495936399552545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13436698881322497065473453 5038762080495936399552545)
              ·
                refine ⟨3779071560371952299664409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5038762080495936399552545 3779071560371952299664409)
                ·
                  refine ⟨2834303670278964224748307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3779071560371952299664409 2834303670278964224748307)
                  ·
                    refine ⟨4251455505418446337122461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834303670278964224748307 4251455505418446337122461)
                    ·
                      refine ⟨1594295814531917376420923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4251455505418446337122461 1594295814531917376420923)
                      ·
                        rfl

theorem cell23_3104880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 1, 3].length) (baseStart_3104880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104880 prefixEnd_3104880 := by exact prefixLift 3104880
  have htrace : WordTrace (prefixWord ++ tailWord_3104880) baseStart_3104880 baseEnd_3104880 := by
    simpa [prefixWord, tailWord_3104880, baseEnd_3104880] using wordTrace_append hprefix tailTrace_3104880
  have hstable : (prefixWord ++ tailWord_3104880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104880).length < 2 ^ (prefixWord ++ tailWord_3104880).sum := by decide
  have hdescent : baseEnd_3104880 < baseStart_3104880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104897 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_3104897 : Nat := 118140960795 + 3104897 * 2 ^ 59
def prefixEnd_3104897 : Nat := 4983230072969 + 3 ^ 40 * 3104897 * 2
def baseEnd_3104897 : Nat := 1594304543703043809908345

theorem tailTrace_3104897 : CollatzResearch.WordTrace tailWord_3104897 prefixEnd_3104897 1594304543703043809908345 := by
  unfold tailWord_3104897
  simp only [CollatzResearch.WordTrace]
  refine ⟨113244897032495918035424945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75496598021663945356949963 113244897032495918035424945)
  ·
    refine ⟨84933672774371938526568709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113244897032495918035424945 84933672774371938526568709)
    ·
      refine ⟨15925063645194738473731633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84933672774371938526568709 15925063645194738473731633)
      ·
        refine ⟨11943797733896053855298725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15925063645194738473731633 11943797733896053855298725)
        ·
          refine ⟨2239462075105510097868511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11943797733896053855298725 2239462075105510097868511)
          ·
            refine ⟨3359193112658265146802767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239462075105510097868511 3359193112658265146802767)
            ·
              refine ⟨5038789668987397720204151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359193112658265146802767 5038789668987397720204151)
              ·
                refine ⟨7558184503481096580306227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038789668987397720204151 7558184503481096580306227)
                ·
                  refine ⟨11337276755221644870459341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7558184503481096580306227 11337276755221644870459341)
                  ·
                    refine ⟨4251478783208116826422253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11337276755221644870459341 4251478783208116826422253)
                    ·
                      refine ⟨1594304543703043809908345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4251478783208116826422253 1594304543703043809908345)
                      ·
                        rfl

theorem cell23_3104897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_3104897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104897 prefixEnd_3104897 := by exact prefixLift 3104897
  have htrace : WordTrace (prefixWord ++ tailWord_3104897) baseStart_3104897 baseEnd_3104897 := by
    simpa [prefixWord, tailWord_3104897, baseEnd_3104897] using wordTrace_append hprefix tailTrace_3104897
  have hstable : (prefixWord ++ tailWord_3104897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104897).length < 2 ^ (prefixWord ++ tailWord_3104897).sum := by decide
  have hdescent : baseEnd_3104897 < baseStart_3104897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104993 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_3104993 : Nat := 118140960795 + 3104993 * 2 ^ 59
def prefixEnd_3104993 : Nat := 4983230072969 + 3 ^ 40 * 3104993 * 2
def baseEnd_3104993 : Nat := 1594353837845875434307903

theorem tailTrace_3104993 : CollatzResearch.WordTrace tailWord_3104993 prefixEnd_3104993 1594353837845875434307903 := by
  unfold tailWord_3104993
  simp only [CollatzResearch.WordTrace]
  refine ⟨113248398440148126430919633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75498932293432084287279755 113248398440148126430919633)
  ·
    refine ⟨84936298830111094823189725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113248398440148126430919633 84936298830111094823189725)
    ·
      refine ⟨31851112061291660558696147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84936298830111094823189725 31851112061291660558696147)
      ·
        refine ⟨47776668091937490838044221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31851112061291660558696147 47776668091937490838044221)
        ·
          refine ⟨17916250534476559064266583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47776668091937490838044221 17916250534476559064266583)
          ·
            refine ⟨26874375801714838596399875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17916250534476559064266583 26874375801714838596399875)
            ·
              refine ⟨40311563702572257894599813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26874375801714838596399875 40311563702572257894599813)
              ·
                refine ⟨7558418194232298355237465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40311563702572257894599813 7558418194232298355237465)
                ·
                  refine ⟨5668813645674223766428099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7558418194232298355237465 5668813645674223766428099)
                  ·
                    refine ⟨8503220468511335649642149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5668813645674223766428099 8503220468511335649642149)
                    ·
                      refine ⟨1594353837845875434307903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8503220468511335649642149 1594353837845875434307903)
                      ·
                        rfl

theorem cell23_3104993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_3104993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104993 prefixEnd_3104993 := by exact prefixLift 3104993
  have htrace : WordTrace (prefixWord ++ tailWord_3104993) baseStart_3104993 baseEnd_3104993 := by
    simpa [prefixWord, tailWord_3104993, baseEnd_3104993] using wordTrace_append hprefix tailTrace_3104993
  have hstable : (prefixWord ++ tailWord_3104993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104993).length < 2 ^ (prefixWord ++ tailWord_3104993).sum := by decide
  have hdescent : baseEnd_3104993 < baseStart_3104993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104996 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_3104996 : Nat := 118140960795 + 3104996 * 2 ^ 59
def prefixEnd_3104996 : Nat := 4983230072969 + 3 ^ 40 * 3104996 * 2
def baseEnd_3104996 : Nat := 1594355378287838922570389

theorem tailTrace_3104996 : CollatzResearch.WordTrace tailWord_3104996 prefixEnd_3104996 1594355378287838922570389 := by
  unfold tailWord_3104996
  simp only [CollatzResearch.WordTrace]
  refine ⟨56624253929568628971639421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75499005239424838628852561 56624253929568628971639421)
  ·
    refine ⟨21234095223588235864364783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56624253929568628971639421 21234095223588235864364783)
    ·
      refine ⟨31851142835382353796547175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21234095223588235864364783 31851142835382353796547175)
      ·
        refine ⟨47776714253073530694820763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31851142835382353796547175 47776714253073530694820763)
        ·
          refine ⟨71665071379610296042231145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47776714253073530694820763 71665071379610296042231145)
          ·
            refine ⟨53748803534707722031673359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71665071379610296042231145 53748803534707722031673359)
            ·
              refine ⟨80623205302061583047510039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53748803534707722031673359 80623205302061583047510039)
              ·
                refine ⟨120934807953092374571265059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80623205302061583047510039 120934807953092374571265059)
                ·
                  refine ⟨181402211929638561856897589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120934807953092374571265059 181402211929638561856897589)
                  ·
                    refine ⟨17006457368403615174084149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181402211929638561856897589 17006457368403615174084149)
                    ·
                      refine ⟨1594355378287838922570389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17006457368403615174084149 1594355378287838922570389)
                      ·
                        rfl

theorem cell23_3104996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_3104996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3104996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3104996 prefixEnd_3104996 := by exact prefixLift 3104996
  have htrace : WordTrace (prefixWord ++ tailWord_3104996) baseStart_3104996 baseEnd_3104996 := by
    simpa [prefixWord, tailWord_3104996, baseEnd_3104996] using wordTrace_append hprefix tailTrace_3104996
  have hstable : (prefixWord ++ tailWord_3104996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104996).length < 2 ^ (prefixWord ++ tailWord_3104996).sum := by decide
  have hdescent : baseEnd_3104996 < baseStart_3104996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105003 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 3, 4]
def baseStart_3105003 : Nat := 118140960795 + 3105003 * 2 ^ 59
def prefixEnd_3105003 : Nat := 4983230072969 + 3 ^ 40 * 3105003 * 2
def baseEnd_3105003 : Nat := 531452990884140131727619

theorem tailTrace_3105003 : CollatzResearch.WordTrace tailWord_3105003 prefixEnd_3105003 531452990884140131727619 := by
  unfold tailWord_3105003
  simp only [CollatzResearch.WordTrace]
  refine ⟨113248763170111898138783663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75499175446741265425855775 113248763170111898138783663)
  ·
    refine ⟨169873144755167847208175495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113248763170111898138783663 169873144755167847208175495)
    ·
      refine ⟨254809717132751770812263243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169873144755167847208175495 254809717132751770812263243)
      ·
        refine ⟨382214575699127656218394865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254809717132751770812263243 382214575699127656218394865)
        ·
          refine ⟨286660931774345742163796149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382214575699127656218394865 286660931774345742163796149)
          ·
            refine ⟨26874462353844913327855889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286660931774345742163796149 26874462353844913327855889)
            ·
              refine ⟨20155846765383684995891917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26874462353844913327855889 20155846765383684995891917)
              ·
                refine ⟨7558442537018881873459469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20155846765383684995891917 7558442537018881873459469)
                ·
                  refine ⟨2834415951382080702547301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7558442537018881873459469 2834415951382080702547301)
                  ·
                    refine ⟨531452990884140131727619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834415951382080702547301 531452990884140131727619)
                    ·
                      rfl

theorem cell23_3105003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 4].length) (baseStart_3105003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105003 prefixEnd_3105003 := by exact prefixLift 3105003
  have htrace : WordTrace (prefixWord ++ tailWord_3105003) baseStart_3105003 baseEnd_3105003 := by
    simpa [prefixWord, tailWord_3105003, baseEnd_3105003] using wordTrace_append hprefix tailTrace_3105003
  have hstable : (prefixWord ++ tailWord_3105003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105003).length < 2 ^ (prefixWord ++ tailWord_3105003).sum := by decide
  have hdescent : baseEnd_3105003 < baseStart_3105003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105010 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_3105010 : Nat := 118140960795 + 3105010 * 2 ^ 59
def prefixEnd_3105010 : Nat := 4983230072969 + 3 ^ 40 * 3105010 * 2
def baseEnd_3105010 : Nat := 1594362567017001867795325

theorem tailTrace_3105010 : CollatzResearch.WordTrace tailWord_3105010 prefixEnd_3105010 1594362567017001867795325 := by
  unfold tailWord_3105010
  simp only [CollatzResearch.WordTrace]
  refine ⟨28312254620271634583572121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75499345654057692222858989 28312254620271634583572121)
  ·
    refine ⟨21234190965203725937679091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28312254620271634583572121 21234190965203725937679091)
    ·
      refine ⟨31851286447805588906518637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21234190965203725937679091 31851286447805588906518637)
      ·
        refine ⟨11944232417927095839944489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31851286447805588906518637 11944232417927095839944489)
        ·
          refine ⟨8958174313445321879958367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11944232417927095839944489 8958174313445321879958367)
          ·
            refine ⟨13437261470167982819937551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8958174313445321879958367 13437261470167982819937551)
            ·
              refine ⟨20155892205251974229906327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13437261470167982819937551 20155892205251974229906327)
              ·
                refine ⟨30233838307877961344859491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20155892205251974229906327 30233838307877961344859491)
                ·
                  refine ⟨45350757461816942017289237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30233838307877961344859491 45350757461816942017289237)
                  ·
                    refine ⟨2125816756022669157060433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45350757461816942017289237 2125816756022669157060433)
                    ·
                      refine ⟨1594362567017001867795325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125816756022669157060433 1594362567017001867795325)
                      ·
                        rfl

theorem cell23_3105010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_3105010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105010 prefixEnd_3105010 := by exact prefixLift 3105010
  have htrace : WordTrace (prefixWord ++ tailWord_3105010) baseStart_3105010 baseEnd_3105010 := by
    simpa [prefixWord, tailWord_3105010, baseEnd_3105010] using wordTrace_append hprefix tailTrace_3105010
  have hstable : (prefixWord ++ tailWord_3105010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105010).length < 2 ^ (prefixWord ++ tailWord_3105010).sum := by decide
  have hdescent : baseEnd_3105010 < baseStart_3105010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105020 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_3105020 : Nat := 118140960795 + 3105020 * 2 ^ 59
def prefixEnd_3105020 : Nat := 4983230072969 + 3 ^ 40 * 3105020 * 2
def baseEnd_3105020 : Nat := 531455900607848942890093

theorem tailTrace_3105020 : CollatzResearch.WordTrace tailWord_3105020 prefixEnd_3105020 531455900607848942890093 := by
  unfold tailWord_3105020
  simp only [CollatzResearch.WordTrace]
  refine ⟨56624691605525155021076257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75499588807366873361435009 56624691605525155021076257)
  ·
    refine ⟨42468518704143866265807193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56624691605525155021076257 42468518704143866265807193)
    ·
      refine ⟨31851389028107899699355395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42468518704143866265807193 31851389028107899699355395)
      ·
        refine ⟨47777083542161849549033093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31851389028107899699355395 47777083542161849549033093)
        ·
          refine ⟨8958203164155346790443705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47777083542161849549033093 8958203164155346790443705)
          ·
            refine ⟨6718652373116510092832779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8958203164155346790443705 6718652373116510092832779)
            ·
              refine ⟨10077978559674765139249169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6718652373116510092832779 10077978559674765139249169)
              ·
                refine ⟨7558483919756073854436877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10077978559674765139249169 7558483919756073854436877)
                ·
                  refine ⟨2834431469908527695413829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7558483919756073854436877 2834431469908527695413829)
                  ·
                    refine ⟨531455900607848942890093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834431469908527695413829 531455900607848942890093)
                    ·
                      rfl

theorem cell23_3105020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_3105020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105020 prefixEnd_3105020 := by exact prefixLift 3105020
  have htrace : WordTrace (prefixWord ++ tailWord_3105020) baseStart_3105020 baseEnd_3105020 := by
    simpa [prefixWord, tailWord_3105020, baseEnd_3105020] using wordTrace_append hprefix tailTrace_3105020
  have hstable : (prefixWord ++ tailWord_3105020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105020).length < 2 ^ (prefixWord ++ tailWord_3105020).sum := by decide
  have hdescent : baseEnd_3105020 < baseStart_3105020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105054 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3105054 : Nat := 118140960795 + 3105054 * 2 ^ 59
def prefixEnd_3105054 : Nat := 4983230072969 + 3 ^ 40 * 3105054 * 2
def baseEnd_3105054 : Nat := 531461720055266565215041

theorem tailTrace_3105054 : CollatzResearch.WordTrace tailWord_3105054 prefixEnd_3105054 531461720055266565215041 := by
  unfold tailWord_3105054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14156327911615891731111277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75500415528618089232593477 14156327911615891731111277)
  ·
    refine ⟨5308622966855959399166729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14156327911615891731111277 5308622966855959399166729)
    ·
      refine ⟨3981467225141969549375047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5308622966855959399166729 3981467225141969549375047)
      ·
        refine ⟨5972200837712954324062571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981467225141969549375047 5972200837712954324062571)
        ·
          refine ⟨8958301256569431486093857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972200837712954324062571 8958301256569431486093857)
          ·
            refine ⟨6718725942427073614570393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8958301256569431486093857 6718725942427073614570393)
            ·
              refine ⟨5039044456820305210927795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6718725942427073614570393 5039044456820305210927795)
              ·
                refine ⟨7558566685230457816391693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039044456820305210927795 7558566685230457816391693)
                ·
                  refine ⟨2834462506961421681146885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7558566685230457816391693 2834462506961421681146885)
                  ·
                    refine ⟨531461720055266565215041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834462506961421681146885 531461720055266565215041)
                    ·
                      rfl

theorem cell23_3105054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3105054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105054 prefixEnd_3105054 := by exact prefixLift 3105054
  have htrace : WordTrace (prefixWord ++ tailWord_3105054) baseStart_3105054 baseEnd_3105054 := by
    simpa [prefixWord, tailWord_3105054, baseEnd_3105054] using wordTrace_append hprefix tailTrace_3105054
  have hstable : (prefixWord ++ tailWord_3105054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105054).length < 2 ^ (prefixWord ++ tailWord_3105054).sum := by decide
  have hdescent : baseEnd_3105054 < baseStart_3105054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105100 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3105100 : Nat := 118140960795 + 3105100 * 2 ^ 59
def prefixEnd_3105100 : Nat := 4983230072969 + 3 ^ 40 * 3105100 * 2
def baseEnd_3105100 : Nat := 1594408780275906515669911

theorem tailTrace_3105100 : CollatzResearch.WordTrace tailWord_3105100 prefixEnd_3105100 1594408780275906515669911 := by
  unfold tailWord_3105100
  simp only [CollatzResearch.WordTrace]
  refine ⟨56626150525380241852532377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75501534033840322470043169 56626150525380241852532377)
  ·
    refine ⟨42469612894035181389399283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56626150525380241852532377 42469612894035181389399283)
    ·
      refine ⟨63704419341052772084098925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42469612894035181389399283 63704419341052772084098925)
      ·
        refine ⟨23889157252894789531537097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63704419341052772084098925 23889157252894789531537097)
        ·
          refine ⟨17916867939671092148652823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23889157252894789531537097 17916867939671092148652823)
          ·
            refine ⟨26875301909506638222979235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17916867939671092148652823 26875301909506638222979235)
            ·
              refine ⟨40312952864259957334468853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26875301909506638222979235 40312952864259957334468853)
              ·
                refine ⟨3779339331024371000106455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40312952864259957334468853 3779339331024371000106455)
                ·
                  refine ⟨5669008996536556500159683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779339331024371000106455 5669008996536556500159683)
                  ·
                    refine ⟨8503513494804834750239525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5669008996536556500159683 8503513494804834750239525)
                    ·
                      refine ⟨1594408780275906515669911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8503513494804834750239525 1594408780275906515669911)
                      ·
                        rfl

theorem cell23_3105100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3105100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105100 prefixEnd_3105100 := by exact prefixLift 3105100
  have htrace : WordTrace (prefixWord ++ tailWord_3105100) baseStart_3105100 baseEnd_3105100 := by
    simpa [prefixWord, tailWord_3105100, baseEnd_3105100] using wordTrace_append hprefix tailTrace_3105100
  have hstable : (prefixWord ++ tailWord_3105100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105100).length < 2 ^ (prefixWord ++ tailWord_3105100).sum := by decide
  have hdescent : baseEnd_3105100 < baseStart_3105100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105123 : List Nat := [1, 1, 1, 5, 2, 1, 4, 8]
def baseStart_3105123 : Nat := 118140960795 + 3105123 * 2 ^ 59
def prefixEnd_3105123 : Nat := 4983230072969 + 3 ^ 40 * 3105123 * 2
def baseEnd_3105123 : Nat := 59052614456702219469715

theorem tailTrace_3105123 : CollatzResearch.WordTrace tailWord_3105123 prefixEnd_3105123 59052614456702219469715 := by
  unfold tailWord_3105123
  simp only [CollatzResearch.WordTrace]
  refine ⟨113253139929677158633152023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75502093286451439088768015 113253139929677158633152023)
  ·
    refine ⟨169879709894515737949728035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113253139929677158633152023 169879709894515737949728035)
    ·
      refine ⟨254819564841773606924592053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169879709894515737949728035 254819564841773606924592053)
      ·
        refine ⟨23889334203916275649180505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254819564841773606924592053 23889334203916275649180505)
        ·
          refine ⟨17917000652937206736885379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23889334203916275649180505 17917000652937206736885379)
          ·
            refine ⟨26875500979405810105328069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17917000652937206736885379 26875500979405810105328069)
            ·
              refine ⟨5039156433638589394749013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26875500979405810105328069 5039156433638589394749013)
              ·
                refine ⟨59052614456702219469715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5039156433638589394749013 59052614456702219469715)
                ·
                  rfl

theorem cell23_3105123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 8].length) (baseStart_3105123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105123 prefixEnd_3105123 := by exact prefixLift 3105123
  have htrace : WordTrace (prefixWord ++ tailWord_3105123) baseStart_3105123 baseEnd_3105123 := by
    simpa [prefixWord, tailWord_3105123, baseEnd_3105123] using wordTrace_append hprefix tailTrace_3105123
  have hstable : (prefixWord ++ tailWord_3105123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105123).length < 2 ^ (prefixWord ++ tailWord_3105123).sum := by decide
  have hdescent : baseEnd_3105123 < baseStart_3105123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105127 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 2, 4]
def baseStart_3105127 : Nat := 118140960795 + 3105127 * 2 ^ 59
def prefixEnd_3105127 : Nat := 4983230072969 + 3 ^ 40 * 3105127 * 2
def baseEnd_3105127 : Nat := 531474214751192636677429

theorem tailTrace_3105127 : CollatzResearch.WordTrace tailWord_3105127 prefixEnd_3105127 531474214751192636677429 := by
  unfold tailWord_3105127
  simp only [CollatzResearch.WordTrace]
  refine ⟨113253285821662667316297635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75502190547775111544198423 113253285821662667316297635)
  ·
    refine ⟨169879928732494000974446453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113253285821662667316297635 169879928732494000974446453)
    ·
      refine ⟨15926243318671312591354355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169879928732494000974446453 15926243318671312591354355)
      ·
        refine ⟨23889364978006968887031533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15926243318671312591354355 23889364978006968887031533)
        ·
          refine ⟨8958511866752613332636825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23889364978006968887031533 8958511866752613332636825)
          ·
            refine ⟨6718883900064459999477619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8958511866752613332636825 6718883900064459999477619)
            ·
              refine ⟨10078325850096689999216429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6718883900064459999477619 10078325850096689999216429)
              ·
                refine ⟨3779372193786258749706161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10078325850096689999216429 3779372193786258749706161)
                ·
                  refine ⟨2834529145339694062279621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3779372193786258749706161 2834529145339694062279621)
                  ·
                    refine ⟨531474214751192636677429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834529145339694062279621 531474214751192636677429)
                    ·
                      rfl

theorem cell23_3105127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_3105127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105127 prefixEnd_3105127 := by exact prefixLift 3105127
  have htrace : WordTrace (prefixWord ++ tailWord_3105127) baseStart_3105127 baseEnd_3105127 := by
    simpa [prefixWord, tailWord_3105127, baseEnd_3105127] using wordTrace_append hprefix tailTrace_3105127
  have hstable : (prefixWord ++ tailWord_3105127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105127).length < 2 ^ (prefixWord ++ tailWord_3105127).sum := by decide
  have hdescent : baseEnd_3105127 < baseStart_3105127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105130 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3105130 : Nat := 118140960795 + 3105130 * 2 ^ 59
def prefixEnd_3105130 : Nat := 4983230072969 + 3 ^ 40 * 3105130 * 2
def baseEnd_3105130 : Nat := 1594424184695541398294773

theorem tailTrace_3105130 : CollatzResearch.WordTrace tailWord_3105130 prefixEnd_3105130 1594424184695541398294773 := by
  unfold tailWord_3105130
  simp only [CollatzResearch.WordTrace]
  refine ⟨28313348810162949707164211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75502263493767865885771229 28313348810162949707164211)
  ·
    refine ⟨42470023215244424560746317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28313348810162949707164211 42470023215244424560746317)
    ·
      refine ⟨15926258705716659210279869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42470023215244424560746317 15926258705716659210279869)
      ·
        refine ⟨5972347014643747203854951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15926258705716659210279869 5972347014643747203854951)
        ·
          refine ⟨8958520521965620805782427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972347014643747203854951 8958520521965620805782427)
          ·
            refine ⟨13437780782948431208673641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8958520521965620805782427 13437780782948431208673641)
            ·
              refine ⟨10078335587211323406505231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13437780782948431208673641 10078335587211323406505231)
              ·
                refine ⟨15117503380816985109757847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10078335587211323406505231 15117503380816985109757847)
                ·
                  refine ⟨22676255071225477664636771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15117503380816985109757847 22676255071225477664636771)
                  ·
                    refine ⟨34014382606838216496955157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22676255071225477664636771 34014382606838216496955157)
                    ·
                      refine ⟨1594424184695541398294773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34014382606838216496955157 1594424184695541398294773)
                      ·
                        rfl

theorem cell23_3105130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3105130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105130 prefixEnd_3105130 := by exact prefixLift 3105130
  have htrace : WordTrace (prefixWord ++ tailWord_3105130) baseStart_3105130 baseEnd_3105130 := by
    simpa [prefixWord, tailWord_3105130, baseEnd_3105130] using wordTrace_append hprefix tailTrace_3105130
  have hstable : (prefixWord ++ tailWord_3105130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105130).length < 2 ^ (prefixWord ++ tailWord_3105130).sum := by decide
  have hdescent : baseEnd_3105130 < baseStart_3105130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105193 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_3105193 : Nat := 118140960795 + 3105193 * 2 ^ 59
def prefixEnd_3105193 : Nat := 4983230072969 + 3 ^ 40 * 3105193 * 2
def baseEnd_3105193 : Nat := 1594456533976774651806983

theorem tailTrace_3105193 : CollatzResearch.WordTrace tailWord_3105193 prefixEnd_3105193 1594456533976774651806983 := by
  unfold tailWord_3105193
  simp only [CollatzResearch.WordTrace]
  refine ⟨113255693039423560588200233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75503795359615707058800155 113255693039423560588200233)
  ·
    refine ⟨84941769779567670441150175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113255693039423560588200233 84941769779567670441150175)
    ·
      refine ⟨127412654669351505661725263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84941769779567670441150175 127412654669351505661725263)
      ·
        refine ⟨191118982004027258492587895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127412654669351505661725263 191118982004027258492587895)
        ·
          refine ⟨286678473006040887738881843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191118982004027258492587895 286678473006040887738881843)
          ·
            refine ⟨430017709509061331608322765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286678473006040887738881843 430017709509061331608322765)
            ·
              refine ⟨161256641065897999353121037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 430017709509061331608322765 161256641065897999353121037)
              ·
                refine ⟨60471240399711749757420389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161256641065897999353121037 60471240399711749757420389)
                ·
                  refine ⟨11338357574945953079516323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60471240399711749757420389 11338357574945953079516323)
                  ·
                    refine ⟨17007536362418929619274485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11338357574945953079516323 17007536362418929619274485)
                    ·
                      refine ⟨1594456533976774651806983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17007536362418929619274485 1594456533976774651806983)
                      ·
                        rfl

theorem cell23_3105193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_3105193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105193 prefixEnd_3105193 := by exact prefixLift 3105193
  have htrace : WordTrace (prefixWord ++ tailWord_3105193) baseStart_3105193 baseEnd_3105193 := by
    simpa [prefixWord, tailWord_3105193, baseEnd_3105193] using wordTrace_append hprefix tailTrace_3105193
  have hstable : (prefixWord ++ tailWord_3105193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105193).length < 2 ^ (prefixWord ++ tailWord_3105193).sum := by decide
  have hdescent : baseEnd_3105193 < baseStart_3105193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105207 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 1, 4, 2]
def baseStart_3105207 : Nat := 118140960795 + 3105207 * 2 ^ 59
def prefixEnd_3105207 : Nat := 4983230072969 + 3 ^ 40 * 3105207 * 2
def baseEnd_3105207 : Nat := 1594463722705937597031919

theorem tailTrace_3105207 : CollatzResearch.WordTrace tailWord_3105207 prefixEnd_3105207 1594463722705937597031919 := by
  unfold tailWord_3105207
  simp only [CollatzResearch.WordTrace]
  refine ⟨113256203661372840979209875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75504135774248560652806583 113256203661372840979209875)
  ·
    refine ⟨169884305492059261468814813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113256203661372840979209875 169884305492059261468814813)
    ·
      refine ⟨63706614559522223050805555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169884305492059261468814813 63706614559522223050805555)
      ·
        refine ⟨95559921839283334576208333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63706614559522223050805555 95559921839283334576208333)
        ·
          refine ⟨35834970689731250466078125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95559921839283334576208333 35834970689731250466078125)
          ·
            refine ⟨13438114008649218924779297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35834970689731250466078125 13438114008649218924779297)
            ·
              refine ⟨10078585506486914193584473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13438114008649218924779297 10078585506486914193584473)
              ·
                refine ⟨7558939129865185645188355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10078585506486914193584473 7558939129865185645188355)
                ·
                  refine ⟨11338408694797778467782533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7558939129865185645188355 11338408694797778467782533)
                  ·
                    refine ⟨2125951630274583462709225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11338408694797778467782533 2125951630274583462709225)
                    ·
                      refine ⟨1594463722705937597031919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125951630274583462709225 1594463722705937597031919)
                      ·
                        rfl

theorem cell23_3105207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_3105207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105207 prefixEnd_3105207 := by exact prefixLift 3105207
  have htrace : WordTrace (prefixWord ++ tailWord_3105207) baseStart_3105207 baseEnd_3105207 := by
    simpa [prefixWord, tailWord_3105207, baseEnd_3105207] using wordTrace_append hprefix tailTrace_3105207
  have hstable : (prefixWord ++ tailWord_3105207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105207).length < 2 ^ (prefixWord ++ tailWord_3105207).sum := by decide
  have hdescent : baseEnd_3105207 < baseStart_3105207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105224 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_3105224 : Nat := 118140960795 + 3105224 * 2 ^ 59
def prefixEnd_3105224 : Nat := 4983230072969 + 3 ^ 40 * 3105224 * 2
def baseEnd_3105224 : Nat := 1594472451877064030519341

theorem tailTrace_3105224 : CollatzResearch.WordTrace tailWord_3105224 prefixEnd_3105224 1594472451877064030519341 := by
  unfold tailWord_3105224
  simp only [CollatzResearch.WordTrace]
  refine ⟨56628411851155626441289363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75504549134874168588385817 56628411851155626441289363)
  ·
    refine ⟨84942617776733439661934045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56628411851155626441289363 84942617776733439661934045)
    ·
      refine ⟨31853481666275039873225267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84942617776733439661934045 31853481666275039873225267)
      ·
        refine ⟨47780222499412559809837901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31853481666275039873225267 47780222499412559809837901)
        ·
          refine ⟨17917583437279709928689213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47780222499412559809837901 17917583437279709928689213)
          ·
            refine ⟨6719093788979891223258455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17917583437279709928689213 6719093788979891223258455)
            ·
              refine ⟨10078640683469836834887683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6719093788979891223258455 10078640683469836834887683)
              ·
                refine ⟨15117961025204755252331525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10078640683469836834887683 15117961025204755252331525)
                ·
                  refine ⟨2834617692225891609812161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15117961025204755252331525 2834617692225891609812161)
                  ·
                    refine ⟨2125963269169418707359121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2834617692225891609812161 2125963269169418707359121)
                    ·
                      refine ⟨1594472451877064030519341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125963269169418707359121 1594472451877064030519341)
                      ·
                        rfl

theorem cell23_3105224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_3105224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105224 prefixEnd_3105224 := by exact prefixLift 3105224
  have htrace : WordTrace (prefixWord ++ tailWord_3105224) baseStart_3105224 baseEnd_3105224 := by
    simpa [prefixWord, tailWord_3105224, baseEnd_3105224] using wordTrace_append hprefix tailTrace_3105224
  have hstable : (prefixWord ++ tailWord_3105224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105224).length < 2 ^ (prefixWord ++ tailWord_3105224).sum := by decide
  have hdescent : baseEnd_3105224 < baseStart_3105224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105241 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 2, 2, 2]
def baseStart_3105241 : Nat := 118140960795 + 3105241 * 2 ^ 59
def prefixEnd_3105241 : Nat := 4983230072969 + 3 ^ 40 * 3105241 * 2
def baseEnd_3105241 : Nat := 1594481181048190464006763

theorem tailTrace_3105241 : CollatzResearch.WordTrace tailWord_3105241 prefixEnd_3105241 1594481181048190464006763 := by
  unfold tailWord_3105241
  simp only [CollatzResearch.WordTrace]
  refine ⟨113257443743249664785947577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75504962495499776523965051 113257443743249664785947577)
  ·
    refine ⟨84943082807437248589460683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113257443743249664785947577 84943082807437248589460683)
    ·
      refine ⟨127414624211155872884191025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84943082807437248589460683 127414624211155872884191025)
      ·
        refine ⟨95560968158366904663143269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127414624211155872884191025 95560968158366904663143269)
        ·
          refine ⟨17917681529693794624339363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95560968158366904663143269 17917681529693794624339363)
          ·
            refine ⟨26876522294540691936509045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17917681529693794624339363 26876522294540691936509045)
            ·
              refine ⟨2519673965113189869047723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26876522294540691936509045 2519673965113189869047723)
              ·
                refine ⟨3779510947669784803571585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2519673965113189869047723 3779510947669784803571585)
                ·
                  refine ⟨2834633210752338602678689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3779510947669784803571585 2834633210752338602678689)
                  ·
                    refine ⟨2125974908064253952009017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2834633210752338602678689 2125974908064253952009017)
                    ·
                      refine ⟨1594481181048190464006763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2125974908064253952009017 1594481181048190464006763)
                      ·
                        rfl

theorem cell23_3105241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_3105241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105241 prefixEnd_3105241 := by exact prefixLift 3105241
  have htrace : WordTrace (prefixWord ++ tailWord_3105241) baseStart_3105241 baseEnd_3105241 := by
    simpa [prefixWord, tailWord_3105241, baseEnd_3105241] using wordTrace_append hprefix tailTrace_3105241
  have hstable : (prefixWord ++ tailWord_3105241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105241).length < 2 ^ (prefixWord ++ tailWord_3105241).sum := by decide
  have hdescent : baseEnd_3105241 < baseStart_3105241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105260 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_3105260 : Nat := 118140960795 + 3105260 * 2 ^ 59
def prefixEnd_3105260 : Nat := 4983230072969 + 3 ^ 40 * 3105260 * 2
def baseEnd_3105260 : Nat := 531496979060208629889725

theorem tailTrace_3105260 : CollatzResearch.WordTrace tailWord_3105260 prefixEnd_3105260 531496979060208629889725 := by
  unfold tailWord_3105260
  simp only [CollatzResearch.WordTrace]
  refine ⟨56629068365090415515444617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75505424486787220687259489 56629068365090415515444617)
  ·
    refine ⟨42471801273817811636583463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56629068365090415515444617 42471801273817811636583463)
    ·
      refine ⟨63707701910726717454875195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42471801273817811636583463 63707701910726717454875195)
      ·
        refine ⟨95561552866090076182312793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63707701910726717454875195 95561552866090076182312793)
        ·
          refine ⟨71671164649567557136734595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95561552866090076182312793 71671164649567557136734595)
          ·
            refine ⟨107506746974351335705101893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71671164649567557136734595 107506746974351335705101893)
            ·
              refine ⟨20157515057690875444706605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107506746974351335705101893 20157515057690875444706605)
              ·
                refine ⟨7559068146634078291764977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20157515057690875444706605 7559068146634078291764977)
                ·
                  refine ⟨5669301109975558718823733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7559068146634078291764977 5669301109975558718823733)
                  ·
                    refine ⟨531496979060208629889725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5669301109975558718823733 531496979060208629889725)
                    ·
                      rfl

theorem cell23_3105260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_3105260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105260 prefixEnd_3105260 := by exact prefixLift 3105260
  have htrace : WordTrace (prefixWord ++ tailWord_3105260) baseStart_3105260 baseEnd_3105260 := by
    simpa [prefixWord, tailWord_3105260, baseEnd_3105260] using wordTrace_append hprefix tailTrace_3105260
  have hstable : (prefixWord ++ tailWord_3105260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105260).length < 2 ^ (prefixWord ++ tailWord_3105260).sum := by decide
  have hdescent : baseEnd_3105260 < baseStart_3105260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105287 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_3105287 : Nat := 118140960795 + 3105287 * 2 ^ 59
def prefixEnd_3105287 : Nat := 4983230072969 + 3 ^ 40 * 3105287 * 2
def baseEnd_3105287 : Nat := 1594504801158297284031551

theorem tailTrace_3105287 : CollatzResearch.WordTrace tailWord_3105287 prefixEnd_3105287 1594504801158297284031551 := by
  unfold tailWord_3105287
  simp only [CollatzResearch.WordTrace]
  refine ⟨113259121501083014642122115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75506081000722009761414743 113259121501083014642122115)
  ·
    refine ⟨169888682251624521963183173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113259121501083014642122115 169888682251624521963183173)
    ·
      refine ⟨31854127922179597868096845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169888682251624521963183173 31854127922179597868096845)
      ·
        refine ⟨11945297970817349200536317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31854127922179597868096845 11945297970817349200536317)
        ·
          refine ⟨4479486739056505950201119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11945297970817349200536317 4479486739056505950201119)
          ·
            refine ⟨6719230108584758925301679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4479486739056505950201119 6719230108584758925301679)
            ·
              refine ⟨10078845162877138387952519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6719230108584758925301679 10078845162877138387952519)
              ·
                refine ⟨15118267744315707581928779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10078845162877138387952519 15118267744315707581928779)
                ·
                  refine ⟨22677401616473561372893169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15118267744315707581928779 22677401616473561372893169)
                  ·
                    refine ⟨17008051212355171029669877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22677401616473561372893169 17008051212355171029669877)
                    ·
                      refine ⟨1594504801158297284031551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17008051212355171029669877 1594504801158297284031551)
                      ·
                        rfl

theorem cell23_3105287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_3105287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105287 prefixEnd_3105287 := by exact prefixLift 3105287
  have htrace : WordTrace (prefixWord ++ tailWord_3105287) baseStart_3105287 baseEnd_3105287 := by
    simpa [prefixWord, tailWord_3105287, baseEnd_3105287] using wordTrace_append hprefix tailTrace_3105287
  have hstable : (prefixWord ++ tailWord_3105287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105287).length < 2 ^ (prefixWord ++ tailWord_3105287).sum := by decide
  have hdescent : baseEnd_3105287 < baseStart_3105287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105317 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_3105317 : Nat := 118140960795 + 3105317 * 2 ^ 59
def prefixEnd_3105317 : Nat := 4983230072969 + 3 ^ 40 * 3105317 * 2
def baseEnd_3105317 : Nat := 1594520205577932166656413

theorem tailTrace_3105317 : CollatzResearch.WordTrace tailWord_3105317 prefixEnd_3105317 1594520205577932166656413 := by
  unfold tailWord_3105317
  simp only [CollatzResearch.WordTrace]
  refine ⟨113260215690974329765714205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75506810460649553177142803 113260215690974329765714205)
  ·
    refine ⟨42472580884115373662142827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113260215690974329765714205 42472580884115373662142827)
    ·
      refine ⟨63708871326173060493214241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42472580884115373662142827 63708871326173060493214241)
      ·
        refine ⟨47781653494629795369910681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63708871326173060493214241 47781653494629795369910681)
        ·
          refine ⟨35836240120972346527433011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47781653494629795369910681 35836240120972346527433011)
          ·
            refine ⟨53754360181458519791149517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35836240120972346527433011 53754360181458519791149517)
            ·
              refine ⟨20157885068046944921681069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53754360181458519791149517 20157885068046944921681069)
              ·
                refine ⟨7559206900517604345630401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20157885068046944921681069 7559206900517604345630401)
                ·
                  refine ⟨5669405175388203259222801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7559206900517604345630401 5669405175388203259222801)
                  ·
                    refine ⟨4252053881541152444417101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5669405175388203259222801 4252053881541152444417101)
                    ·
                      refine ⟨1594520205577932166656413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252053881541152444417101 1594520205577932166656413)
                      ·
                        rfl

theorem cell23_3105317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_3105317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105317 prefixEnd_3105317 := by exact prefixLift 3105317
  have htrace : WordTrace (prefixWord ++ tailWord_3105317) baseStart_3105317 baseEnd_3105317 := by
    simpa [prefixWord, tailWord_3105317, baseEnd_3105317] using wordTrace_append hprefix tailTrace_3105317
  have hstable : (prefixWord ++ tailWord_3105317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105317).length < 2 ^ (prefixWord ++ tailWord_3105317).sum := by decide
  have hdescent : baseEnd_3105317 < baseStart_3105317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105337 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 6]
def baseStart_3105337 : Nat := 118140960795 + 3105337 * 2 ^ 59
def prefixEnd_3105337 : Nat := 4983230072969 + 3 ^ 40 * 3105337 * 2
def baseEnd_3105337 : Nat := 177170052799002454267369

theorem tailTrace_3105337 : CollatzResearch.WordTrace tailWord_3105337 prefixEnd_3105337 177170052799002454267369 := by
  unfold tailWord_3105337
  simp only [CollatzResearch.WordTrace]
  refine ⟨113260945150901873181442265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75507296767267915454294843 113260945150901873181442265)
  ·
    refine ⟨84945708863176404886081699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113260945150901873181442265 84945708863176404886081699)
    ·
      refine ⟨127418563294764607329122549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84945708863176404886081699 127418563294764607329122549)
      ·
        refine ⟨11945490308884181937105239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127418563294764607329122549 11945490308884181937105239)
        ·
          refine ⟨17918235463326272905657859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11945490308884181937105239 17918235463326272905657859)
          ·
            refine ⟨26877353194989409358486789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17918235463326272905657859 26877353194989409358486789)
            ·
              refine ⟨5039503724060514254716273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26877353194989409358486789 5039503724060514254716273)
              ·
                refine ⟨3779627793045385691037205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039503724060514254716273 3779627793045385691037205)
                ·
                  refine ⟨177170052799002454267369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3779627793045385691037205 177170052799002454267369)
                  ·
                    rfl

theorem cell23_3105337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 6].length) (baseStart_3105337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105337 prefixEnd_3105337 := by exact prefixLift 3105337
  have htrace : WordTrace (prefixWord ++ tailWord_3105337) baseStart_3105337 baseEnd_3105337 := by
    simpa [prefixWord, tailWord_3105337, baseEnd_3105337] using wordTrace_append hprefix tailTrace_3105337
  have hstable : (prefixWord ++ tailWord_3105337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105337).length < 2 ^ (prefixWord ++ tailWord_3105337).sum := by decide
  have hdescent : baseEnd_3105337 < baseStart_3105337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105341 : List Nat := [1, 4, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_3105341 : Nat := 118140960795 + 3105341 * 2 ^ 59
def prefixEnd_3105341 : Nat := 4983230072969 + 3 ^ 40 * 3105341 * 2
def baseEnd_3105341 : Nat := 531510843037880024252101

theorem tailTrace_3105341 : CollatzResearch.WordTrace tailWord_3105341 prefixEnd_3105341 531510843037880024252101 := by
  unfold tailWord_3105341
  simp only [CollatzResearch.WordTrace]
  refine ⟨113261091042887381864587877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75507394028591587909725251 113261091042887381864587877)
  ·
    refine ⟨21236454570541384099610227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113261091042887381864587877 21236454570541384099610227)
    ·
      refine ⟨31854681855812076149415341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21236454570541384099610227 31854681855812076149415341)
      ·
        refine ⟨11945505695929528556030753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31854681855812076149415341 11945505695929528556030753)
        ·
          refine ⟨8959129271947146417023065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11945505695929528556030753 8959129271947146417023065)
          ·
            refine ⟨6719346953960359812767299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8959129271947146417023065 6719346953960359812767299)
            ·
              refine ⟨10079020430940539719150949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6719346953960359812767299 10079020430940539719150949)
              ·
                refine ⟨1889816330801351197340803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10079020430940539719150949 1889816330801351197340803)
                ·
                  refine ⟨2834724496202026796011205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889816330801351197340803 2834724496202026796011205)
                  ·
                    refine ⟨531510843037880024252101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834724496202026796011205 531510843037880024252101)
                    ·
                      rfl

theorem cell23_3105341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_3105341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105341 prefixEnd_3105341 := by exact prefixLift 3105341
  have htrace : WordTrace (prefixWord ++ tailWord_3105341) baseStart_3105341 baseEnd_3105341 := by
    simpa [prefixWord, tailWord_3105341, baseEnd_3105341] using wordTrace_append hprefix tailTrace_3105341
  have hstable : (prefixWord ++ tailWord_3105341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105341).length < 2 ^ (prefixWord ++ tailWord_3105341).sum := by decide
  have hdescent : baseEnd_3105341 < baseStart_3105341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105347 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 3]
def baseStart_3105347 : Nat := 118140960795 + 3105347 * 2 ^ 59
def prefixEnd_3105347 : Nat := 4983230072969 + 3 ^ 40 * 3105347 * 2
def baseEnd_3105347 : Nat := 1594535609997567049281275

theorem tailTrace_3105347 : CollatzResearch.WordTrace tailWord_3105347 prefixEnd_3105347 1594535609997567049281275 := by
  unfold tailWord_3105347
  simp only [CollatzResearch.WordTrace]
  refine ⟨113261309880865644889306295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75507539920577096592870863 113261309880865644889306295)
  ·
    refine ⟨169891964821298467333959443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113261309880865644889306295 169891964821298467333959443)
    ·
      refine ⟨254837947231947701000939165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169891964821298467333959443 254837947231947701000939165)
      ·
        refine ⟨95564230211980387875352187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254837947231947701000939165 95564230211980387875352187)
        ·
          refine ⟨143346345317970581813028281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95564230211980387875352187 143346345317970581813028281)
          ·
            refine ⟨107509758988477936359771211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143346345317970581813028281 107509758988477936359771211)
            ·
              refine ⟨161264638482716904539656817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107509758988477936359771211 161264638482716904539656817)
              ·
                refine ⟨120948478862037678404742613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161264638482716904539656817 120948478862037678404742613)
                ·
                  refine ⟨2834729973329008087611155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 120948478862037678404742613 2834729973329008087611155)
                  ·
                    refine ⟨4252094959993512131416733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834729973329008087611155 4252094959993512131416733)
                    ·
                      refine ⟨1594535609997567049281275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252094959993512131416733 1594535609997567049281275)
                      ·
                        rfl

theorem cell23_3105347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_3105347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105347 prefixEnd_3105347 := by exact prefixLift 3105347
  have htrace : WordTrace (prefixWord ++ tailWord_3105347) baseStart_3105347 baseEnd_3105347 := by
    simpa [prefixWord, tailWord_3105347, baseEnd_3105347] using wordTrace_append hprefix tailTrace_3105347
  have hstable : (prefixWord ++ tailWord_3105347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105347).length < 2 ^ (prefixWord ++ tailWord_3105347).sum := by decide
  have hdescent : baseEnd_3105347 < baseStart_3105347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105364 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_3105364 : Nat := 118140960795 + 3105364 * 2 ^ 59
def prefixEnd_3105364 : Nat := 4983230072969 + 3 ^ 40 * 3105364 * 2
def baseEnd_3105364 : Nat := 1594544339168693482768697

theorem tailTrace_3105364 : CollatzResearch.WordTrace tailWord_3105364 prefixEnd_3105364 1594544339168693482768697 := by
  unfold tailWord_3105364
  simp only [CollatzResearch.WordTrace]
  refine ⟨56630964960902028396337573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75507953281202704528450097 56630964960902028396337573)
  ·
    refine ⟨10618305930169130324313295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56630964960902028396337573 10618305930169130324313295)
    ·
      refine ⟨15927458895253695486469943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10618305930169130324313295 15927458895253695486469943)
      ·
        refine ⟨23891188342880543229704915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15927458895253695486469943 23891188342880543229704915)
        ·
          refine ⟨35836782514320814844557373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23891188342880543229704915 35836782514320814844557373)
          ·
            refine ⟨13438793442870305566709015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35836782514320814844557373 13438793442870305566709015)
            ·
              refine ⟨20158190164305458350063523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13438793442870305566709015 20158190164305458350063523)
              ·
                refine ⟨30237285246458187525095285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20158190164305458350063523 30237285246458187525095285)
                ·
                  refine ⟨2834745491855455080477683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30237285246458187525095285 2834745491855455080477683)
                  ·
                    refine ⟨4252118237783182620716525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834745491855455080477683 4252118237783182620716525)
                    ·
                      refine ⟨1594544339168693482768697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252118237783182620716525 1594544339168693482768697)
                      ·
                        rfl

theorem cell23_3105364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_3105364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105364 prefixEnd_3105364 := by exact prefixLift 3105364
  have htrace : WordTrace (prefixWord ++ tailWord_3105364) baseStart_3105364 baseEnd_3105364 := by
    simpa [prefixWord, tailWord_3105364, baseEnd_3105364] using wordTrace_append hprefix tailTrace_3105364
  have hstable : (prefixWord ++ tailWord_3105364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105364).length < 2 ^ (prefixWord ++ tailWord_3105364).sum := by decide
  have hdescent : baseEnd_3105364 < baseStart_3105364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105367 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 1, 5]
def baseStart_3105367 : Nat := 118140960795 + 3105367 * 2 ^ 59
def prefixEnd_3105367 : Nat := 4983230072969 + 3 ^ 40 * 3105367 * 2
def baseEnd_3105367 : Nat := 531515293203552323677061

theorem tailTrace_3105367 : CollatzResearch.WordTrace tailWord_3105367 prefixEnd_3105367 531515293203552323677061 := by
  unfold tailWord_3105367
  simp only [CollatzResearch.WordTrace]
  refine ⟨113262039340793188305034355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75508026227195458870022903 113262039340793188305034355)
  ·
    refine ⟨169893059011189782457551533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113262039340793188305034355 169893059011189782457551533)
    ·
      refine ⟨63709897129196168421581825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169893059011189782457551533 63709897129196168421581825)
      ·
        refine ⟨47782422846897126316186369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63709897129196168421581825 47782422846897126316186369)
        ·
          refine ⟨35836817135172844737139777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47782422846897126316186369 35836817135172844737139777)
          ·
            refine ⟨26877612851379633552854833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35836817135172844737139777 26877612851379633552854833)
            ·
              refine ⟨20158209638534725164641125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26877612851379633552854833 20158209638534725164641125)
              ·
                refine ⟨3779664307225260968370211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20158209638534725164641125 3779664307225260968370211)
                ·
                  refine ⟨5669496460837891452555317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779664307225260968370211 5669496460837891452555317)
                  ·
                    refine ⟨531515293203552323677061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5669496460837891452555317 531515293203552323677061)
                    ·
                      rfl

theorem cell23_3105367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_3105367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105367 prefixEnd_3105367 := by exact prefixLift 3105367
  have htrace : WordTrace (prefixWord ++ tailWord_3105367) baseStart_3105367 baseEnd_3105367 := by
    simpa [prefixWord, tailWord_3105367, baseEnd_3105367] using wordTrace_append hprefix tailTrace_3105367
  have hstable : (prefixWord ++ tailWord_3105367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105367).length < 2 ^ (prefixWord ++ tailWord_3105367).sum := by decide
  have hdescent : baseEnd_3105367 < baseStart_3105367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105398 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3105398 : Nat := 118140960795 + 3105398 * 2 ^ 59
def prefixEnd_3105398 : Nat := 4983230072969 + 3 ^ 40 * 3105398 * 2
def baseEnd_3105398 : Nat := 1594561797510946349743541

theorem tailTrace_3105398 : CollatzResearch.WordTrace tailWord_3105398 prefixEnd_3105398 1594561797510946349743541 := by
  unfold tailWord_3105398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7078948125230055037463303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75508780002453920399608565 7078948125230055037463303)
  ·
    refine ⟨10618422187845082556194955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7078948125230055037463303 10618422187845082556194955)
    ·
      refine ⟨15927633281767623834292433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10618422187845082556194955 15927633281767623834292433)
      ·
        refine ⟨11945724961325717875719325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15927633281767623834292433 11945724961325717875719325)
        ·
          refine ⟨4479646860497144203394747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11945724961325717875719325 4479646860497144203394747)
          ·
            refine ⟨6719470290745716305092121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4479646860497144203394747 6719470290745716305092121)
            ·
              refine ⟨5039602718059287228819091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6719470290745716305092121 5039602718059287228819091)
              ·
                refine ⟨7559404077088930843228637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039602718059287228819091 7559404077088930843228637)
                ·
                  refine ⟨2834776528908349066210739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7559404077088930843228637 2834776528908349066210739)
                  ·
                    refine ⟨4252164793362523599316109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834776528908349066210739 4252164793362523599316109)
                    ·
                      refine ⟨1594561797510946349743541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252164793362523599316109 1594561797510946349743541)
                      ·
                        rfl

theorem cell23_3105398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3105398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105398 prefixEnd_3105398 := by exact prefixLift 3105398
  have htrace : WordTrace (prefixWord ++ tailWord_3105398) baseStart_3105398 baseEnd_3105398 := by
    simpa [prefixWord, tailWord_3105398, baseEnd_3105398] using wordTrace_append hprefix tailTrace_3105398
  have hstable : (prefixWord ++ tailWord_3105398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105398).length < 2 ^ (prefixWord ++ tailWord_3105398).sum := by decide
  have hdescent : baseEnd_3105398 < baseStart_3105398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105400 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_3105400 : Nat := 118140960795 + 3105400 * 2 ^ 59
def prefixEnd_3105400 : Nat := 4983230072969 + 3 ^ 40 * 3105400 * 2
def baseEnd_3105400 : Nat := 1594562824472255341918531

theorem tailTrace_3105400 : CollatzResearch.WordTrace tailWord_3105400 prefixEnd_3105400 1594562824472255341918531 := by
  unfold tailWord_3105400
  simp only [CollatzResearch.WordTrace]
  refine ⟨56631621474836817470492827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75508828633115756627323769 56631621474836817470492827)
  ·
    refine ⟨84947432212255226205739241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56631621474836817470492827 84947432212255226205739241)
    ·
      refine ⟨63710574159191419654304431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84947432212255226205739241 63710574159191419654304431)
      ·
        refine ⟨95565861238787129481456647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63710574159191419654304431 95565861238787129481456647)
        ·
          refine ⟨143348791858180694222184971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95565861238787129481456647 143348791858180694222184971)
          ·
            refine ⟨215023187787271041333277457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143348791858180694222184971 215023187787271041333277457)
            ·
              refine ⟨161267390840453280999958093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215023187787271041333277457 161267390840453280999958093)
              ·
                refine ⟨60475271565169980374984285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161267390840453280999958093 60475271565169980374984285)
                ·
                  refine ⟨22678226836938742640619107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60475271565169980374984285 22678226836938742640619107)
                  ·
                    refine ⟨34017340255408113960928661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22678226836938742640619107 34017340255408113960928661)
                    ·
                      refine ⟨1594562824472255341918531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34017340255408113960928661 1594562824472255341918531)
                      ·
                        rfl

theorem cell23_3105400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_3105400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105400 prefixEnd_3105400 := by exact prefixLift 3105400
  have htrace : WordTrace (prefixWord ++ tailWord_3105400) baseStart_3105400 baseEnd_3105400 := by
    simpa [prefixWord, tailWord_3105400, baseEnd_3105400] using wordTrace_append hprefix tailTrace_3105400
  have hstable : (prefixWord ++ tailWord_3105400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105400).length < 2 ^ (prefixWord ++ tailWord_3105400).sum := by decide
  have hdescent : baseEnd_3105400 < baseStart_3105400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105407 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 3]
def baseStart_3105407 : Nat := 118140960795 + 3105407 * 2 ^ 59
def prefixEnd_3105407 : Nat := 4983230072969 + 3 ^ 40 * 3105407 * 2
def baseEnd_3105407 : Nat := 1594566418836836814530999

theorem tailTrace_3105407 : CollatzResearch.WordTrace tailWord_3105407 prefixEnd_3105407 1594566418836836814530999 := by
  unfold tailWord_3105407
  simp only [CollatzResearch.WordTrace]
  refine ⟨113263498260648275136490475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75508998840432183424326983 113263498260648275136490475)
  ·
    refine ⟨169895247390972412704735713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113263498260648275136490475 169895247390972412704735713)
    ·
      refine ⟨127421435543229309528551785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169895247390972412704735713 127421435543229309528551785)
      ·
        refine ⟨95566076657421982146413839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127421435543229309528551785 95566076657421982146413839)
        ·
          refine ⟨143349114986132973219620759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95566076657421982146413839 143349114986132973219620759)
          ·
            refine ⟨215023672479199459829431139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143349114986132973219620759 215023672479199459829431139)
            ·
              refine ⟨322535508718799189744146709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215023672479199459829431139 322535508718799189744146709)
              ·
                refine ⟨15118851971193712019256877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 322535508718799189744146709 15118851971193712019256877)
                ·
                  refine ⟨5669569489197642007221329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15118851971193712019256877 5669569489197642007221329)
                  ·
                    refine ⟨4252177116898231505415997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5669569489197642007221329 4252177116898231505415997)
                    ·
                      refine ⟨1594566418836836814530999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252177116898231505415997 1594566418836836814530999)
                      ·
                        rfl

theorem cell23_3105407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_3105407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105407 prefixEnd_3105407 := by exact prefixLift 3105407
  have htrace : WordTrace (prefixWord ++ tailWord_3105407) baseStart_3105407 baseEnd_3105407 := by
    simpa [prefixWord, tailWord_3105407, baseEnd_3105407] using wordTrace_append hprefix tailTrace_3105407
  have hstable : (prefixWord ++ tailWord_3105407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105407).length < 2 ^ (prefixWord ++ tailWord_3105407).sum := by decide
  have hdescent : baseEnd_3105407 < baseStart_3105407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105455 : List Nat := [1, 1, 2, 1, 2, 6, 3, 2, 1, 2, 2]
def baseStart_3105455 : Nat := 118140960795 + 3105455 * 2 ^ 59
def prefixEnd_3105455 : Nat := 4983230072969 + 3 ^ 40 * 3105455 * 2
def baseEnd_3105455 : Nat := 1594591065908252626730779

theorem tailTrace_3105455 : CollatzResearch.WordTrace tailWord_3105455 prefixEnd_3105455 1594591065908252626730779 := by
  unfold tailWord_3105455
  simp only [CollatzResearch.WordTrace]
  refine ⟨113265248964474379334237819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75510165976316252889491879 113265248964474379334237819)
  ·
    refine ⟨169897873446711569001356729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113265248964474379334237819 169897873446711569001356729)
    ·
      refine ⟨127423405085033676751017547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169897873446711569001356729 127423405085033676751017547)
      ·
        refine ⟨191135107627550515126526321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127423405085033676751017547 191135107627550515126526321)
        ·
          refine ⟨143351330720662886344894741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191135107627550515126526321 143351330720662886344894741)
          ·
            refine ⟨6719593627531072797416941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143351330720662886344894741 6719593627531072797416941)
            ·
              refine ⟨2519847610324152299031353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6719593627531072797416941 2519847610324152299031353)
              ·
                refine ⟨1889885707743114224273515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519847610324152299031353 1889885707743114224273515)
                ·
                  refine ⟨2834828561614671336410273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889885707743114224273515 2834828561614671336410273)
                  ·
                    refine ⟨2126121421211003502307705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2834828561614671336410273 2126121421211003502307705)
                    ·
                      refine ⟨1594591065908252626730779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126121421211003502307705 1594591065908252626730779)
                      ·
                        rfl

theorem cell23_3105455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 2, 2].length) (baseStart_3105455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105455 prefixEnd_3105455 := by exact prefixLift 3105455
  have htrace : WordTrace (prefixWord ++ tailWord_3105455) baseStart_3105455 baseEnd_3105455 := by
    simpa [prefixWord, tailWord_3105455, baseEnd_3105455] using wordTrace_append hprefix tailTrace_3105455
  have hstable : (prefixWord ++ tailWord_3105455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105455).length < 2 ^ (prefixWord ++ tailWord_3105455).sum := by decide
  have hdescent : baseEnd_3105455 < baseStart_3105455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105471 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 3]
def baseStart_3105471 : Nat := 118140960795 + 3105471 * 2 ^ 59
def prefixEnd_3105471 : Nat := 4983230072969 + 3 ^ 40 * 3105471 * 2
def baseEnd_3105471 : Nat := 1594599281598724564130705

theorem tailTrace_3105471 : CollatzResearch.WordTrace tailWord_3105471 prefixEnd_3105471 1594599281598724564130705 := by
  unfold tailWord_3105471
  simp only [CollatzResearch.WordTrace]
  refine ⟨113265832532416414066820267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75510555021610942711213511 113265832532416414066820267)
  ·
    refine ⟨169898748798624621100230401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113265832532416414066820267 169898748798624621100230401)
    ·
      refine ⟨127424061598968465825172801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169898748798624621100230401 127424061598968465825172801)
      ·
        refine ⟨95568046199226349368879601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127424061598968465825172801 95568046199226349368879601)
        ·
          refine ⟨71676034649419762026659701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95568046199226349368879601 71676034649419762026659701)
          ·
            refine ⟨6719628248383102689999347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71676034649419762026659701 6719628248383102689999347)
            ·
              refine ⟨10079442372574654034999021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6719628248383102689999347 10079442372574654034999021)
              ·
                refine ⟨3779790889715495263124633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10079442372574654034999021 3779790889715495263124633)
                ·
                  refine ⟨2834843167286621447343475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3779790889715495263124633 2834843167286621447343475)
                  ·
                    refine ⟨4252264750929932171015213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834843167286621447343475 4252264750929932171015213)
                    ·
                      refine ⟨1594599281598724564130705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252264750929932171015213 1594599281598724564130705)
                      ·
                        rfl

theorem cell23_3105471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_3105471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105471 prefixEnd_3105471 := by exact prefixLift 3105471
  have htrace : WordTrace (prefixWord ++ tailWord_3105471) baseStart_3105471 baseEnd_3105471 := by
    simpa [prefixWord, tailWord_3105471, baseEnd_3105471] using wordTrace_append hprefix tailTrace_3105471
  have hstable : (prefixWord ++ tailWord_3105471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105471).length < 2 ^ (prefixWord ++ tailWord_3105471).sum := by decide
  have hdescent : baseEnd_3105471 < baseStart_3105471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105497 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_3105497 : Nat := 118140960795 + 3105497 * 2 ^ 59
def prefixEnd_3105497 : Nat := 4983230072969 + 3 ^ 40 * 3105497 * 2
def baseEnd_3105497 : Nat := 1594612632095741462405585

theorem tailTrace_3105497 : CollatzResearch.WordTrace tailWord_3105497 prefixEnd_3105497 1594612632095741462405585 := by
  unfold tailWord_3105497
  simp only [CollatzResearch.WordTrace]
  refine ⟨113266780830322220507266745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75511187220214813671511163 113266780830322220507266745)
  ·
    refine ⟨84950085622741665380450059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113266780830322220507266745 84950085622741665380450059)
    ·
      refine ⟨127425128434112498070675089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84950085622741665380450059 127425128434112498070675089)
      ·
        refine ⟨95568846325584373553006317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127425128434112498070675089 95568846325584373553006317)
        ·
          refine ⟨35838317372094140082377369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95568846325584373553006317 35838317372094140082377369)
          ·
            refine ⟨26878738029070605061783027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35838317372094140082377369 26878738029070605061783027)
            ·
              refine ⟨40318107043605907592674541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26878738029070605061783027 40318107043605907592674541)
              ·
                refine ⟨15119290141352215347252953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40318107043605907592674541 15119290141352215347252953)
                ·
                  refine ⟨11339467606014161510439715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15119290141352215347252953 11339467606014161510439715)
                  ·
                    refine ⟨17009201409021242265659573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11339467606014161510439715 17009201409021242265659573)
                    ·
                      refine ⟨1594612632095741462405585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17009201409021242265659573 1594612632095741462405585)
                      ·
                        rfl

theorem cell23_3105497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_3105497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105497 prefixEnd_3105497 := by exact prefixLift 3105497
  have htrace : WordTrace (prefixWord ++ tailWord_3105497) baseStart_3105497 baseEnd_3105497 := by
    simpa [prefixWord, tailWord_3105497, baseEnd_3105497] using wordTrace_append hprefix tailTrace_3105497
  have hstable : (prefixWord ++ tailWord_3105497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105497).length < 2 ^ (prefixWord ++ tailWord_3105497).sum := by decide
  have hdescent : baseEnd_3105497 < baseStart_3105497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105498 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2]
def baseStart_3105498 : Nat := 118140960795 + 3105498 * 2 ^ 59
def prefixEnd_3105498 : Nat := 4983230072969 + 3 ^ 40 * 3105498 * 2
def baseEnd_3105498 : Nat := 1594613145576395958493081

theorem tailTrace_3105498 : CollatzResearch.WordTrace tailWord_3105498 prefixEnd_3105498 1594613145576395958493081 := by
  unfold tailWord_3105498
  simp only [CollatzResearch.WordTrace]
  refine ⟨28316704325829649419513287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75511211535545731785368765 28316704325829649419513287)
  ·
    refine ⟨42475056488744474129269931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28316704325829649419513287 42475056488744474129269931)
    ·
      refine ⟨63712584733116711193904897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42475056488744474129269931 63712584733116711193904897)
      ·
        refine ⟨47784438549837533395428673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63712584733116711193904897 47784438549837533395428673)
        ·
          refine ⟨35838328912378150046571505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47784438549837533395428673 35838328912378150046571505)
          ·
            refine ⟨26878746684283612534928629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35838328912378150046571505 26878746684283612534928629)
            ·
              refine ⟨2519882501651588675149559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26878746684283612534928629 2519882501651588675149559)
              ·
                refine ⟨3779823752477383012724339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2519882501651588675149559 3779823752477383012724339)
                ·
                  refine ⟨5669735628716074519086509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779823752477383012724339 5669735628716074519086509)
                  ·
                    refine ⟨2126150860768527944657441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5669735628716074519086509 2126150860768527944657441)
                    ·
                      refine ⟨1594613145576395958493081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126150860768527944657441 1594613145576395958493081)
                      ·
                        rfl

theorem cell23_3105498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_3105498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105498 prefixEnd_3105498 := by exact prefixLift 3105498
  have htrace : WordTrace (prefixWord ++ tailWord_3105498) baseStart_3105498 baseEnd_3105498 := by
    simpa [prefixWord, tailWord_3105498, baseEnd_3105498] using wordTrace_append hprefix tailTrace_3105498
  have hstable : (prefixWord ++ tailWord_3105498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105498).length < 2 ^ (prefixWord ++ tailWord_3105498).sum := by decide
  have hdescent : baseEnd_3105498 < baseStart_3105498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105534 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_3105534 : Nat := 118140960795 + 3105534 * 2 ^ 59
def prefixEnd_3105534 : Nat := 4983230072969 + 3 ^ 40 * 3105534 * 2
def baseEnd_3105534 : Nat := 177181292319995313071435

theorem tailTrace_3105534 : CollatzResearch.WordTrace tailWord_3105534 prefixEnd_3105534 177181292319995313071435 := by
  unfold tailWord_3105534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14158516291398521978295457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75512086887458783884242437 14158516291398521978295457)
  ·
    refine ⟨10618887218548891483721593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14158516291398521978295457 10618887218548891483721593)
    ·
      refine ⟨7964165413911668612791195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10618887218548891483721593 7964165413911668612791195)
      ·
        refine ⟨11946248120867502919186793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7964165413911668612791195 11946248120867502919186793)
        ·
          refine ⟨8959686090650627189390095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11946248120867502919186793 8959686090650627189390095)
          ·
            refine ⟨13439529135975940784085143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8959686090650627189390095 13439529135975940784085143)
            ·
              refine ⟨20159293703963911176127715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13439529135975940784085143 20159293703963911176127715)
              ·
                refine ⟨30238940555945866764191573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20159293703963911176127715 30238940555945866764191573)
                ·
                  refine ⟨177181292319995313071435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30238940555945866764191573 177181292319995313071435)
                  ·
                    rfl

theorem cell23_3105534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_3105534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105534 prefixEnd_3105534 := by exact prefixLift 3105534
  have htrace : WordTrace (prefixWord ++ tailWord_3105534) baseStart_3105534 baseEnd_3105534 := by
    simpa [prefixWord, tailWord_3105534, baseEnd_3105534] using wordTrace_append hprefix tailTrace_3105534
  have hstable : (prefixWord ++ tailWord_3105534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105534).length < 2 ^ (prefixWord ++ tailWord_3105534).sum := by decide
  have hdescent : baseEnd_3105534 < baseStart_3105534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105621 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_3105621 : Nat := 118140960795 + 3105621 * 2 ^ 59
def prefixEnd_3105621 : Nat := 4983230072969 + 3 ^ 40 * 3105621 * 2
def baseEnd_3105621 : Nat := 1594676303696898977255015

theorem tailTrace_3105621 : CollatzResearch.WordTrace tailWord_3105621 prefixEnd_3105621 1594676303696898977255015 := by
  unfold tailWord_3105621
  simp only [CollatzResearch.WordTrace]
  refine ⟨113271303481872989684780717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75514202321248659789853811 113271303481872989684780717)
  ·
    refine ⟨42476738805702371131792769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113271303481872989684780717 42476738805702371131792769)
    ·
      refine ⟨31857554104276778348844577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42476738805702371131792769 31857554104276778348844577)
      ·
        refine ⟨23893165578207583761633433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31857554104276778348844577 23893165578207583761633433)
        ·
          refine ⟨17919874183655687821225075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23893165578207583761633433 17919874183655687821225075)
          ·
            refine ⟨26879811275483531731837613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17919874183655687821225075 26879811275483531731837613)
            ·
              refine ⟨10079929228306324399439105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26879811275483531731837613 10079929228306324399439105)
              ·
                refine ⟨7559946921229743299579329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10079929228306324399439105 7559946921229743299579329)
                ·
                  refine ⟨5669960190922307474684497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7559946921229743299579329 5669960190922307474684497)
                  ·
                    refine ⟨4252470143191730606013373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5669960190922307474684497 4252470143191730606013373)
                    ·
                      refine ⟨1594676303696898977255015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252470143191730606013373 1594676303696898977255015)
                      ·
                        rfl

theorem cell23_3105621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_3105621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105621 prefixEnd_3105621 := by exact prefixLift 3105621
  have htrace : WordTrace (prefixWord ++ tailWord_3105621) baseStart_3105621 baseEnd_3105621 := by
    simpa [prefixWord, tailWord_3105621, baseEnd_3105621] using wordTrace_append hprefix tailTrace_3105621
  have hstable : (prefixWord ++ tailWord_3105621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105621).length < 2 ^ (prefixWord ++ tailWord_3105621).sum := by decide
  have hdescent : baseEnd_3105621 < baseStart_3105621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105627 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 6]
def baseStart_3105627 : Nat := 118140960795 + 3105627 * 2 ^ 59
def prefixEnd_3105627 : Nat := 4983230072969 + 3 ^ 40 * 3105627 * 2
def baseEnd_3105627 : Nat := 1594679384580825953779987

theorem tailTrace_3105627 : CollatzResearch.WordTrace tailWord_3105627 prefixEnd_3105627 1594679384580825953779987 := by
  unfold tailWord_3105627
  simp only [CollatzResearch.WordTrace]
  refine ⟨113271522319851252709499135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75514348213234168472999423 113271522319851252709499135)
  ·
    refine ⟨169907283479776879064248703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113271522319851252709499135 169907283479776879064248703)
    ·
      refine ⟨254860925219665318596373055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169907283479776879064248703 254860925219665318596373055)
      ·
        refine ⟨382291387829497977894559583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254860925219665318596373055 382291387829497977894559583)
        ·
          refine ⟨573437081744246966841839375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382291387829497977894559583 573437081744246966841839375)
          ·
            refine ⟨860155622616370450262759063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573437081744246966841839375 860155622616370450262759063)
            ·
              refine ⟨1290233433924555675394138595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860155622616370450262759063 1290233433924555675394138595)
              ·
                refine ⟨1935350150886833513091207893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290233433924555675394138595 1935350150886833513091207893)
                ·
                  refine ⟨45359769161410160463075185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1935350150886833513091207893 45359769161410160463075185)
                  ·
                    refine ⟨34019826871057620347306389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45359769161410160463075185 34019826871057620347306389)
                    ·
                      refine ⟨1594679384580825953779987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34019826871057620347306389 1594679384580825953779987)
                      ·
                        rfl

theorem cell23_3105627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_3105627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105627 prefixEnd_3105627 := by exact prefixLift 3105627
  have htrace : WordTrace (prefixWord ++ tailWord_3105627) baseStart_3105627 baseEnd_3105627 := by
    simpa [prefixWord, tailWord_3105627, baseEnd_3105627] using wordTrace_append hprefix tailTrace_3105627
  have hstable : (prefixWord ++ tailWord_3105627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105627).length < 2 ^ (prefixWord ++ tailWord_3105627).sum := by decide
  have hdescent : baseEnd_3105627 < baseStart_3105627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105628 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_3105628 : Nat := 118140960795 + 3105628 * 2 ^ 59
def prefixEnd_3105628 : Nat := 4983230072969 + 3 ^ 40 * 3105628 * 2
def baseEnd_3105628 : Nat := 531559966020493483289161

theorem tailTrace_3105628 : CollatzResearch.WordTrace tailWord_3105628 prefixEnd_3105628 531559966020493483289161 := by
  unfold tailWord_3105628
  simp only [CollatzResearch.WordTrace]
  refine ⟨56635779396423814940142769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75514372528565086586857025 56635779396423814940142769)
  ·
    refine ⟨42476834547317861205107077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56635779396423814940142769 42476834547317861205107077)
    ·
      refine ⟨7964406477622098975957577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42476834547317861205107077 7964406477622098975957577)
      ·
        refine ⟨5973304858216574231968183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7964406477622098975957577 5973304858216574231968183)
        ·
          refine ⟨8959957287324861347952275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5973304858216574231968183 8959957287324861347952275)
          ·
            refine ⟨13439935930987292021928413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8959957287324861347952275 13439935930987292021928413)
            ·
              refine ⟨5039975974120234508223155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13439935930987292021928413 5039975974120234508223155)
              ·
                refine ⟨7559963961180351762334733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039975974120234508223155 7559963961180351762334733)
                ·
                  refine ⟨2834986485442631910875525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7559963961180351762334733 2834986485442631910875525)
                  ·
                    refine ⟨531559966020493483289161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834986485442631910875525 531559966020493483289161)
                    ·
                      rfl

theorem cell23_3105628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_3105628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105628 prefixEnd_3105628 := by exact prefixLift 3105628
  have htrace : WordTrace (prefixWord ++ tailWord_3105628) baseStart_3105628 baseEnd_3105628 := by
    simpa [prefixWord, tailWord_3105628, baseEnd_3105628] using wordTrace_append hprefix tailTrace_3105628
  have hstable : (prefixWord ++ tailWord_3105628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105628).length < 2 ^ (prefixWord ++ tailWord_3105628).sum := by decide
  have hdescent : baseEnd_3105628 < baseStart_3105628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105651 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 3]
def baseStart_3105651 : Nat := 118140960795 + 3105651 * 2 ^ 59
def prefixEnd_3105651 : Nat := 4983230072969 + 3 ^ 40 * 3105651 * 2
def baseEnd_3105651 : Nat := 1594691708116533859879877

theorem tailTrace_3105651 : CollatzResearch.WordTrace tailWord_3105651 prefixEnd_3105651 1594691708116533859879877 := by
  unfold tailWord_3105651
  simp only [CollatzResearch.WordTrace]
  refine ⟨113272397671764304808372807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75514931781176203205581871 113272397671764304808372807)
  ·
    refine ⟨169908596507646457212559211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113272397671764304808372807 169908596507646457212559211)
    ·
      refine ⟨254862894761469685818838817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169908596507646457212559211 254862894761469685818838817)
      ·
        refine ⟨191147171071102264364129113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254862894761469685818838817 191147171071102264364129113)
        ·
          refine ⟨143360378303326698273096835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191147171071102264364129113 143360378303326698273096835)
          ·
            refine ⟨215040567454990047409645253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143360378303326698273096835 215040567454990047409645253)
            ·
              refine ⟨40320106397810633889308485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215040567454990047409645253 40320106397810633889308485)
              ·
                refine ⟨7560019949589493854245341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40320106397810633889308485 7560019949589493854245341)
                ·
                  refine ⟨2835007481096060195342003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7560019949589493854245341 2835007481096060195342003)
                  ·
                    refine ⟨4252511221644090293013005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2835007481096060195342003 4252511221644090293013005)
                    ·
                      refine ⟨1594691708116533859879877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252511221644090293013005 1594691708116533859879877)
                      ·
                        rfl

theorem cell23_3105651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 3].length) (baseStart_3105651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105651 prefixEnd_3105651 := by exact prefixLift 3105651
  have htrace : WordTrace (prefixWord ++ tailWord_3105651) baseStart_3105651 baseEnd_3105651 := by
    simpa [prefixWord, tailWord_3105651, baseEnd_3105651] using wordTrace_append hprefix tailTrace_3105651
  have hstable : (prefixWord ++ tailWord_3105651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105651).length < 2 ^ (prefixWord ++ tailWord_3105651).sum := by decide
  have hdescent : baseEnd_3105651 < baseStart_3105651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105661 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_3105661 : Nat := 118140960795 + 3105661 * 2 ^ 59
def prefixEnd_3105661 : Nat := 4983230072969 + 3 ^ 40 * 3105661 * 2
def baseEnd_3105661 : Nat := 1594696842923078820754831

theorem tailTrace_3105661 : CollatzResearch.WordTrace tailWord_3105661 prefixEnd_3105661 1594696842923078820754831 := by
  unfold tailWord_3105661
  simp only [CollatzResearch.WordTrace]
  refine ⟨113272762401728076516236837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75515174934485384344157891 113272762401728076516236837)
  ·
    refine ⟨21238642950324014346794407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113272762401728076516236837 21238642950324014346794407)
    ·
      refine ⟨31857964425486021520191611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21238642950324014346794407 31857964425486021520191611)
      ·
        refine ⟨47786946638229032280287417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31857964425486021520191611 47786946638229032280287417)
        ·
          refine ⟨35840209978671774210215563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47786946638229032280287417 35840209978671774210215563)
          ·
            refine ⟨53760314968007661315323345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35840209978671774210215563 53760314968007661315323345)
            ·
              refine ⟨40320236226005745986492509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53760314968007661315323345 40320236226005745986492509)
              ·
                refine ⟨15120088584752154744934691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40320236226005745986492509 15120088584752154744934691)
                ·
                  refine ⟨22680132877128232117402037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15120088584752154744934691 22680132877128232117402037)
                  ·
                    refine ⟨2126262457230771761006441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22680132877128232117402037 2126262457230771761006441)
                    ·
                      refine ⟨1594696842923078820754831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126262457230771761006441 1594696842923078820754831)
                      ·
                        rfl

theorem cell23_3105661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_3105661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105661 prefixEnd_3105661 := by exact prefixLift 3105661
  have htrace : WordTrace (prefixWord ++ tailWord_3105661) baseStart_3105661 baseEnd_3105661 := by
    simpa [prefixWord, tailWord_3105661, baseEnd_3105661] using wordTrace_append hprefix tailTrace_3105661
  have hstable : (prefixWord ++ tailWord_3105661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105661).length < 2 ^ (prefixWord ++ tailWord_3105661).sum := by decide
  have hdescent : baseEnd_3105661 < baseStart_3105661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105685 : List Nat := [1, 3, 2, 1, 1, 5, 1, 4, 1, 1, 3]
def baseStart_3105685 : Nat := 118140960795 + 3105685 * 2 ^ 59
def prefixEnd_3105685 : Nat := 4983230072969 + 3 ^ 40 * 3105685 * 2
def baseEnd_3105685 : Nat := 1594709166458786726854721

theorem tailTrace_3105685 : CollatzResearch.WordTrace tailWord_3105685 prefixEnd_3105685 1594709166458786726854721 := by
  unfold tailWord_3105685
  simp only [CollatzResearch.WordTrace]
  refine ⟨113273637753641128615110509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75515758502427419076740339 113273637753641128615110509)
  ·
    refine ⟨42477614157615423230666441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113273637753641128615110509 42477614157615423230666441)
    ·
      refine ⟨31858210618211567422999831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42477614157615423230666441 31858210618211567422999831)
      ·
        refine ⟨47787315927317351134499747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31858210618211567422999831 47787315927317351134499747)
        ·
          refine ⟨71680973890976026701749621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47787315927317351134499747 71680973890976026701749621)
          ·
            refine ⟨6720091302279002503289027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71680973890976026701749621 6720091302279002503289027)
            ·
              refine ⟨10080136953418503754933541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6720091302279002503289027 10080136953418503754933541)
              ·
                refine ⟨1890025678765969454050039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10080136953418503754933541 1890025678765969454050039)
                ·
                  refine ⟨2835038518148954181075059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890025678765969454050039 2835038518148954181075059)
                  ·
                    refine ⟨4252557777223431271612589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2835038518148954181075059 4252557777223431271612589)
                    ·
                      refine ⟨1594709166458786726854721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252557777223431271612589 1594709166458786726854721)
                      ·
                        rfl

theorem cell23_3105685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_3105685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105685 prefixEnd_3105685 := by exact prefixLift 3105685
  have htrace : WordTrace (prefixWord ++ tailWord_3105685) baseStart_3105685 baseEnd_3105685 := by
    simpa [prefixWord, tailWord_3105685, baseEnd_3105685] using wordTrace_append hprefix tailTrace_3105685
  have hstable : (prefixWord ++ tailWord_3105685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105685).length < 2 ^ (prefixWord ++ tailWord_3105685).sum := by decide
  have hdescent : baseEnd_3105685 < baseStart_3105685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105708 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 3, 2, 2]
def baseStart_3105708 : Nat := 118140960795 + 3105708 * 2 ^ 59
def prefixEnd_3105708 : Nat := 4983230072969 + 3 ^ 40 * 3105708 * 2
def baseEnd_3105708 : Nat := 1594720976513840136867115

theorem tailTrace_3105708 : CollatzResearch.WordTrace tailWord_3105708 prefixEnd_3105708 1594720976513840136867115 := by
  unfold tailWord_3105708
  simp only [CollatzResearch.WordTrace]
  refine ⟨56637238316278901771598889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75516317755038535695465185 56637238316278901771598889)
  ·
    refine ⟨42477928737209176328699167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56637238316278901771598889 42477928737209176328699167)
    ·
      refine ⟨63716893105813764493048751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42477928737209176328699167 63716893105813764493048751)
      ·
        refine ⟨95575339658720646739573127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63716893105813764493048751 95575339658720646739573127)
        ·
          refine ⟨143363009488080970109359691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95575339658720646739573127 143363009488080970109359691)
          ·
            refine ⟨215044514232121455164039537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143363009488080970109359691 215044514232121455164039537)
            ·
              refine ⟨161283385674091091373029653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215044514232121455164039537 161283385674091091373029653)
              ·
                refine ⟨7560158703473019908110765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161283385674091091373029653 7560158703473019908110765)
                ·
                  refine ⟨2835059513802382465541537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7560158703473019908110765 2835059513802382465541537)
                  ·
                    refine ⟨2126294635351786849156153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2835059513802382465541537 2126294635351786849156153)
                    ·
                      refine ⟨1594720976513840136867115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126294635351786849156153 1594720976513840136867115)
                      ·
                        rfl

theorem cell23_3105708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_3105708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105708 prefixEnd_3105708 := by exact prefixLift 3105708
  have htrace : WordTrace (prefixWord ++ tailWord_3105708) baseStart_3105708 baseEnd_3105708 := by
    simpa [prefixWord, tailWord_3105708, baseEnd_3105708] using wordTrace_append hprefix tailTrace_3105708
  have hstable : (prefixWord ++ tailWord_3105708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105708).length < 2 ^ (prefixWord ++ tailWord_3105708).sum := by decide
  have hdescent : baseEnd_3105708 < baseStart_3105708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105721 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3105721 : Nat := 118140960795 + 3105721 * 2 ^ 59
def prefixEnd_3105721 : Nat := 4983230072969 + 3 ^ 40 * 3105721 * 2
def baseEnd_3105721 : Nat := 1594727651762348586004555

theorem tailTrace_3105721 : CollatzResearch.WordTrace tailWord_3105721 prefixEnd_3105721 1594727651762348586004555 := by
  unfold tailWord_3105721
  simp only [CollatzResearch.WordTrace]
  refine ⟨113274950781510706763421017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75516633854340471175614011 113274950781510706763421017)
  ·
    refine ⟨84956213086133030072565763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113274950781510706763421017 84956213086133030072565763)
    ·
      refine ⟨127434319629199545108848645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84956213086133030072565763 127434319629199545108848645)
      ·
        refine ⟨23893934930474914707909121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127434319629199545108848645 23893934930474914707909121)
        ·
          refine ⟨17920451197856186030931841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23893934930474914707909121 17920451197856186030931841)
          ·
            refine ⟨13440338398392139523198881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17920451197856186030931841 13440338398392139523198881)
            ·
              refine ⟨10080253798794104642399161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13440338398392139523198881 10080253798794104642399161)
              ·
                refine ⟨7560190349095578481799371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10080253798794104642399161 7560190349095578481799371)
                ·
                  refine ⟨11340285523643367722699057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7560190349095578481799371 11340285523643367722699057)
                  ·
                    refine ⟨8505214142732525792024293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11340285523643367722699057 8505214142732525792024293)
                    ·
                      refine ⟨1594727651762348586004555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8505214142732525792024293 1594727651762348586004555)
                      ·
                        rfl

theorem cell23_3105721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3105721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105721 prefixEnd_3105721 := by exact prefixLift 3105721
  have htrace : WordTrace (prefixWord ++ tailWord_3105721) baseStart_3105721 baseEnd_3105721 := by
    simpa [prefixWord, tailWord_3105721, baseEnd_3105721] using wordTrace_append hprefix tailTrace_3105721
  have hstable : (prefixWord ++ tailWord_3105721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105721).length < 2 ^ (prefixWord ++ tailWord_3105721).sum := by decide
  have hdescent : baseEnd_3105721 < baseStart_3105721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105728 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 3]
def baseStart_3105728 : Nat := 118140960795 + 3105728 * 2 ^ 59
def prefixEnd_3105728 : Nat := 4983230072969 + 3 ^ 40 * 3105728 * 2
def baseEnd_3105728 : Nat := 1594731246126930058617023

theorem tailTrace_3105728 : CollatzResearch.WordTrace tailWord_3105728 prefixEnd_3105728 1594731246126930058617023 := by
  unfold tailWord_3105728
  simp only [CollatzResearch.WordTrace]
  refine ⟨56637603046242673479462919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75516804061656897972617225 56637603046242673479462919)
  ·
    refine ⟨84956404569364010219194379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56637603046242673479462919 84956404569364010219194379)
    ·
      refine ⟨127434606854046015328791569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84956404569364010219194379 127434606854046015328791569)
      ·
        refine ⟨95575955140534511496593677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127434606854046015328791569 95575955140534511496593677)
        ·
          refine ⟨35840983177700441811222629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95575955140534511496593677 35840983177700441811222629)
          ·
            refine ⟨6720184345818832839604243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35840983177700441811222629 6720184345818832839604243)
            ·
              refine ⟨10080276518728249259406365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6720184345818832839604243 10080276518728249259406365)
              ·
                refine ⟨3780103694523093472277387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10080276518728249259406365 3780103694523093472277387)
                ·
                  refine ⟨5670155541784640208416081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780103694523093472277387 5670155541784640208416081)
                  ·
                    refine ⟨4252616656338480156312061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5670155541784640208416081 4252616656338480156312061)
                    ·
                      refine ⟨1594731246126930058617023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252616656338480156312061 1594731246126930058617023)
                      ·
                        rfl

theorem cell23_3105728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_3105728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105728 prefixEnd_3105728 := by exact prefixLift 3105728
  have htrace : WordTrace (prefixWord ++ tailWord_3105728) baseStart_3105728 baseEnd_3105728 := by
    simpa [prefixWord, tailWord_3105728, baseEnd_3105728] using wordTrace_append hprefix tailTrace_3105728
  have hstable : (prefixWord ++ tailWord_3105728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105728).length < 2 ^ (prefixWord ++ tailWord_3105728).sum := by decide
  have hdescent : baseEnd_3105728 < baseStart_3105728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105742 : List Nat := [4, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2]
def baseStart_3105742 : Nat := 118140960795 + 3105742 * 2 ^ 59
def prefixEnd_3105742 : Nat := 4983230072969 + 3 ^ 40 * 3105742 * 2
def baseEnd_3105742 : Nat := 1594738434856093003841959

theorem tailTrace_3105742 : CollatzResearch.WordTrace tailWord_3105742 prefixEnd_3105742 1594738434856093003841959 := by
  unfold tailWord_3105742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159464589304328418741935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75517144476289751566623653 14159464589304328418741935)
  ·
    refine ⟨21239196883956492628112903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14159464589304328418741935 21239196883956492628112903)
    ·
      refine ⟨31858795325934738942169355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21239196883956492628112903 31858795325934738942169355)
      ·
        refine ⟨47788192988902108413254033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31858795325934738942169355 47788192988902108413254033)
        ·
          refine ⟨35841144741676581309940525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47788192988902108413254033 35841144741676581309940525)
          ·
            refine ⟨13440429278128717991227697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35841144741676581309940525 13440429278128717991227697)
            ·
              refine ⟨10080321958596538493420773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13440429278128717991227697 10080321958596538493420773)
              ·
                refine ⟨1890060367236850967516395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10080321958596538493420773 1890060367236850967516395)
                ·
                  refine ⟨2835090550855276451274593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890060367236850967516395 2835090550855276451274593)
                  ·
                    refine ⟨2126317913141457338455945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2835090550855276451274593 2126317913141457338455945)
                    ·
                      refine ⟨1594738434856093003841959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126317913141457338455945 1594738434856093003841959)
                      ·
                        rfl

theorem cell23_3105742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_3105742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105742 prefixEnd_3105742 := by exact prefixLift 3105742
  have htrace : WordTrace (prefixWord ++ tailWord_3105742) baseStart_3105742 baseEnd_3105742 := by
    simpa [prefixWord, tailWord_3105742, baseEnd_3105742] using wordTrace_append hprefix tailTrace_3105742
  have hstable : (prefixWord ++ tailWord_3105742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105742).length < 2 ^ (prefixWord ++ tailWord_3105742).sum := by decide
  have hdescent : baseEnd_3105742 < baseStart_3105742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105751 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 2, 7, 2]
def baseStart_3105751 : Nat := 118140960795 + 3105751 * 2 ^ 59
def prefixEnd_3105751 : Nat := 4983230072969 + 3 ^ 40 * 3105751 * 2
def baseEnd_3105751 : Nat := 1594743056181983468629417

theorem tailTrace_3105751 : CollatzResearch.WordTrace tailWord_3105751 prefixEnd_3105751 1594743056181983468629417 := by
  unfold tailWord_3105751
  simp only [CollatzResearch.WordTrace]
  refine ⟨113276044971402021887013107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75517363314268014591342071 113276044971402021887013107)
  ·
    refine ⟨169914067457103032830519661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113276044971402021887013107 169914067457103032830519661)
    ·
      refine ⟨63717775296413637311444873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169914067457103032830519661 63717775296413637311444873)
      ·
        refine ⟨47788331472310227983583655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63717775296413637311444873 47788331472310227983583655)
        ·
          refine ⟨71682497208465341975375483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47788331472310227983583655 71682497208465341975375483)
          ·
            refine ⟨107523745812698012963063225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71682497208465341975375483 107523745812698012963063225)
            ·
              refine ⟨80642809359523509722297419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107523745812698012963063225 80642809359523509722297419)
              ·
                refine ⟨120964214039285264583446129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80642809359523509722297419 120964214039285264583446129)
                ·
                  refine ⟨90723160529463948437584597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120964214039285264583446129 90723160529463948437584597)
                  ·
                    refine ⟨2126324074909311291505889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 90723160529463948437584597 2126324074909311291505889)
                    ·
                      refine ⟨1594743056181983468629417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126324074909311291505889 1594743056181983468629417)
                      ·
                        rfl

theorem cell23_3105751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_3105751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105751 prefixEnd_3105751 := by exact prefixLift 3105751
  have htrace : WordTrace (prefixWord ++ tailWord_3105751) baseStart_3105751 baseEnd_3105751 := by
    simpa [prefixWord, tailWord_3105751, baseEnd_3105751] using wordTrace_append hprefix tailTrace_3105751
  have hstable : (prefixWord ++ tailWord_3105751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105751).length < 2 ^ (prefixWord ++ tailWord_3105751).sum := by decide
  have hdescent : baseEnd_3105751 < baseStart_3105751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105762 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3105762 : Nat := 118140960795 + 3105762 * 2 ^ 59
def prefixEnd_3105762 : Nat := 4983230072969 + 3 ^ 40 * 3105762 * 2
def baseEnd_3105762 : Nat := 1594748704469182925591867

theorem tailTrace_3105762 : CollatzResearch.WordTrace tailWord_3105762 prefixEnd_3105762 1594748704469182925591867 := by
  unfold tailWord_3105762
  simp only [CollatzResearch.WordTrace]
  refine ⟨28319111543590542691415885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75517630782908113843775693 28319111543590542691415885)
  ·
    refine ⟨10619666828846453509280957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28319111543590542691415885 10619666828846453509280957)
    ·
      refine ⟨3982375060817420065980359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10619666828846453509280957 3982375060817420065980359)
      ·
        refine ⟨5973562591226130098970539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3982375060817420065980359 5973562591226130098970539)
        ·
          refine ⟨8960343886839195148455809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5973562591226130098970539 8960343886839195148455809)
          ·
            refine ⟨6720257915129396361341857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8960343886839195148455809 6720257915129396361341857)
            ·
              refine ⟨5040193436347047271006393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720257915129396361341857 5040193436347047271006393)
              ·
                refine ⟨3780145077260285453254795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5040193436347047271006393 3780145077260285453254795)
                ·
                  refine ⟨5670217615890428179882193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780145077260285453254795 5670217615890428179882193)
                  ·
                    refine ⟨4252663211917821134911645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5670217615890428179882193 4252663211917821134911645)
                    ·
                      refine ⟨1594748704469182925591867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4252663211917821134911645 1594748704469182925591867)
                      ·
                        rfl

theorem cell23_3105762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3105762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105762 prefixEnd_3105762 := by exact prefixLift 3105762
  have htrace : WordTrace (prefixWord ++ tailWord_3105762) baseStart_3105762 baseEnd_3105762 := by
    simpa [prefixWord, tailWord_3105762, baseEnd_3105762] using wordTrace_append hprefix tailTrace_3105762
  have hstable : (prefixWord ++ tailWord_3105762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105762).length < 2 ^ (prefixWord ++ tailWord_3105762).sum := by decide
  have hdescent : baseEnd_3105762 < baseStart_3105762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105764 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_3105764 : Nat := 118140960795 + 3105764 * 2 ^ 59
def prefixEnd_3105764 : Nat := 4983230072969 + 3 ^ 40 * 3105764 * 2
def baseEnd_3105764 : Nat := 1594749731430491917766857

theorem tailTrace_3105764 : CollatzResearch.WordTrace tailWord_3105764 prefixEnd_3105764 1594749731430491917766857 := by
  unfold tailWord_3105764
  simp only [CollatzResearch.WordTrace]
  refine ⟨56638259560177462553618173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75517679413569950071490897 56638259560177462553618173)
  ·
    refine ⟨21239347335066548457606815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56638259560177462553618173 21239347335066548457606815)
    ·
      refine ⟨31859021002599822686410223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21239347335066548457606815 31859021002599822686410223)
      ·
        refine ⟨47788531503899734029615335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31859021002599822686410223 47788531503899734029615335)
        ·
          refine ⟨71682797255849601044423003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47788531503899734029615335 71682797255849601044423003)
          ·
            refine ⟨107524195883774401566634505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71682797255849601044423003 107524195883774401566634505)
            ·
              refine ⟨80643146912830801174975879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107524195883774401566634505 80643146912830801174975879)
              ·
                refine ⟨120964720369246201762463819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80643146912830801174975879 120964720369246201762463819)
                ·
                  refine ⟨181447080553869302643695729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120964720369246201762463819 181447080553869302643695729)
                  ·
                    refine ⟨136085310415401976982771797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181447080553869302643695729 136085310415401976982771797)
                    ·
                      refine ⟨1594749731430491917766857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 136085310415401976982771797 1594749731430491917766857)
                      ·
                        rfl

theorem cell23_3105764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_3105764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105764 prefixEnd_3105764 := by exact prefixLift 3105764
  have htrace : WordTrace (prefixWord ++ tailWord_3105764) baseStart_3105764 baseEnd_3105764 := by
    simpa [prefixWord, tailWord_3105764, baseEnd_3105764] using wordTrace_append hprefix tailTrace_3105764
  have hstable : (prefixWord ++ tailWord_3105764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105764).length < 2 ^ (prefixWord ++ tailWord_3105764).sum := by decide
  have hdescent : baseEnd_3105764 < baseStart_3105764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105765 : List Nat := [1, 3, 1, 6, 1, 2, 2, 7]
def baseStart_3105765 : Nat := 118140960795 + 3105765 * 2 ^ 59
def prefixEnd_3105765 : Nat := 4983230072969 + 3 ^ 40 * 3105765 * 2
def baseEnd_3105765 : Nat := 59064823885598015327939

theorem tailTrace_3105765 : CollatzResearch.WordTrace tailWord_3105765 prefixEnd_3105765 59064823885598015327939 := by
  unfold tailWord_3105765
  simp only [CollatzResearch.WordTrace]
  refine ⟨113276555593351302278022749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75517703728900868185348499 113276555593351302278022749)
  ·
    refine ⟨42478708347506738354258531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113276555593351302278022749 42478708347506738354258531)
    ·
      refine ⟨63718062521260107531387797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42478708347506738354258531 63718062521260107531387797)
      ·
        refine ⟨2986784180684067540533803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63718062521260107531387797 2986784180684067540533803)
        ·
          refine ⟨4480176271026101310800705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986784180684067540533803 4480176271026101310800705)
          ·
            refine ⟨3360132203269575983100529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4480176271026101310800705 3360132203269575983100529)
            ·
              refine ⟨2520099152452181987325397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360132203269575983100529 2520099152452181987325397)
              ·
                refine ⟨59064823885598015327939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2520099152452181987325397 59064823885598015327939)
                ·
                  rfl

theorem cell23_3105765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 7].length) (baseStart_3105765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105765 prefixEnd_3105765 := by exact prefixLift 3105765
  have htrace : WordTrace (prefixWord ++ tailWord_3105765) baseStart_3105765 baseEnd_3105765 := by
    simpa [prefixWord, tailWord_3105765, baseEnd_3105765] using wordTrace_append hprefix tailTrace_3105765
  have hstable : (prefixWord ++ tailWord_3105765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105765).length < 2 ^ (prefixWord ++ tailWord_3105765).sum := by decide
  have hdescent : baseEnd_3105765 < baseStart_3105765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105768 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_3105768 : Nat := 118140960795 + 3105768 * 2 ^ 59
def prefixEnd_3105768 : Nat := 4983230072969 + 3 ^ 40 * 3105768 * 2
def baseEnd_3105768 : Nat := 1594751785353109902116839

theorem tailTrace_3105768 : CollatzResearch.WordTrace tailWord_3105768 prefixEnd_3105768 1594751785353109902116839 := by
  unfold tailWord_3105768
  simp only [CollatzResearch.WordTrace]
  refine ⟨56638332506170216895190979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75517776674893622526921305 56638332506170216895190979)
  ·
    refine ⟨84957498759255325342786469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56638332506170216895190979 84957498759255325342786469)
    ·
      refine ⟨15929531017360373501772463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84957498759255325342786469 15929531017360373501772463)
      ·
        refine ⟨23894296526040560252658695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15929531017360373501772463 23894296526040560252658695)
        ·
          refine ⟨35841444789060840378988043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23894296526040560252658695 35841444789060840378988043)
          ·
            refine ⟨53762167183591260568482065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35841444789060840378988043 53762167183591260568482065)
            ·
              refine ⟨40321625387693445426361549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53762167183591260568482065 40321625387693445426361549)
              ·
                refine ⟨15120609520385042034885581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40321625387693445426361549 15120609520385042034885581)
                ·
                  refine ⟨5670228570144390763082093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15120609520385042034885581 5670228570144390763082093)
                  ·
                    refine ⟨2126335713804146536155785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5670228570144390763082093 2126335713804146536155785)
                    ·
                      refine ⟨1594751785353109902116839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126335713804146536155785 1594751785353109902116839)
                      ·
                        rfl

theorem cell23_3105768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_3105768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105768 prefixEnd_3105768 := by exact prefixLift 3105768
  have htrace : WordTrace (prefixWord ++ tailWord_3105768) baseStart_3105768 baseEnd_3105768 := by
    simpa [prefixWord, tailWord_3105768, baseEnd_3105768] using wordTrace_append hprefix tailTrace_3105768
  have hstable : (prefixWord ++ tailWord_3105768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105768).length < 2 ^ (prefixWord ++ tailWord_3105768).sum := by decide
  have hdescent : baseEnd_3105768 < baseStart_3105768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105861 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_3105861 : Nat := 118140960795 + 3105861 * 2 ^ 59
def prefixEnd_3105861 : Nat := 4983230072969 + 3 ^ 40 * 3105861 * 2
def baseEnd_3105861 : Nat := 1594799539053978038253911

theorem tailTrace_3105861 : CollatzResearch.WordTrace tailWord_3105861 prefixEnd_3105861 1594799539053978038253911 := by
  unfold tailWord_3105861
  simp only [CollatzResearch.WordTrace]
  refine ⟨113280057001003510673517437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75520038000669007115678291 113280057001003510673517437)
  ·
    refine ⟨42480021375376316502569039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113280057001003510673517437 42480021375376316502569039)
    ·
      refine ⟨63720032063064474753853559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42480021375376316502569039 63720032063064474753853559)
      ·
        refine ⟨95580048094596712130780339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63720032063064474753853559 95580048094596712130780339)
        ·
          refine ⟨143370072141895068196170509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95580048094596712130780339 143370072141895068196170509)
          ·
            refine ⟨53763777053210650573563941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143370072141895068196170509 53763777053210650573563941)
            ·
              refine ⟨10080708197476996982543239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53763777053210650573563941 10080708197476996982543239)
              ·
                refine ⟨15121062296215495473814859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10080708197476996982543239 15121062296215495473814859)
                ·
                  refine ⟨22681593444323243210722289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15121062296215495473814859 22681593444323243210722289)
                  ·
                    refine ⟨17011195083242432408041717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22681593444323243210722289 17011195083242432408041717)
                    ·
                      refine ⟨1594799539053978038253911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17011195083242432408041717 1594799539053978038253911)
                      ·
                        rfl

theorem cell23_3105861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_3105861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105861 prefixEnd_3105861 := by exact prefixLift 3105861
  have htrace : WordTrace (prefixWord ++ tailWord_3105861) baseStart_3105861 baseEnd_3105861 := by
    simpa [prefixWord, tailWord_3105861, baseEnd_3105861] using wordTrace_append hprefix tailTrace_3105861
  have hstable : (prefixWord ++ tailWord_3105861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105861).length < 2 ^ (prefixWord ++ tailWord_3105861).sum := by decide
  have hdescent : baseEnd_3105861 < baseStart_3105861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105885 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3105885 : Nat := 118140960795 + 3105885 * 2 ^ 59
def prefixEnd_3105885 : Nat := 4983230072969 + 3 ^ 40 * 3105885 * 2
def baseEnd_3105885 : Nat := 531603954196561981451267

theorem tailTrace_3105885 : CollatzResearch.WordTrace tailWord_3105885 prefixEnd_3105885 531603954196561981451267 := by
  unfold tailWord_3105885
  simp only [CollatzResearch.WordTrace]
  refine ⟨113280932352916562772391109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75520621568611041848260739 113280932352916562772391109)
  ·
    refine ⟨21240174816171855519823333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113280932352916562772391109 21240174816171855519823333)
    ·
      refine ⟨3982532778032222909966875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21240174816171855519823333 3982532778032222909966875)
      ·
        refine ⟨5973799167048334364950313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3982532778032222909966875 5973799167048334364950313)
        ·
          refine ⟨4480349375286250773712735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5973799167048334364950313 4480349375286250773712735)
          ·
            refine ⟨6720524062929376160569103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480349375286250773712735 6720524062929376160569103)
            ·
              refine ⟨10080786094394064240853655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6720524062929376160569103 10080786094394064240853655)
              ·
                refine ⟨15121179141591096361280483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10080786094394064240853655 15121179141591096361280483)
                ·
                  refine ⟨22681768712386644541920725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15121179141591096361280483 22681768712386644541920725)
                  ·
                    refine ⟨531603954196561981451267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22681768712386644541920725 531603954196561981451267)
                    ·
                      rfl

theorem cell23_3105885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3105885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105885 prefixEnd_3105885 := by exact prefixLift 3105885
  have htrace : WordTrace (prefixWord ++ tailWord_3105885) baseStart_3105885 baseEnd_3105885 := by
    simpa [prefixWord, tailWord_3105885, baseEnd_3105885] using wordTrace_append hprefix tailTrace_3105885
  have hstable : (prefixWord ++ tailWord_3105885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105885).length < 2 ^ (prefixWord ++ tailWord_3105885).sum := by decide
  have hdescent : baseEnd_3105885 < baseStart_3105885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105888 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 1, 6, 2]
def baseStart_3105888 : Nat := 118140960795 + 3105888 * 2 ^ 59
def prefixEnd_3105888 : Nat := 4983230072969 + 3 ^ 40 * 3105888 * 2
def baseEnd_3105888 : Nat := 1594813403031649432616287

theorem tailTrace_3105888 : CollatzResearch.WordTrace tailWord_3105888 prefixEnd_3105888 1594813403031649432616287 := by
  unfold tailWord_3105888
  simp only [CollatzResearch.WordTrace]
  refine ⟨56640520885952847142375159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75520694514603796189833545 56640520885952847142375159)
  ·
    refine ⟨84960781328929270713562739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56640520885952847142375159 84960781328929270713562739)
    ·
      refine ⟨127441171993393906070344109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84960781328929270713562739 127441171993393906070344109)
      ·
        refine ⟨47790439497522714776379041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127441171993393906070344109 47790439497522714776379041)
        ·
          refine ⟨35842829623142036082284281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47790439497522714776379041 35842829623142036082284281)
          ·
            refine ⟨26882122217356527061713211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35842829623142036082284281 26882122217356527061713211)
            ·
              refine ⟨40323183326034790592569817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26882122217356527061713211 40323183326034790592569817)
              ·
                refine ⟨30242387494526092944427363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40323183326034790592569817 30242387494526092944427363)
                ·
                  refine ⟨45363581241789139416641045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30242387494526092944427363 45363581241789139416641045)
                  ·
                    refine ⟨2126417870708865910155049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45363581241789139416641045 2126417870708865910155049)
                    ·
                      refine ⟨1594813403031649432616287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126417870708865910155049 1594813403031649432616287)
                      ·
                        rfl

theorem cell23_3105888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_3105888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105888 prefixEnd_3105888 := by exact prefixLift 3105888
  have htrace : WordTrace (prefixWord ++ tailWord_3105888) baseStart_3105888 baseEnd_3105888 := by
    simpa [prefixWord, tailWord_3105888, baseEnd_3105888] using wordTrace_append hprefix tailTrace_3105888
  have hstable : (prefixWord ++ tailWord_3105888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105888).length < 2 ^ (prefixWord ++ tailWord_3105888).sum := by decide
  have hdescent : baseEnd_3105888 < baseStart_3105888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105911 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 8]
def baseStart_3105911 : Nat := 118140960795 + 3105911 * 2 ^ 59
def prefixEnd_3105911 : Nat := 4983230072969 + 3 ^ 40 * 3105911 * 2
def baseEnd_3105911 : Nat := 177202801454078093625409

theorem tailTrace_3105911 : CollatzResearch.WordTrace tailWord_3105911 prefixEnd_3105911 177202801454078093625409 := by
  unfold tailWord_3105911
  simp only [CollatzResearch.WordTrace]
  refine ⟨113281880650822369212837587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75521253767214912808558391 113281880650822369212837587)
  ·
    refine ⟨169922820976233553819256381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113281880650822369212837587 169922820976233553819256381)
    ·
      refine ⟨63721057866087582682221143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169922820976233553819256381 63721057866087582682221143)
      ·
        refine ⟨95581586799131374023331715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63721057866087582682221143 95581586799131374023331715)
        ·
          refine ⟨143372380198697061034997573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95581586799131374023331715 143372380198697061034997573)
          ·
            refine ⟨26882321287255698944062045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143372380198697061034997573 26882321287255698944062045)
            ·
              refine ⟨10080870482720887104023267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26882321287255698944062045 10080870482720887104023267)
              ·
                refine ⟨15121305724081330656034901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10080870482720887104023267 15121305724081330656034901)
                ·
                  refine ⟨177202801454078093625409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15121305724081330656034901 177202801454078093625409)
                  ·
                    rfl

theorem cell23_3105911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 8].length) (baseStart_3105911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105911 prefixEnd_3105911 := by exact prefixLift 3105911
  have htrace : WordTrace (prefixWord ++ tailWord_3105911) baseStart_3105911 baseEnd_3105911 := by
    simpa [prefixWord, tailWord_3105911, baseEnd_3105911] using wordTrace_append hprefix tailTrace_3105911
  have hstable : (prefixWord ++ tailWord_3105911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105911).length < 2 ^ (prefixWord ++ tailWord_3105911).sum := by decide
  have hdescent : baseEnd_3105911 < baseStart_3105911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105978 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_3105978 : Nat := 118140960795 + 3105978 * 2 ^ 59
def prefixEnd_3105978 : Nat := 4983230072969 + 3 ^ 40 * 3105978 * 2
def baseEnd_3105978 : Nat := 1594859616290554080490873

theorem tailTrace_3105978 : CollatzResearch.WordTrace tailWord_3105978 prefixEnd_3105978 1594859616290554080490873 := by
  unfold tailWord_3105978
  simp only [CollatzResearch.WordTrace]
  refine ⟨28321081085394909913881647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75522882894386426437017725 28321081085394909913881647)
  ·
    refine ⟨42481621628092364870822471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28321081085394909913881647 42481621628092364870822471)
    ·
      refine ⟨63722432442138547306233707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42481621628092364870822471 63722432442138547306233707)
      ·
        refine ⟨95583648663207820959350561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63722432442138547306233707 95583648663207820959350561)
        ·
          refine ⟨71687736497405865719512921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95583648663207820959350561 71687736497405865719512921)
          ·
            refine ⟨53765802373054399289634691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71687736497405865719512921 53765802373054399289634691)
            ·
              refine ⟨80648703559581598934452037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53765802373054399289634691 80648703559581598934452037)
              ·
                refine ⟨15121631917421549800209757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80648703559581598934452037 15121631917421549800209757)
                ·
                  refine ⟨5670611969033081175078659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15121631917421549800209757 5670611969033081175078659)
                  ·
                    refine ⟨8505917953549621762617989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5670611969033081175078659 8505917953549621762617989)
                    ·
                      refine ⟨1594859616290554080490873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8505917953549621762617989 1594859616290554080490873)
                      ·
                        rfl

theorem cell23_3105978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_3105978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3105978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3105978 prefixEnd_3105978 := by exact prefixLift 3105978
  have htrace : WordTrace (prefixWord ++ tailWord_3105978) baseStart_3105978 baseEnd_3105978 := by
    simpa [prefixWord, tailWord_3105978, baseEnd_3105978] using wordTrace_append hprefix tailTrace_3105978
  have hstable : (prefixWord ++ tailWord_3105978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105978).length < 2 ^ (prefixWord ++ tailWord_3105978).sum := by decide
  have hdescent : baseEnd_3105978 < baseStart_3105978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106005 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_3106005 : Nat := 118140960795 + 3106005 * 2 ^ 59
def prefixEnd_3106005 : Nat := 4983230072969 + 3 ^ 40 * 3106005 * 2
def baseEnd_3106005 : Nat := 531624493422741824951083

theorem tailTrace_3106005 : CollatzResearch.WordTrace tailWord_3106005 prefixEnd_3106005 531624493422741824951083 := by
  unfold tailWord_3106005
  simp only [CollatzResearch.WordTrace]
  refine ⟨113285309112481823266759469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75523539408321215511172979 113285309112481823266759469)
  ·
    refine ⟨42481990917180683725034801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113285309112481823266759469 42481990917180683725034801)
    ·
      refine ⟨31861493187885512793776101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42481990917180683725034801 31861493187885512793776101)
      ·
        refine ⟨5974029972728533648833019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31861493187885512793776101 5974029972728533648833019)
        ·
          refine ⟨8961044959092800473249529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5974029972728533648833019 8961044959092800473249529)
          ·
            refine ⟨6720783719319600354937147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8961044959092800473249529 6720783719319600354937147)
            ·
              refine ⟨10081175578979400532405721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6720783719319600354937147 10081175578979400532405721)
              ·
                refine ⟨7560881684234550399304291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10081175578979400532405721 7560881684234550399304291)
                ·
                  refine ⟨11341322526351825598956437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7560881684234550399304291 11341322526351825598956437)
                  ·
                    refine ⟨531624493422741824951083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11341322526351825598956437 531624493422741824951083)
                    ·
                      rfl

theorem cell23_3106005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_3106005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106005 prefixEnd_3106005 := by exact prefixLift 3106005
  have htrace : WordTrace (prefixWord ++ tailWord_3106005) baseStart_3106005 baseEnd_3106005 := by
    simpa [prefixWord, tailWord_3106005, baseEnd_3106005] using wordTrace_append hprefix tailTrace_3106005
  have hstable : (prefixWord ++ tailWord_3106005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106005).length < 2 ^ (prefixWord ++ tailWord_3106005).sum := by decide
  have hdescent : baseEnd_3106005 < baseStart_3106005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106011 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 7]
def baseStart_3106011 : Nat := 118140960795 + 3106011 * 2 ^ 59
def prefixEnd_3106011 : Nat := 4983230072969 + 3 ^ 40 * 3106011 * 2
def baseEnd_3106011 : Nat := 1594876561152152451378221

theorem tailTrace_3106011 : CollatzResearch.WordTrace tailWord_3106011 prefixEnd_3106011 1594876561152152451378221 := by
  unfold tailWord_3106011
  simp only [CollatzResearch.WordTrace]
  refine ⟨113285527950460086291477887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75523685300306724194318591 113285527950460086291477887)
  ·
    refine ⟨169928291925690129437216831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113285527950460086291477887 169928291925690129437216831)
    ·
      refine ⟨254892437888535194155825247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169928291925690129437216831 254892437888535194155825247)
      ·
        refine ⟨382338656832802791233737871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254892437888535194155825247 382338656832802791233737871)
        ·
          refine ⟨573507985249204186850606807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382338656832802791233737871 573507985249204186850606807)
          ·
            refine ⟨860261977873806280275910211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573507985249204186850606807 860261977873806280275910211)
            ·
              refine ⟨1290392966810709420413865317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860261977873806280275910211 1290392966810709420413865317)
              ·
                refine ⟨241948681277008016327599747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1290392966810709420413865317 241948681277008016327599747)
                ·
                  refine ⟨362923021915512024491399621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241948681277008016327599747 362923021915512024491399621)
                  ·
                    refine ⟨68048066609158504592137429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 362923021915512024491399621 68048066609158504592137429)
                    ·
                      refine ⟨1594876561152152451378221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68048066609158504592137429 1594876561152152451378221)
                      ·
                        rfl

theorem cell23_3106011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_3106011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106011 prefixEnd_3106011 := by exact prefixLift 3106011
  have htrace : WordTrace (prefixWord ++ tailWord_3106011) baseStart_3106011 baseEnd_3106011 := by
    simpa [prefixWord, tailWord_3106011, baseEnd_3106011] using wordTrace_append hprefix tailTrace_3106011
  have hstable : (prefixWord ++ tailWord_3106011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106011).length < 2 ^ (prefixWord ++ tailWord_3106011).sum := by decide
  have hdescent : baseEnd_3106011 < baseStart_3106011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106015 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 3]
def baseStart_3106015 : Nat := 118140960795 + 3106015 * 2 ^ 59
def prefixEnd_3106015 : Nat := 4983230072969 + 3 ^ 40 * 3106015 * 2
def baseEnd_3106015 : Nat := 1594878615074770435728203

theorem tailTrace_3106015 : CollatzResearch.WordTrace tailWord_3106015 prefixEnd_3106015 1594878615074770435728203 := by
  unfold tailWord_3106015
  simp only [CollatzResearch.WordTrace]
  refine ⟨113285673842445594974623499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75523782561630396649748999 113285673842445594974623499)
  ·
    refine ⟨169928510763668392461935249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113285673842445594974623499 169928510763668392461935249)
    ·
      refine ⟨127446383072751294346451437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169928510763668392461935249 127446383072751294346451437)
      ·
        refine ⟨47792393652281735379919289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127446383072751294346451437 47792393652281735379919289)
        ·
          refine ⟨35844295239211301534939467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47792393652281735379919289 35844295239211301534939467)
          ·
            refine ⟨53766442858816952302409201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35844295239211301534939467 53766442858816952302409201)
            ·
              refine ⟨40324832144112714226806901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53766442858816952302409201 40324832144112714226806901)
              ·
                refine ⟨3780453013510566958763147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40324832144112714226806901 3780453013510566958763147)
                ·
                  refine ⟨5670679520265850438144721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780453013510566958763147 5670679520265850438144721)
                  ·
                    refine ⟨4253009640199387828608541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5670679520265850438144721 4253009640199387828608541)
                    ·
                      refine ⟨1594878615074770435728203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4253009640199387828608541 1594878615074770435728203)
                      ·
                        rfl

theorem cell23_3106015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_3106015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106015 prefixEnd_3106015 := by exact prefixLift 3106015
  have htrace : WordTrace (prefixWord ++ tailWord_3106015) baseStart_3106015 baseEnd_3106015 := by
    simpa [prefixWord, tailWord_3106015, baseEnd_3106015] using wordTrace_append hprefix tailTrace_3106015
  have hstable : (prefixWord ++ tailWord_3106015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106015).length < 2 ^ (prefixWord ++ tailWord_3106015).sum := by decide
  have hdescent : baseEnd_3106015 < baseStart_3106015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106023 : List Nat := [1, 1, 5, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3106023 : Nat := 118140960795 + 3106023 * 2 ^ 59
def prefixEnd_3106023 : Nat := 4983230072969 + 3 ^ 40 * 3106023 * 2
def baseEnd_3106023 : Nat := 1594882722920006404428167

theorem tailTrace_3106023 : CollatzResearch.WordTrace tailWord_3106023 prefixEnd_3106023 1594882722920006404428167 := by
  unfold tailWord_3106023
  simp only [CollatzResearch.WordTrace]
  refine ⟨113285965626416612340914723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75523977084277741560609815 113285965626416612340914723)
  ·
    refine ⟨169928948439624918511372085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113285965626416612340914723 169928948439624918511372085)
    ·
      refine ⟨15930838916214836110441133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169928948439624918511372085 15930838916214836110441133)
      ·
        refine ⟨5974064593580563541415425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15930838916214836110441133 5974064593580563541415425)
        ·
          refine ⟨4480548445185422656061569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5974064593580563541415425 4480548445185422656061569)
          ·
            refine ⟨3360411333889066992046177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4480548445185422656061569 3360411333889066992046177)
            ·
              refine ⟨2520308500416800244034633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360411333889066992046177 2520308500416800244034633)
              ·
                refine ⟨1890231375312600183025975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520308500416800244034633 1890231375312600183025975)
                ·
                  refine ⟨2835347062968900274538963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890231375312600183025975 2835347062968900274538963)
                  ·
                    refine ⟨4253020594453350411808445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2835347062968900274538963 4253020594453350411808445)
                    ·
                      refine ⟨1594882722920006404428167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4253020594453350411808445 1594882722920006404428167)
                      ·
                        rfl

theorem cell23_3106023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3106023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106023 prefixEnd_3106023 := by exact prefixLift 3106023
  have htrace : WordTrace (prefixWord ++ tailWord_3106023) baseStart_3106023 baseEnd_3106023 := by
    simpa [prefixWord, tailWord_3106023, baseEnd_3106023] using wordTrace_append hprefix tailTrace_3106023
  have hstable : (prefixWord ++ tailWord_3106023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106023).length < 2 ^ (prefixWord ++ tailWord_3106023).sum := by decide
  have hdescent : baseEnd_3106023 < baseStart_3106023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106045 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_3106045 : Nat := 118140960795 + 3106045 * 2 ^ 59
def prefixEnd_3106045 : Nat := 4983230072969 + 3 ^ 40 * 3106045 * 2
def baseEnd_3106045 : Nat := 1594894019494405318353065

theorem tailTrace_3106045 : CollatzResearch.WordTrace tailWord_3106045 prefixEnd_3106045 1594894019494405318353065 := by
  unfold tailWord_3106045
  simp only [CollatzResearch.WordTrace]
  refine ⟨113286768032336910098215589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75524512021557940065477059 113286768032336910098215589)
  ·
    refine ⟨21241269006063170643415423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113286768032336910098215589 21241269006063170643415423)
    ·
      refine ⟨31861903509094755965123135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21241269006063170643415423 31861903509094755965123135)
      ·
        refine ⟨47792855263642133947684703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31861903509094755965123135 47792855263642133947684703)
        ·
          refine ⟨71689282895463200921527055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47792855263642133947684703 71689282895463200921527055)
          ·
            refine ⟨107533924343194801382290583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71689282895463200921527055 107533924343194801382290583)
            ·
              refine ⟨161300886514792202073435875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107533924343194801382290583 161300886514792202073435875)
              ·
                refine ⟨241951329772188303110153813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161300886514792202073435875 241951329772188303110153813)
                ·
                  refine ⟨2835367145767831677072115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 241951329772188303110153813 2835367145767831677072115)
                  ·
                    refine ⟨4253050718651747515608173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2835367145767831677072115 4253050718651747515608173)
                    ·
                      refine ⟨1594894019494405318353065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4253050718651747515608173 1594894019494405318353065)
                      ·
                        rfl

theorem cell23_3106045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_3106045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106045 prefixEnd_3106045 := by exact prefixLift 3106045
  have htrace : WordTrace (prefixWord ++ tailWord_3106045) baseStart_3106045 baseEnd_3106045 := by
    simpa [prefixWord, tailWord_3106045, baseEnd_3106045] using wordTrace_append hprefix tailTrace_3106045
  have hstable : (prefixWord ++ tailWord_3106045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106045).length < 2 ^ (prefixWord ++ tailWord_3106045).sum := by decide
  have hdescent : baseEnd_3106045 < baseStart_3106045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106058 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3106058 : Nat := 118140960795 + 3106058 * 2 ^ 59
def prefixEnd_3106058 : Nat := 4983230072969 + 3 ^ 40 * 3106058 * 2
def baseEnd_3106058 : Nat := 1594900694742913767490505

theorem tailTrace_3106058 : CollatzResearch.WordTrace tailWord_3106058 prefixEnd_3106058 1594900694742913767490505 := by
  unfold tailWord_3106058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28321810545322453329609707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75524828120859875545625885 28321810545322453329609707)
  ·
    refine ⟨42482715817983679994414561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28321810545322453329609707 42482715817983679994414561)
    ·
      refine ⟨31862036863487759995810921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42482715817983679994414561 31862036863487759995810921)
      ·
        refine ⟨23896527647615819996858191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31862036863487759995810921 23896527647615819996858191)
        ·
          refine ⟨35844791471423729995287287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23896527647615819996858191 35844791471423729995287287)
          ·
            refine ⟨53767187207135594992930931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35844791471423729995287287 53767187207135594992930931)
            ·
              refine ⟨80650780810703392489396397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53767187207135594992930931 80650780810703392489396397)
              ·
                refine ⟨30244042804013772183523649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80650780810703392489396397 30244042804013772183523649)
                ·
                  refine ⟨22683032103010329137642737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30244042804013772183523649 22683032103010329137642737)
                  ·
                    refine ⟨17012274077257746853232053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22683032103010329137642737 17012274077257746853232053)
                    ·
                      refine ⟨1594900694742913767490505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17012274077257746853232053 1594900694742913767490505)
                      ·
                        rfl

theorem cell23_3106058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3106058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106058 prefixEnd_3106058 := by exact prefixLift 3106058
  have htrace : WordTrace (prefixWord ++ tailWord_3106058) baseStart_3106058 baseEnd_3106058 := by
    simpa [prefixWord, tailWord_3106058, baseEnd_3106058] using wordTrace_append hprefix tailTrace_3106058
  have hstable : (prefixWord ++ tailWord_3106058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106058).length < 2 ^ (prefixWord ++ tailWord_3106058).sum := by decide
  have hdescent : baseEnd_3106058 < baseStart_3106058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106066 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3106066 : Nat := 118140960795 + 3106066 * 2 ^ 59
def prefixEnd_3106066 : Nat := 4983230072969 + 3 ^ 40 * 3106066 * 2
def baseEnd_3106066 : Nat := 1594904802588149736190469

theorem tailTrace_3106066 : CollatzResearch.WordTrace tailWord_3106066 prefixEnd_3106066 1594904802588149736190469 := by
  unfold tailWord_3106066
  simp only [CollatzResearch.WordTrace]
  refine ⟨28321883491315207671182513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75525022643507220456486701 28321883491315207671182513)
  ·
    refine ⟨21241412618486405753386885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28321883491315207671182513 21241412618486405753386885)
    ·
      refine ⟨3982764865966201078760041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21241412618486405753386885 3982764865966201078760041)
      ·
        refine ⟨2987073649474650809070031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3982764865966201078760041 2987073649474650809070031)
        ·
          refine ⟨4480610474211976213605047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987073649474650809070031 4480610474211976213605047)
          ·
            refine ⟨6720915711317964320407571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480610474211976213605047 6720915711317964320407571)
            ·
              refine ⟨10081373566976946480611357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6720915711317964320407571 10081373566976946480611357)
              ·
                refine ⟨3780515087616354930229259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10081373566976946480611357 3780515087616354930229259)
                ·
                  refine ⟨5670772631424532395343889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780515087616354930229259 5670772631424532395343889)
                  ·
                    refine ⟨4253079473568399296507917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5670772631424532395343889 4253079473568399296507917)
                    ·
                      refine ⟨1594904802588149736190469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4253079473568399296507917 1594904802588149736190469)
                      ·
                        rfl

theorem cell23_3106066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3106066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106066 prefixEnd_3106066 := by exact prefixLift 3106066
  have htrace : WordTrace (prefixWord ++ tailWord_3106066) baseStart_3106066 baseEnd_3106066 := by
    simpa [prefixWord, tailWord_3106066, baseEnd_3106066] using wordTrace_append hprefix tailTrace_3106066
  have hstable : (prefixWord ++ tailWord_3106066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106066).length < 2 ^ (prefixWord ++ tailWord_3106066).sum := by decide
  have hdescent : baseEnd_3106066 < baseStart_3106066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106202 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_3106202 : Nat := 118140960795 + 3106202 * 2 ^ 59
def prefixEnd_3106202 : Nat := 4983230072969 + 3 ^ 40 * 3106202 * 2
def baseEnd_3106202 : Nat := 531658211985720401363281

theorem tailTrace_3106202 : CollatzResearch.WordTrace tailWord_3106202 prefixEnd_3106202 531658211985720401363281 := by
  unfold tailWord_3106202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28323123573192031477920215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75528329528512083941120573 28323123573192031477920215)
  ·
    refine ⟨42484685359788047216880323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28323123573192031477920215 42484685359788047216880323)
    ·
      refine ⟨63727028039682070825320485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42484685359788047216880323 63727028039682070825320485)
      ·
        refine ⟨11948817757440388279747591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63727028039682070825320485 11948817757440388279747591)
        ·
          refine ⟨17923226636160582419621387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11948817757440388279747591 17923226636160582419621387)
          ·
            refine ⟨26884839954240873629432081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17923226636160582419621387 26884839954240873629432081)
            ·
              refine ⟨20163629965680655222074061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26884839954240873629432081 20163629965680655222074061)
              ·
                refine ⟨7561361237130245708277773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20163629965680655222074061 7561361237130245708277773)
                ·
                  refine ⟨2835510463923842140604165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7561361237130245708277773 2835510463923842140604165)
                  ·
                    refine ⟨531658211985720401363281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2835510463923842140604165 531658211985720401363281)
                    ·
                      rfl

theorem cell23_3106202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_3106202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106202 prefixEnd_3106202 := by exact prefixLift 3106202
  have htrace : WordTrace (prefixWord ++ tailWord_3106202) baseStart_3106202 baseEnd_3106202 := by
    simpa [prefixWord, tailWord_3106202, baseEnd_3106202] using wordTrace_append hprefix tailTrace_3106202
  have hstable : (prefixWord ++ tailWord_3106202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106202).length < 2 ^ (prefixWord ++ tailWord_3106202).sum := by decide
  have hdescent : baseEnd_3106202 < baseStart_3106202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106229 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3106229 : Nat := 118140960795 + 3106229 * 2 ^ 59
def prefixEnd_3106229 : Nat := 4983230072969 + 3 ^ 40 * 3106229 * 2
def baseEnd_3106229 : Nat := 1594988499934832598452219

theorem tailTrace_3106229 : CollatzResearch.WordTrace tailWord_3106229 prefixEnd_3106229 1594988499934832598452219 := by
  unfold tailWord_3106229
  simp only [CollatzResearch.WordTrace]
  refine ⟨113293479063670309522913741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75528986042446873015275827 113293479063670309522913741)
  ·
    refine ⟨42485054648876366071092653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113293479063670309522913741 42485054648876366071092653)
    ·
      refine ⟨15931895493328637276659745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42485054648876366071092653 15931895493328637276659745)
      ·
        refine ⟨11948921619996477957494809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15931895493328637276659745 11948921619996477957494809)
        ·
          refine ⟨8961691214997358468121107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11948921619996477957494809 8961691214997358468121107)
          ·
            refine ⟨13442536822496037702181661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961691214997358468121107 13442536822496037702181661)
            ·
              refine ⟨5040951308436014138318123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13442536822496037702181661 5040951308436014138318123)
              ·
                refine ⟨7561426962654021207477185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040951308436014138318123 7561426962654021207477185)
                ·
                  refine ⟨5671070221990515905607889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7561426962654021207477185 5671070221990515905607889)
                  ·
                    refine ⟨4253302666492886929205917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5671070221990515905607889 4253302666492886929205917)
                    ·
                      refine ⟨1594988499934832598452219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4253302666492886929205917 1594988499934832598452219)
                      ·
                        rfl

theorem cell23_3106229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3106229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106229 prefixEnd_3106229 := by exact prefixLift 3106229
  have htrace : WordTrace (prefixWord ++ tailWord_3106229) baseStart_3106229 baseEnd_3106229 := by
    simpa [prefixWord, tailWord_3106229, baseEnd_3106229] using wordTrace_append hprefix tailTrace_3106229
  have hstable : (prefixWord ++ tailWord_3106229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106229).length < 2 ^ (prefixWord ++ tailWord_3106229).sum := by decide
  have hdescent : baseEnd_3106229 < baseStart_3106229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106269 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_3106269 : Nat := 118140960795 + 3106269 * 2 ^ 59
def prefixEnd_3106269 : Nat := 4983230072969 + 3 ^ 40 * 3106269 * 2
def baseEnd_3106269 : Nat := 1595009039161012441952035

theorem tailTrace_3106269 : CollatzResearch.WordTrace tailWord_3106269 prefixEnd_3106269 1595009039161012441952035 := by
  unfold tailWord_3106269
  simp only [CollatzResearch.WordTrace]
  refine ⟨113294937983525396354369861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75529958655683597569579907 113294937983525396354369861)
  ·
    refine ⟨21242800871911011816444349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113294937983525396354369861 21242800871911011816444349)
    ·
      refine ⟨7966050326966629431166631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21242800871911011816444349 7966050326966629431166631)
      ·
        refine ⟨11949075490449944146749947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7966050326966629431166631 11949075490449944146749947)
        ·
          refine ⟨17923613235674916220124921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11949075490449944146749947 17923613235674916220124921)
          ·
            refine ⟨13442709926756187165093691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17923613235674916220124921 13442709926756187165093691)
            ·
              refine ⟨20164064890134280747640537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13442709926756187165093691 20164064890134280747640537)
              ·
                refine ⟨15123048667600710560730403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20164064890134280747640537 15123048667600710560730403)
                ·
                  refine ⟨22684573001401065841095605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15123048667600710560730403 22684573001401065841095605)
                  ·
                    refine ⟨2126678718881349922602713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22684573001401065841095605 2126678718881349922602713)
                    ·
                      refine ⟨1595009039161012441952035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126678718881349922602713 1595009039161012441952035)
                      ·
                        rfl

theorem cell23_3106269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_3106269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106269 prefixEnd_3106269 := by exact prefixLift 3106269
  have htrace : WordTrace (prefixWord ++ tailWord_3106269) baseStart_3106269 baseEnd_3106269 := by
    simpa [prefixWord, tailWord_3106269, baseEnd_3106269] using wordTrace_append hprefix tailTrace_3106269
  have hstable : (prefixWord ++ tailWord_3106269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106269).length < 2 ^ (prefixWord ++ tailWord_3106269).sum := by decide
  have hdescent : baseEnd_3106269 < baseStart_3106269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106279 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 1, 5]
def baseStart_3106279 : Nat := 118140960795 + 3106279 * 2 ^ 59
def prefixEnd_3106279 : Nat := 4983230072969 + 3 ^ 40 * 3106279 * 2
def baseEnd_3106279 : Nat := 531671391322519134275663

theorem tailTrace_3106279 : CollatzResearch.WordTrace tailWord_3106279 prefixEnd_3106279 531671391322519134275663 := by
  unfold tailWord_3106279
  simp only [CollatzResearch.WordTrace]
  refine ⟨113295302713489168062233891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75530201808992778708155927 113295302713489168062233891)
  ·
    refine ⟨169942954070233752093350837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113295302713489168062233891 169942954070233752093350837)
    ·
      refine ⟨15932151944084414258751641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169942954070233752093350837 15932151944084414258751641)
      ·
        refine ⟨11949113958063310694063731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15932151944084414258751641 11949113958063310694063731)
        ·
          refine ⟨17923670937094966041095597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11949113958063310694063731 17923670937094966041095597)
          ·
            refine ⟨6721376601410612265410849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17923670937094966041095597 6721376601410612265410849)
            ·
              refine ⟨5041032451057959199058137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6721376601410612265410849 5041032451057959199058137)
              ·
                refine ⟨3780774338293469399293603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5041032451057959199058137 3780774338293469399293603)
                ·
                  refine ⟨5671161507440204098940405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780774338293469399293603 5671161507440204098940405)
                  ·
                    refine ⟨531671391322519134275663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5671161507440204098940405 531671391322519134275663)
                    ·
                      rfl

theorem cell23_3106279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_3106279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106279 prefixEnd_3106279 := by exact prefixLift 3106279
  have htrace : WordTrace (prefixWord ++ tailWord_3106279) baseStart_3106279 baseEnd_3106279 := by
    simpa [prefixWord, tailWord_3106279, baseEnd_3106279] using wordTrace_append hprefix tailTrace_3106279
  have hstable : (prefixWord ++ tailWord_3106279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106279).length < 2 ^ (prefixWord ++ tailWord_3106279).sum := by decide
  have hdescent : baseEnd_3106279 < baseStart_3106279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106336 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3106336 : Nat := 118140960795 + 3106336 * 2 ^ 59
def prefixEnd_3106336 : Nat := 4983230072969 + 3 ^ 40 * 3106336 * 2
def baseEnd_3106336 : Nat := 1595043442364863679814227

theorem tailTrace_3106336 : CollatzResearch.WordTrace tailWord_3106336 prefixEnd_3106336 1595043442364863679814227 := by
  unfold tailWord_3106336
  simp only [CollatzResearch.WordTrace]
  refine ⟨56648690837141333398529431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75531587782855111198039241 56648690837141333398529431)
  ·
    refine ⟨84973036255712000097794147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56648690837141333398529431 84973036255712000097794147)
    ·
      refine ⟨127459554383568000146691221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84973036255712000097794147 127459554383568000146691221)
      ·
        refine ⟨5974666611729750006876151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127459554383568000146691221 5974666611729750006876151)
        ·
          refine ⟨8961999917594625010314227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5974666611729750006876151 8961999917594625010314227)
          ·
            refine ⟨13442999876391937515471341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961999917594625010314227 13442999876391937515471341)
            ·
              refine ⟨5041124953646976568301753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13442999876391937515471341 5041124953646976568301753)
              ·
                refine ⟨3780843715235232426226315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5041124953646976568301753 3780843715235232426226315)
                ·
                  refine ⟨5671265572852848639339473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780843715235232426226315 5671265572852848639339473)
                  ·
                    refine ⟨4253449179639636479504605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5671265572852848639339473 4253449179639636479504605)
                    ·
                      refine ⟨1595043442364863679814227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4253449179639636479504605 1595043442364863679814227)
                      ·
                        rfl

theorem cell23_3106336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3106336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106336 prefixEnd_3106336 := by exact prefixLift 3106336
  have htrace : WordTrace (prefixWord ++ tailWord_3106336) baseStart_3106336 baseEnd_3106336 := by
    simpa [prefixWord, tailWord_3106336, baseEnd_3106336] using wordTrace_append hprefix tailTrace_3106336
  have hstable : (prefixWord ++ tailWord_3106336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106336).length < 2 ^ (prefixWord ++ tailWord_3106336).sum := by decide
  have hdescent : baseEnd_3106336 < baseStart_3106336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106392 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_3106392 : Nat := 118140960795 + 3106392 * 2 ^ 59
def prefixEnd_3106392 : Nat := 4983230072969 + 3 ^ 40 * 3106392 * 2
def baseEnd_3106392 : Nat := 1595072197281515460713969

theorem tailTrace_3106392 : CollatzResearch.WordTrace tailWord_3106392 prefixEnd_3106392 1595072197281515460713969 := by
  unfold tailWord_3106392
  simp only [CollatzResearch.WordTrace]
  refine ⟨56649712081039894180548715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75532949441386525574064953 56649712081039894180548715)
  ·
    refine ⟨84974568121559841270823073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56649712081039894180548715 84974568121559841270823073)
    ·
      refine ⟨63730926091169880953117305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84974568121559841270823073 63730926091169880953117305)
      ·
        refine ⟨47798194568377410714837979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63730926091169880953117305 47798194568377410714837979)
        ·
          refine ⟨71697291852566116072256969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47798194568377410714837979 71697291852566116072256969)
          ·
            refine ⟨53772968889424587054192727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71697291852566116072256969 53772968889424587054192727)
            ·
              refine ⟨80659453334136880581289091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53772968889424587054192727 80659453334136880581289091)
              ·
                refine ⟨120989180001205320871933637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80659453334136880581289091 120989180001205320871933637)
                ·
                  refine ⟨22685471250225997663487557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120989180001205320871933637 22685471250225997663487557)
                  ·
                    refine ⟨4253525859417374561903917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22685471250225997663487557 4253525859417374561903917)
                    ·
                      refine ⟨1595072197281515460713969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4253525859417374561903917 1595072197281515460713969)
                      ·
                        rfl

theorem cell23_3106392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_3106392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106392 prefixEnd_3106392 := by exact prefixLift 3106392
  have htrace : WordTrace (prefixWord ++ tailWord_3106392) baseStart_3106392 baseEnd_3106392 := by
    simpa [prefixWord, tailWord_3106392, baseEnd_3106392] using wordTrace_append hprefix tailTrace_3106392
  have hstable : (prefixWord ++ tailWord_3106392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106392).length < 2 ^ (prefixWord ++ tailWord_3106392).sum := by decide
  have hdescent : baseEnd_3106392 < baseStart_3106392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106410 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_3106410 : Nat := 118140960795 + 3106410 * 2 ^ 59
def prefixEnd_3106410 : Nat := 4983230072969 + 3 ^ 40 * 3106410 * 2
def baseEnd_3106410 : Nat := 1595081439933296390288887

theorem tailTrace_3106410 : CollatzResearch.WordTrace tailWord_3106410 prefixEnd_3106410 1595081439933296390288887 := by
  unfold tailWord_3106410
  simp only [CollatzResearch.WordTrace]
  refine ⟨28325020169003644358813171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75533387117343051623501789 28325020169003644358813171)
  ·
    refine ⟨42487530253505466538219757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28325020169003644358813171 42487530253505466538219757)
    ·
      refine ⟨15932823845064549951832409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42487530253505466538219757 15932823845064549951832409)
      ·
        refine ⟨11949617883798412463874307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15932823845064549951832409 11949617883798412463874307)
        ·
          refine ⟨17924426825697618695811461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11949617883798412463874307 17924426825697618695811461)
          ·
            refine ⟨3360830029818303505464649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17924426825697618695811461 3360830029818303505464649)
            ·
              refine ⟨2520622522363727629098487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360830029818303505464649 2520622522363727629098487)
              ·
                refine ⟨3780933783545591443647731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520622522363727629098487 3780933783545591443647731)
                ·
                  refine ⟨5671400675318387165471597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780933783545591443647731 5671400675318387165471597)
                  ·
                    refine ⟨2126775253244395187051849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5671400675318387165471597 2126775253244395187051849)
                    ·
                      refine ⟨1595081439933296390288887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126775253244395187051849 1595081439933296390288887)
                      ·
                        rfl

theorem cell23_3106410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_3106410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106410 prefixEnd_3106410 := by exact prefixLift 3106410
  have htrace : WordTrace (prefixWord ++ tailWord_3106410) baseStart_3106410 baseEnd_3106410 := by
    simpa [prefixWord, tailWord_3106410, baseEnd_3106410] using wordTrace_append hprefix tailTrace_3106410
  have hstable : (prefixWord ++ tailWord_3106410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106410).length < 2 ^ (prefixWord ++ tailWord_3106410).sum := by decide
  have hdescent : baseEnd_3106410 < baseStart_3106410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106429 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 7]
def baseStart_3106429 : Nat := 118140960795 + 3106429 * 2 ^ 59
def prefixEnd_3106429 : Nat := 4983230072969 + 3 ^ 40 * 3106429 * 2
def baseEnd_3106429 : Nat := 177232355118414646216811

theorem tailTrace_3106429 : CollatzResearch.WordTrace tailWord_3106429 prefixEnd_3106429 177232355118414646216811 := by
  unfold tailWord_3106429
  simp only [CollatzResearch.WordTrace]
  refine ⟨113300773662945743680194341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75533849108630495786796227 113300773662945743680194341)
  ·
    refine ⟨21243895061802326940036439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113300773662945743680194341 21243895061802326940036439)
    ·
      refine ⟨31865842592703490410054659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21243895061802326940036439 31865842592703490410054659)
      ·
        refine ⟨47798763889055235615081989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31865842592703490410054659 47798763889055235615081989)
        ·
          refine ⟨8962268229197856677827873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47798763889055235615081989 8962268229197856677827873)
          ·
            refine ⟨6721701171898392508370905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8962268229197856677827873 6721701171898392508370905)
            ·
              refine ⟨5041275878923794381278179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6721701171898392508370905 5041275878923794381278179)
              ·
                refine ⟨7561913818385691571917269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041275878923794381278179 7561913818385691571917269)
                ·
                  refine ⟨177232355118414646216811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7561913818385691571917269 177232355118414646216811)
                  ·
                    rfl

theorem cell23_3106429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_3106429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106429 prefixEnd_3106429 := by exact prefixLift 3106429
  have htrace : WordTrace (prefixWord ++ tailWord_3106429) baseStart_3106429 baseEnd_3106429 := by
    simpa [prefixWord, tailWord_3106429, baseEnd_3106429] using wordTrace_append hprefix tailTrace_3106429
  have hstable : (prefixWord ++ tailWord_3106429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106429).length < 2 ^ (prefixWord ++ tailWord_3106429).sum := by decide
  have hdescent : baseEnd_3106429 < baseStart_3106429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106439 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_3106439 : Nat := 118140960795 + 3106439 * 2 ^ 59
def prefixEnd_3106439 : Nat := 4983230072969 + 3 ^ 40 * 3106439 * 2
def baseEnd_3106439 : Nat := 1595096330872276776826253

theorem tailTrace_3106439 : CollatzResearch.WordTrace tailWord_3106439 prefixEnd_3106439 1595096330872276776826253 := by
  unfold tailWord_3106439
  simp only [CollatzResearch.WordTrace]
  refine ⟨113301138392909515388058371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75534092261939676925372247 113301138392909515388058371)
  ·
    refine ⟨169951707589364273082087557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113301138392909515388058371 169951707589364273082087557)
    ·
      refine ⟨31865945173005801202891417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169951707589364273082087557 31865945173005801202891417)
      ·
        refine ⟨23899458879754350902168563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31865945173005801202891417 23899458879754350902168563)
        ·
          refine ⟨35849188319631526353252845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23899458879754350902168563 35849188319631526353252845)
          ·
            refine ⟨13443445619861822382469817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35849188319631526353252845 13443445619861822382469817)
            ·
              refine ⟨10082584214896366786852363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13443445619861822382469817 10082584214896366786852363)
              ·
                refine ⟨15123876322344550180278545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10082584214896366786852363 15123876322344550180278545)
                ·
                  refine ⟨11342907241758412635208909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15123876322344550180278545 11342907241758412635208909)
                  ·
                    refine ⟨4253590215659404738203341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11342907241758412635208909 4253590215659404738203341)
                    ·
                      refine ⟨1595096330872276776826253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4253590215659404738203341 1595096330872276776826253)
                      ·
                        rfl

theorem cell23_3106439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_3106439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106439 prefixEnd_3106439 := by exact prefixLift 3106439
  have htrace : WordTrace (prefixWord ++ tailWord_3106439) baseStart_3106439 baseEnd_3106439 := by
    simpa [prefixWord, tailWord_3106439, baseEnd_3106439] using wordTrace_append hprefix tailTrace_3106439
  have hstable : (prefixWord ++ tailWord_3106439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106439).length < 2 ^ (prefixWord ++ tailWord_3106439).sum := by decide
  have hdescent : baseEnd_3106439 < baseStart_3106439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106440 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3106440 : Nat := 118140960795 + 3106440 * 2 ^ 59
def prefixEnd_3106440 : Nat := 4983230072969 + 3 ^ 40 * 3106440 * 2
def baseEnd_3106440 : Nat := 1595096844352931272913749

theorem tailTrace_3106440 : CollatzResearch.WordTrace tailWord_3106440 prefixEnd_3106440 1595096844352931272913749 := by
  unfold tailWord_3106440
  simp only [CollatzResearch.WordTrace]
  refine ⟨56650587432952946279422387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75534116577270595039229849 56650587432952946279422387)
  ·
    refine ⟨84975881149429419419133581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56650587432952946279422387 84975881149429419419133581)
    ·
      refine ⟨31865955431036032282175093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84975881149429419419133581 31865955431036032282175093)
      ·
        refine ⟨2987433321659628026453915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31865955431036032282175093 2987433321659628026453915)
        ·
          refine ⟨4481149982489442039680873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987433321659628026453915 4481149982489442039680873)
          ·
            refine ⟨3360862486867081529760655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4481149982489442039680873 3360862486867081529760655)
            ·
              refine ⟨5041293730300622294640983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360862486867081529760655 5041293730300622294640983)
              ·
                refine ⟨7561940595450933441961475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041293730300622294640983 7561940595450933441961475)
                ·
                  refine ⟨11342910893176400162942213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7561940595450933441961475 11342910893176400162942213)
                  ·
                    refine ⟨2126795792470575030551665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11342910893176400162942213 2126795792470575030551665)
                    ·
                      refine ⟨1595096844352931272913749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126795792470575030551665 1595096844352931272913749)
                      ·
                        rfl

theorem cell23_3106440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3106440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106440 prefixEnd_3106440 := by exact prefixLift 3106440
  have htrace : WordTrace (prefixWord ++ tailWord_3106440) baseStart_3106440 baseEnd_3106440 := by
    simpa [prefixWord, tailWord_3106440, baseEnd_3106440] using wordTrace_append hprefix tailTrace_3106440
  have hstable : (prefixWord ++ tailWord_3106440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106440).length < 2 ^ (prefixWord ++ tailWord_3106440).sum := by decide
  have hdescent : baseEnd_3106440 < baseStart_3106440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106479 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_3106479 : Nat := 118140960795 + 3106479 * 2 ^ 59
def prefixEnd_3106479 : Nat := 4983230072969 + 3 ^ 40 * 3106479 * 2
def baseEnd_3106479 : Nat := 1595116870098456620326069

theorem tailTrace_3106479 : CollatzResearch.WordTrace tailWord_3106479 prefixEnd_3106479 1595116870098456620326069 := by
  unfold tailWord_3106479
  simp only [CollatzResearch.WordTrace]
  refine ⟨113302597312764602219514491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75535064875176401479676327 113302597312764602219514491)
  ·
    refine ⟨169953895969146903329271737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113302597312764602219514491 169953895969146903329271737)
    ·
      refine ⟨127465421976860177496953803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169953895969146903329271737 127465421976860177496953803)
      ·
        refine ⟨191198132965290266245430705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127465421976860177496953803 191198132965290266245430705)
        ·
          refine ⟨143398599723967699684073029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191198132965290266245430705 143398599723967699684073029)
          ·
            refine ⟨26887237448243943690763693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143398599723967699684073029 26887237448243943690763693)
            ·
              refine ⟨10082714043091478884036385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26887237448243943690763693 10082714043091478884036385)
              ·
                refine ⟨7562035532318609163027289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10082714043091478884036385 7562035532318609163027289)
                ·
                  refine ⟨5671526649238956872270467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7562035532318609163027289 5671526649238956872270467)
                  ·
                    refine ⟨8507289973858435308405701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5671526649238956872270467 8507289973858435308405701)
                    ·
                      refine ⟨1595116870098456620326069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8507289973858435308405701 1595116870098456620326069)
                      ·
                        rfl

theorem cell23_3106479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_3106479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106479 prefixEnd_3106479 := by exact prefixLift 3106479
  have htrace : WordTrace (prefixWord ++ tailWord_3106479) baseStart_3106479 baseEnd_3106479 := by
    simpa [prefixWord, tailWord_3106479, baseEnd_3106479] using wordTrace_append hprefix tailTrace_3106479
  have hstable : (prefixWord ++ tailWord_3106479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106479).length < 2 ^ (prefixWord ++ tailWord_3106479).sum := by decide
  have hdescent : baseEnd_3106479 < baseStart_3106479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106486 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3106486 : Nat := 118140960795 + 3106486 * 2 ^ 59
def prefixEnd_3106486 : Nat := 4983230072969 + 3 ^ 40 * 3106486 * 2
def baseEnd_3106486 : Nat := 1595120464463038092938537

theorem tailTrace_3106486 : CollatzResearch.WordTrace tailWord_3106486 prefixEnd_3106486 1595120464463038092938537 := by
  unfold tailWord_3106486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081428288983702650938707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75535235082492828276679541 7081428288983702650938707)
  ·
    refine ⟨10622142433475553976408061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7081428288983702650938707 10622142433475553976408061)
    ·
      refine ⟨3983303412553332741153023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10622142433475553976408061 3983303412553332741153023)
      ·
        refine ⟨5974955118829999111729535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3983303412553332741153023 5974955118829999111729535)
        ·
          refine ⟨8962432678244998667594303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5974955118829999111729535 8962432678244998667594303)
          ·
            refine ⟨13443649017367498001391455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8962432678244998667594303 13443649017367498001391455)
            ·
              refine ⟨20165473526051247002087183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13443649017367498001391455 20165473526051247002087183)
              ·
                refine ⟨30248210289076870503130775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20165473526051247002087183 30248210289076870503130775)
                ·
                  refine ⟨45372315433615305754696163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30248210289076870503130775 45372315433615305754696163)
                  ·
                    refine ⟨68058473150422958632044245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45372315433615305754696163 68058473150422958632044245)
                    ·
                      refine ⟨1595120464463038092938537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68058473150422958632044245 1595120464463038092938537)
                      ·
                        rfl

theorem cell23_3106486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3106486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106486 prefixEnd_3106486 := by exact prefixLift 3106486
  have htrace : WordTrace (prefixWord ++ tailWord_3106486) baseStart_3106486 baseEnd_3106486 := by
    simpa [prefixWord, tailWord_3106486, baseEnd_3106486] using wordTrace_append hprefix tailTrace_3106486
  have hstable : (prefixWord ++ tailWord_3106486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106486).length < 2 ^ (prefixWord ++ tailWord_3106486).sum := by decide
  have hdescent : baseEnd_3106486 < baseStart_3106486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106536 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 6]
def baseStart_3106536 : Nat := 118140960795 + 3106536 * 2 ^ 59
def prefixEnd_3106536 : Nat := 4983230072969 + 3 ^ 40 * 3106536 * 2
def baseEnd_3106536 : Nat := 177238459832862544145923

theorem tailTrace_3106536 : CollatzResearch.WordTrace tailWord_3106536 prefixEnd_3106536 177238459832862544145923 := by
  unfold tailWord_3106536
  simp only [CollatzResearch.WordTrace]
  refine ⟨56652338136779050477169731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75536450849038733969559641 56652338136779050477169731)
  ·
    refine ⟨84978507205168575715754597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56652338136779050477169731 84978507205168575715754597)
    ·
      refine ⟨15933470100969107946703987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84978507205168575715754597 15933470100969107946703987)
      ·
        refine ⟨23900205151453661920055981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15933470100969107946703987 23900205151453661920055981)
        ·
          refine ⟨8962576931795123220020993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23900205151453661920055981 8962576931795123220020993)
          ·
            refine ⟨6721932698846342415015745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8962576931795123220020993 6721932698846342415015745)
            ·
              refine ⟨5041449524134756811261809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6721932698846342415015745 5041449524134756811261809)
              ·
                refine ⟨3781087143101067608446357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5041449524134756811261809 3781087143101067608446357)
                ·
                  refine ⟨177238459832862544145923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3781087143101067608446357 177238459832862544145923)
                  ·
                    rfl

theorem cell23_3106536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 6].length) (baseStart_3106536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106536 prefixEnd_3106536 := by exact prefixLift 3106536
  have htrace : WordTrace (prefixWord ++ tailWord_3106536) baseStart_3106536 baseEnd_3106536 := by
    simpa [prefixWord, tailWord_3106536, baseEnd_3106536] using wordTrace_append hprefix tailTrace_3106536
  have hstable : (prefixWord ++ tailWord_3106536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106536).length < 2 ^ (prefixWord ++ tailWord_3106536).sum := by decide
  have hdescent : baseEnd_3106536 < baseStart_3106536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106556 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_3106556 : Nat := 118140960795 + 3106556 * 2 ^ 59
def prefixEnd_3106556 : Nat := 4983230072969 + 3 ^ 40 * 3106556 * 2
def baseEnd_3106556 : Nat := 1595156408108852819063215

theorem tailTrace_3106556 : CollatzResearch.WordTrace tailWord_3106556 prefixEnd_3106556 1595156408108852819063215 := by
  unfold tailWord_3106556
  simp only [CollatzResearch.WordTrace]
  refine ⟨56652702866742822185033761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75536937155657096246711681 56652702866742822185033761)
  ·
    refine ⟨42489527150057116638775321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56652702866742822185033761 42489527150057116638775321)
    ·
      refine ⟨31867145362542837479081491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42489527150057116638775321 31867145362542837479081491)
      ·
        refine ⟨47800718043814256218622237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31867145362542837479081491 47800718043814256218622237)
        ·
          refine ⟨17925269266430346081983339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47800718043814256218622237 17925269266430346081983339)
          ·
            refine ⟨26887903899645519122975009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17925269266430346081983339 26887903899645519122975009)
            ·
              refine ⟨20165927924734139342231257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26887903899645519122975009 20165927924734139342231257)
              ·
                refine ⟨15124445943550604506673443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20165927924734139342231257 15124445943550604506673443)
                ·
                  refine ⟨22686668915325906760010165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15124445943550604506673443 22686668915325906760010165)
                  ·
                    refine ⟨2126875210811803758750953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22686668915325906760010165 2126875210811803758750953)
                    ·
                      refine ⟨1595156408108852819063215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126875210811803758750953 1595156408108852819063215)
                      ·
                        rfl

theorem cell23_3106556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_3106556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106556 prefixEnd_3106556 := by exact prefixLift 3106556
  have htrace : WordTrace (prefixWord ++ tailWord_3106556) baseStart_3106556 baseEnd_3106556 := by
    simpa [prefixWord, tailWord_3106556, baseEnd_3106556] using wordTrace_append hprefix tailTrace_3106556
  have hstable : (prefixWord ++ tailWord_3106556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106556).length < 2 ^ (prefixWord ++ tailWord_3106556).sum := by decide
  have hdescent : baseEnd_3106556 < baseStart_3106556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106583 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 1, 5]
def baseStart_3106583 : Nat := 118140960795 + 3106583 * 2 ^ 59
def prefixEnd_3106583 : Nat := 4983230072969 + 3 ^ 40 * 3106583 * 2
def baseEnd_3106583 : Nat := 531723424028841404475197

theorem tailTrace_3106583 : CollatzResearch.WordTrace tailWord_3106583 prefixEnd_3106583 531723424028841404475197 := by
  unfold tailWord_3106583
  simp only [CollatzResearch.WordTrace]
  refine ⟨113306390504387827981300403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75537593669591885320866935 113306390504387827981300403)
  ·
    refine ⟨169959585756581741971950605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113306390504387827981300403 169959585756581741971950605)
    ·
      refine ⟨63734844658718153239481477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169959585756581741971950605 63734844658718153239481477)
      ·
        refine ⟨11950283373509653732402777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63734844658718153239481477 11950283373509653732402777)
        ·
          refine ⟨8962712530132240299302083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11950283373509653732402777 8962712530132240299302083)
          ·
            refine ⟨13444068795198360448953125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8962712530132240299302083 13444068795198360448953125)
            ·
              refine ⟨2520762899099692584178711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13444068795198360448953125 2520762899099692584178711)
              ·
                refine ⟨3781144348649538876268067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520762899099692584178711 3781144348649538876268067)
                ·
                  refine ⟨5671716522974308314402101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781144348649538876268067 5671716522974308314402101)
                  ·
                    refine ⟨531723424028841404475197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5671716522974308314402101 531723424028841404475197)
                    ·
                      rfl

theorem cell23_3106583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_3106583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106583 prefixEnd_3106583 := by exact prefixLift 3106583
  have htrace : WordTrace (prefixWord ++ tailWord_3106583) baseStart_3106583 baseEnd_3106583 := by
    simpa [prefixWord, tailWord_3106583, baseEnd_3106583] using wordTrace_append hprefix tailTrace_3106583
  have hstable : (prefixWord ++ tailWord_3106583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106583).length < 2 ^ (prefixWord ++ tailWord_3106583).sum := by decide
  have hdescent : baseEnd_3106583 < baseStart_3106583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106613 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_3106613 : Nat := 118140960795 + 3106613 * 2 ^ 59
def prefixEnd_3106613 : Nat := 4983230072969 + 3 ^ 40 * 3106613 * 2
def baseEnd_3106613 : Nat := 531728558835386365350151

theorem tailTrace_3106613 : CollatzResearch.WordTrace tailWord_3106613 prefixEnd_3106613 531728558835386365350151 := by
  unfold tailWord_3106613
  simp only [CollatzResearch.WordTrace]
  refine ⟨113307484694279143104892493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75538323129519428736594995 113307484694279143104892493)
  ·
    refine ⟨42490306760354678664334685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113307484694279143104892493 42490306760354678664334685)
    ·
      refine ⟨15933865035133004499125507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42490306760354678664334685 15933865035133004499125507)
      ·
        refine ⟨23900797552699506748688261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15933865035133004499125507 23900797552699506748688261)
        ·
          refine ⟨4481399541131157515379049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23900797552699506748688261 4481399541131157515379049)
          ·
            refine ⟨3361049655848368136534287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4481399541131157515379049 3361049655848368136534287)
            ·
              refine ⟨5041574483772552204801431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361049655848368136534287 5041574483772552204801431)
              ·
                refine ⟨7562361725658828307202147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041574483772552204801431 7562361725658828307202147)
                ·
                  refine ⟨11343542588488242460803221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7562361725658828307202147 11343542588488242460803221)
                  ·
                    refine ⟨531728558835386365350151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11343542588488242460803221 531728558835386365350151)
                    ·
                      rfl

theorem cell23_3106613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_3106613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106613 prefixEnd_3106613 := by exact prefixLift 3106613
  have htrace : WordTrace (prefixWord ++ tailWord_3106613) baseStart_3106613 baseEnd_3106613 := by
    simpa [prefixWord, tailWord_3106613, baseEnd_3106613] using wordTrace_append hprefix tailTrace_3106613
  have hstable : (prefixWord ++ tailWord_3106613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106613).length < 2 ^ (prefixWord ++ tailWord_3106613).sum := by decide
  have hdescent : baseEnd_3106613 < baseStart_3106613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106616 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_3106616 : Nat := 118140960795 + 3106616 * 2 ^ 59
def prefixEnd_3106616 : Nat := 4983230072969 + 3 ^ 40 * 3106616 * 2
def baseEnd_3106616 : Nat := 1595187216948122584312939

theorem tailTrace_3106616 : CollatzResearch.WordTrace tailWord_3106616 prefixEnd_3106616 1595187216948122584312939 := by
  unfold tailWord_3106616
  simp only [CollatzResearch.WordTrace]
  refine ⟨56653797056634137308625851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75538396075512183078167801 56653797056634137308625851)
  ·
    refine ⟨84980695584951205962938777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56653797056634137308625851 84980695584951205962938777)
    ·
      refine ⟨63735521688713404472204083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84980695584951205962938777 63735521688713404472204083)
      ·
        refine ⟨95603282533070106708306125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63735521688713404472204083 95603282533070106708306125)
        ·
          refine ⟨35851230949901290015614797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95603282533070106708306125 35851230949901290015614797)
          ·
            refine ⟨13444211606212983755855549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35851230949901290015614797 13444211606212983755855549)
            ·
              refine ⟨5041579352329868908445831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13444211606212983755855549 5041579352329868908445831)
              ·
                refine ⟨7562369028494803362668747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041579352329868908445831 7562369028494803362668747)
                ·
                  refine ⟨11343553542742205044003121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7562369028494803362668747 11343553542742205044003121)
                  ·
                    refine ⟨8507665157056653783002341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11343553542742205044003121 8507665157056653783002341)
                    ·
                      refine ⟨1595187216948122584312939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8507665157056653783002341 1595187216948122584312939)
                      ·
                        rfl

theorem cell23_3106616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_3106616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106616 prefixEnd_3106616 := by exact prefixLift 3106616
  have htrace : WordTrace (prefixWord ++ tailWord_3106616) baseStart_3106616 baseEnd_3106616 := by
    simpa [prefixWord, tailWord_3106616, baseEnd_3106616] using wordTrace_append hprefix tailTrace_3106616
  have hstable : (prefixWord ++ tailWord_3106616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106616).length < 2 ^ (prefixWord ++ tailWord_3106616).sum := by decide
  have hdescent : baseEnd_3106616 < baseStart_3106616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106630 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3106630 : Nat := 118140960795 + 3106630 * 2 ^ 59
def prefixEnd_3106630 : Nat := 4983230072969 + 3 ^ 40 * 3106630 * 2
def baseEnd_3106630 : Nat := 531731468559095176512625

theorem tailTrace_3106630 : CollatzResearch.WordTrace tailWord_3106630 prefixEnd_3106630 531731468559095176512625 := by
  unfold tailWord_3106630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3540878272975548594008167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75538736490145036672174229 3540878272975548594008167)
  ·
    refine ⟨5311317409463322891012251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3540878272975548594008167 5311317409463322891012251)
    ·
      refine ⟨7966976114194984336518377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5311317409463322891012251 7966976114194984336518377)
      ·
        refine ⟨5975232085646238252388783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7966976114194984336518377 5975232085646238252388783)
        ·
          refine ⟨8962848128469357378583175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975232085646238252388783 8962848128469357378583175)
          ·
            refine ⟨13444272192704036067874763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8962848128469357378583175 13444272192704036067874763)
            ·
              refine ⟨20166408289056054101812145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13444272192704036067874763 20166408289056054101812145)
              ·
                refine ⟨15124806216792040576359109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20166408289056054101812145 15124806216792040576359109)
                ·
                  refine ⟨2835901165648507608067333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15124806216792040576359109 2835901165648507608067333)
                  ·
                    refine ⟨531731468559095176512625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2835901165648507608067333 531731468559095176512625)
                    ·
                      rfl

theorem cell23_3106630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3106630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106630 prefixEnd_3106630 := by exact prefixLift 3106630
  have htrace : WordTrace (prefixWord ++ tailWord_3106630) baseStart_3106630 baseEnd_3106630 := by
    simpa [prefixWord, tailWord_3106630, baseEnd_3106630] using wordTrace_append hprefix tailTrace_3106630
  have hstable : (prefixWord ++ tailWord_3106630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106630).length < 2 ^ (prefixWord ++ tailWord_3106630).sum := by decide
  have hdescent : baseEnd_3106630 < baseStart_3106630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106649 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_3106649 : Nat := 118140960795 + 3106649 * 2 ^ 59
def prefixEnd_3106649 : Nat := 4983230072969 + 3 ^ 40 * 3106649 * 2
def baseEnd_3106649 : Nat := 1595204161809720955200287

theorem tailTrace_3106649 : CollatzResearch.WordTrace tailWord_3106649 prefixEnd_3106649 1595204161809720955200287 := by
  unfold tailWord_3106649
  simp only [CollatzResearch.WordTrace]
  refine ⟨113308797722148721253203001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75539198481432480835468667 113308797722148721253203001)
  ·
    refine ⟨84981598291611540939902251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113308797722148721253203001 84981598291611540939902251)
    ·
      refine ⟨127472397437417311409853377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84981598291611540939902251 127472397437417311409853377)
      ·
        refine ⟨95604298078062983557390033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127472397437417311409853377 95604298078062983557390033)
        ·
          refine ⟨71703223558547237668042525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95604298078062983557390033 71703223558547237668042525)
          ·
            refine ⟨26888708834455214125515947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71703223558547237668042525 26888708834455214125515947)
            ·
              refine ⟨40333063251682821188273921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26888708834455214125515947 40333063251682821188273921)
              ·
                refine ⟨30249797438762115891205441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40333063251682821188273921 30249797438762115891205441)
                ·
                  refine ⟨22687348079071586918404081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30249797438762115891205441 22687348079071586918404081)
                  ·
                    refine ⟨17015511059303690188803061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22687348079071586918404081 17015511059303690188803061)
                    ·
                      refine ⟨1595204161809720955200287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17015511059303690188803061 1595204161809720955200287)
                      ·
                        rfl

theorem cell23_3106649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_3106649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106649 prefixEnd_3106649 := by exact prefixLift 3106649
  have htrace : WordTrace (prefixWord ++ tailWord_3106649) baseStart_3106649 baseEnd_3106649 := by
    simpa [prefixWord, tailWord_3106649, baseEnd_3106649] using wordTrace_append hprefix tailTrace_3106649
  have hstable : (prefixWord ++ tailWord_3106649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106649).length < 2 ^ (prefixWord ++ tailWord_3106649).sum := by decide
  have hdescent : baseEnd_3106649 < baseStart_3106649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106663 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_3106663 : Nat := 118140960795 + 3106663 * 2 ^ 59
def prefixEnd_3106663 : Nat := 4983230072969 + 3 ^ 40 * 3106663 * 2
def baseEnd_3106663 : Nat := 1595211350538883900425223

theorem tailTrace_3106663 : CollatzResearch.WordTrace tailWord_3106663 prefixEnd_3106663 1595211350538883900425223 := by
  unfold tailWord_3106663
  simp only [CollatzResearch.WordTrace]
  refine ⟨113309308344098001644212643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75539538896065334429475095 113309308344098001644212643)
  ·
    refine ⟨169963962516147002466318965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113309308344098001644212643 169963962516147002466318965)
    ·
      refine ⟨15934121485888781481217403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169963962516147002466318965 15934121485888781481217403)
      ·
        refine ⟨23901182228833172221826105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15934121485888781481217403 23901182228833172221826105)
        ·
          refine ⟨17925886671624879166369579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23901182228833172221826105 17925886671624879166369579)
          ·
            refine ⟨26888830007437318749554369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17925886671624879166369579 26888830007437318749554369)
            ·
              refine ⟨20166622505577989062165777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26888830007437318749554369 20166622505577989062165777)
              ·
                refine ⟨15124966879183491796624333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20166622505577989062165777 15124966879183491796624333)
                ·
                  refine ⟨5671862579693809423734125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15124966879183491796624333 5671862579693809423734125)
                  ·
                    refine ⟨2126948467385178533900297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5671862579693809423734125 2126948467385178533900297)
                    ·
                      refine ⟨1595211350538883900425223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126948467385178533900297 1595211350538883900425223)
                      ·
                        rfl

theorem cell23_3106663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_3106663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106663 prefixEnd_3106663 := by exact prefixLift 3106663
  have htrace : WordTrace (prefixWord ++ tailWord_3106663) baseStart_3106663 baseEnd_3106663 := by
    simpa [prefixWord, tailWord_3106663, baseEnd_3106663] using wordTrace_append hprefix tailTrace_3106663
  have hstable : (prefixWord ++ tailWord_3106663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106663).length < 2 ^ (prefixWord ++ tailWord_3106663).sum := by decide
  have hdescent : baseEnd_3106663 < baseStart_3106663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106693 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 1, 4, 2]
def baseStart_3106693 : Nat := 118140960795 + 3106693 * 2 ^ 59
def prefixEnd_3106693 : Nat := 4983230072969 + 3 ^ 40 * 3106693 * 2
def baseEnd_3106693 : Nat := 1595226754958518783050085

theorem tailTrace_3106693 : CollatzResearch.WordTrace tailWord_3106693 prefixEnd_3106693 1595226754958518783050085 := by
  unfold tailWord_3106693
  simp only [CollatzResearch.WordTrace]
  refine ⟨113310402533989316767804733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75540268355992877845203155 113310402533989316767804733)
  ·
    refine ⟨42491400950245993787926775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113310402533989316767804733 42491400950245993787926775)
    ·
      refine ⟨63737101425368990681890163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42491400950245993787926775 63737101425368990681890163)
      ·
        refine ⟨95605652138053486022835245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63737101425368990681890163 95605652138053486022835245)
        ·
          refine ⟨35852119551770057258563217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95605652138053486022835245 35852119551770057258563217)
          ·
            refine ⟨26889089663827542943922413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35852119551770057258563217 26889089663827542943922413)
            ·
              refine ⟨10083408623935328603970905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26889089663827542943922413 10083408623935328603970905)
              ·
                refine ⟨7562556467951496452978179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10083408623935328603970905 7562556467951496452978179)
                ·
                  refine ⟨11343834701927244679467269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7562556467951496452978179 11343834701927244679467269)
                  ·
                    refine ⟨2126969006611358377400113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11343834701927244679467269 2126969006611358377400113)
                    ·
                      refine ⟨1595226754958518783050085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126969006611358377400113 1595226754958518783050085)
                      ·
                        rfl

theorem cell23_3106693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_3106693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106693 prefixEnd_3106693 := by exact prefixLift 3106693
  have htrace : WordTrace (prefixWord ++ tailWord_3106693) baseStart_3106693 baseEnd_3106693 := by
    simpa [prefixWord, tailWord_3106693, baseEnd_3106693] using wordTrace_append hprefix tailTrace_3106693
  have hstable : (prefixWord ++ tailWord_3106693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106693).length < 2 ^ (prefixWord ++ tailWord_3106693).sum := by decide
  have hdescent : baseEnd_3106693 < baseStart_3106693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106727 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_3106727 : Nat := 118140960795 + 3106727 * 2 ^ 59
def prefixEnd_3106727 : Nat := 4983230072969 + 3 ^ 40 * 3106727 * 2
def baseEnd_3106727 : Nat := 1595244213300771650024929

theorem tailTrace_3106727 : CollatzResearch.WordTrace tailWord_3106727 prefixEnd_3106727 1595244213300771650024929 := by
  unfold tailWord_3106727
  simp only [CollatzResearch.WordTrace]
  refine ⟨113311642615866140574542435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75541095077244093716361623 113311642615866140574542435)
  ·
    refine ⟨169967463923799210861813653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113311642615866140574542435 169967463923799210861813653)
    ·
      refine ⟨7967224871428088009147515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 169967463923799210861813653 7967224871428088009147515)
      ·
        refine ⟨11950837307142132013721273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967224871428088009147515 11950837307142132013721273)
        ·
          refine ⟨8963127980356599010290955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11950837307142132013721273 8963127980356599010290955)
          ·
            refine ⟨13444691970534898515436433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8963127980356599010290955 13444691970534898515436433)
            ·
              refine ⟨10083518977901173886577325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13444691970534898515436433 10083518977901173886577325)
              ·
                refine ⟨3781319616712940207466497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10083518977901173886577325 3781319616712940207466497)
                ·
                  refine ⟨2835989712534705155599873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3781319616712940207466497 2835989712534705155599873)
                  ·
                    refine ⟨2126992284401028866699905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2835989712534705155599873 2126992284401028866699905)
                    ·
                      refine ⟨1595244213300771650024929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2126992284401028866699905 1595244213300771650024929)
                      ·
                        rfl

theorem cell23_3106727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_3106727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106727 prefixEnd_3106727 := by exact prefixLift 3106727
  have htrace : WordTrace (prefixWord ++ tailWord_3106727) baseStart_3106727 baseEnd_3106727 := by
    simpa [prefixWord, tailWord_3106727, baseEnd_3106727] using wordTrace_append hprefix tailTrace_3106727
  have hstable : (prefixWord ++ tailWord_3106727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106727).length < 2 ^ (prefixWord ++ tailWord_3106727).sum := by decide
  have hdescent : baseEnd_3106727 < baseStart_3106727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106746 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_3106746 : Nat := 118140960795 + 3106746 * 2 ^ 59
def prefixEnd_3106746 : Nat := 4983230072969 + 3 ^ 40 * 3106746 * 2
def baseEnd_3106746 : Nat := 531751323144402358562447

theorem tailTrace_3106746 : CollatzResearch.WordTrace tailWord_3106746 prefixEnd_3106746 531751323144402358562447 := by
  unfold tailWord_3106746
  simp only [CollatzResearch.WordTrace]
  refine ⟨28328083900699326704871023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75541557068531537879656061 28328083900699326704871023)
  ·
    refine ⟨42492125851048990057306535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28328083900699326704871023 42492125851048990057306535)
    ·
      refine ⟨63738188776573485085959803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42492125851048990057306535 63738188776573485085959803)
      ·
        refine ⟨95607283164860227628939705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63738188776573485085959803 95607283164860227628939705)
        ·
          refine ⟨71705462373645170721704779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95607283164860227628939705 71705462373645170721704779)
          ·
            refine ⟨107558193560467756082557169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71705462373645170721704779 107558193560467756082557169)
            ·
              refine ⟨80668645170350817061917877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107558193560467756082557169 80668645170350817061917877)
              ·
                refine ⟨7562685484720389099554801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80668645170350817061917877 7562685484720389099554801)
                ·
                  refine ⟨5672014113540291824666101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7562685484720389099554801 5672014113540291824666101)
                  ·
                    refine ⟨531751323144402358562447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5672014113540291824666101 531751323144402358562447)
                    ·
                      rfl

theorem cell23_3106746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_3106746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106746 prefixEnd_3106746 := by exact prefixLift 3106746
  have htrace : WordTrace (prefixWord ++ tailWord_3106746) baseStart_3106746 baseEnd_3106746 := by
    simpa [prefixWord, tailWord_3106746, baseEnd_3106746] using wordTrace_append hprefix tailTrace_3106746
  have hstable : (prefixWord ++ tailWord_3106746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106746).length < 2 ^ (prefixWord ++ tailWord_3106746).sum := by decide
  have hdescent : baseEnd_3106746 < baseStart_3106746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106750 : List Nat := [4, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_3106750 : Nat := 118140960795 + 3106750 * 2 ^ 59
def prefixEnd_3106750 : Nat := 4983230072969 + 3 ^ 40 * 3106750 * 2
def baseEnd_3106750 : Nat := 177250669261758340004147

theorem tailTrace_3106750 : CollatzResearch.WordTrace tailWord_3106750 prefixEnd_3106750 177250669261758340004147 := by
  unfold tailWord_3106750
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164060186847851937828713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75541654329855210335086469 14164060186847851937828713)
  ·
    refine ⟨10623045140135888953371535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14164060186847851937828713 10623045140135888953371535)
    ·
      refine ⟨15934567710203833430057303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10623045140135888953371535 15934567710203833430057303)
      ·
        refine ⟨23901851565305750145085955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15934567710203833430057303 23901851565305750145085955)
        ·
          refine ⟨35852777347958625217628933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23901851565305750145085955 35852777347958625217628933)
          ·
            refine ⟨6722395752742242228305425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35852777347958625217628933 6722395752742242228305425)
            ·
              refine ⟨5041796814556681671229069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6722395752742242228305425 5041796814556681671229069)
              ·
                refine ⟨1890673805458755626710901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5041796814556681671229069 1890673805458755626710901)
                ·
                  refine ⟨177250669261758340004147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1890673805458755626710901 177250669261758340004147)
                  ·
                    rfl

theorem cell23_3106750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_3106750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106750 prefixEnd_3106750 := by exact prefixLift 3106750
  have htrace : WordTrace (prefixWord ++ tailWord_3106750) baseStart_3106750 baseEnd_3106750 := by
    simpa [prefixWord, tailWord_3106750, baseEnd_3106750] using wordTrace_append hprefix tailTrace_3106750
  have hstable : (prefixWord ++ tailWord_3106750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106750).length < 2 ^ (prefixWord ++ tailWord_3106750).sum := by decide
  have hdescent : baseEnd_3106750 < baseStart_3106750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106827 : List Nat := [1, 1, 1, 1, 6, 1, 5, 2, 1, 4]
def baseStart_3106827 : Nat := 118140960795 + 3106827 * 2 ^ 59
def prefixEnd_3106827 : Nat := 4983230072969 + 3 ^ 40 * 3106827 * 2
def baseEnd_3106827 : Nat := 531765187122073752924823

theorem tailTrace_3106827 : CollatzResearch.WordTrace tailWord_3106827 prefixEnd_3106827 531765187122073752924823 := by
  unfold tailWord_3106827
  simp only [CollatzResearch.WordTrace]
  refine ⟨113315289915503857653182735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75543526610335905102121823 113315289915503857653182735)
  ·
    refine ⟨169972934873255786479774103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113315289915503857653182735 169972934873255786479774103)
    ·
      refine ⟨254959402309883679719661155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169972934873255786479774103 254959402309883679719661155)
      ·
        refine ⟨382439103464825519579491733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254959402309883679719661155 382439103464825519579491733)
        ·
          refine ⟨17926832974913696230288675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 382439103464825519579491733 17926832974913696230288675)
          ·
            refine ⟨26890249462370544345433013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17926832974913696230288675 26890249462370544345433013)
            ·
              refine ⟨2520960887097238532384345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26890249462370544345433013 2520960887097238532384345)
              ·
                refine ⟨1890720665322928899288259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520960887097238532384345 1890720665322928899288259)
                ·
                  refine ⟨2836080997984393348932389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890720665322928899288259 2836080997984393348932389)
                  ·
                    refine ⟨531765187122073752924823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2836080997984393348932389 531765187122073752924823)
                    ·
                      rfl

theorem cell23_3106827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 4].length) (baseStart_3106827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106827 prefixEnd_3106827 := by exact prefixLift 3106827
  have htrace : WordTrace (prefixWord ++ tailWord_3106827) baseStart_3106827 baseEnd_3106827 := by
    simpa [prefixWord, tailWord_3106827, baseEnd_3106827] using wordTrace_append hprefix tailTrace_3106827
  have hstable : (prefixWord ++ tailWord_3106827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106827).length < 2 ^ (prefixWord ++ tailWord_3106827).sum := by decide
  have hdescent : baseEnd_3106827 < baseStart_3106827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106843 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 1, 5, 2]
def baseStart_3106843 : Nat := 118140960795 + 3106843 * 2 ^ 59
def prefixEnd_3106843 : Nat := 4983230072969 + 3 ^ 40 * 3106843 * 2
def baseEnd_3106843 : Nat := 1595303777056693196174395

theorem tailTrace_3106843 : CollatzResearch.WordTrace tailWord_3106843 prefixEnd_3106843 1595303777056693196174395 := by
  unfold tailWord_3106843
  simp only [CollatzResearch.WordTrace]
  refine ⟨113315873483445892385765183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75543915655630594923843455 113315873483445892385765183)
  ·
    refine ⟨169973810225168838578647775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113315873483445892385765183 169973810225168838578647775)
    ·
      refine ⟨254960715337753257867971663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169973810225168838578647775 254960715337753257867971663)
      ·
        refine ⟨382441073006629886801957495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254960715337753257867971663 382441073006629886801957495)
        ·
          refine ⟨573661609509944830202936243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382441073006629886801957495 573661609509944830202936243)
          ·
            refine ⟨860492414264917245304404365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573661609509944830202936243 860492414264917245304404365)
            ·
              refine ⟨322684655349343966989151637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 860492414264917245304404365 322684655349343966989151637)
              ·
                refine ⟨15125843219500498452616483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 322684655349343966989151637 15125843219500498452616483)
                ·
                  refine ⟨22688764829250747678924725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15125843219500498452616483 22688764829250747678924725)
                  ·
                    refine ⟨2127071702742257594899193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22688764829250747678924725 2127071702742257594899193)
                    ·
                      refine ⟨1595303777056693196174395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127071702742257594899193 1595303777056693196174395)
                      ·
                        rfl

theorem cell23_3106843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 5, 2].length) (baseStart_3106843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106843 prefixEnd_3106843 := by exact prefixLift 3106843
  have htrace : WordTrace (prefixWord ++ tailWord_3106843) baseStart_3106843 baseEnd_3106843 := by
    simpa [prefixWord, tailWord_3106843, baseEnd_3106843] using wordTrace_append hprefix tailTrace_3106843
  have hstable : (prefixWord ++ tailWord_3106843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106843).length < 2 ^ (prefixWord ++ tailWord_3106843).sum := by decide
  have hdescent : baseEnd_3106843 < baseStart_3106843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106850 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_3106850 : Nat := 118140960795 + 3106850 * 2 ^ 59
def prefixEnd_3106850 : Nat := 4983230072969 + 3 ^ 40 * 3106850 * 2
def baseEnd_3106850 : Nat := 1595307371421274668786863

theorem tailTrace_3106850 : CollatzResearch.WordTrace tailWord_3106850 prefixEnd_3106850 1595307371421274668786863 := by
  unfold tailWord_3106850
  simp only [CollatzResearch.WordTrace]
  refine ⟨28329032198605133145317501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75544085862947021720846669 28329032198605133145317501)
  ·
    refine ⟨10623387074476924929494063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28329032198605133145317501 10623387074476924929494063)
    ·
      refine ⟨15935080611715387394241095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10623387074476924929494063 15935080611715387394241095)
      ·
        refine ⟨23902620917573081091361643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15935080611715387394241095 23902620917573081091361643)
        ·
          refine ⟨35853931376359621637042465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23902620917573081091361643 35853931376359621637042465)
          ·
            refine ⟨26890448532269716227781849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35853931376359621637042465 26890448532269716227781849)
            ·
              refine ⟨20167836399202287170836387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26890448532269716227781849 20167836399202287170836387)
              ·
                refine ⟨30251754598803430756254581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20167836399202287170836387 30251754598803430756254581)
                ·
                  refine ⟨2836101993637821633398867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30251754598803430756254581 2836101993637821633398867)
                  ·
                    refine ⟨4254152990456732450098301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2836101993637821633398867 4254152990456732450098301)
                    ·
                      refine ⟨1595307371421274668786863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4254152990456732450098301 1595307371421274668786863)
                      ·
                        rfl

theorem cell23_3106850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_3106850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106850 prefixEnd_3106850 := by exact prefixLift 3106850
  have htrace : WordTrace (prefixWord ++ tailWord_3106850) baseStart_3106850 baseEnd_3106850 := by
    simpa [prefixWord, tailWord_3106850, baseEnd_3106850] using wordTrace_append hprefix tailTrace_3106850
  have hstable : (prefixWord ++ tailWord_3106850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106850).length < 2 ^ (prefixWord ++ tailWord_3106850).sum := by decide
  have hdescent : baseEnd_3106850 < baseStart_3106850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106853 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_3106853 : Nat := 118140960795 + 3106853 * 2 ^ 59
def prefixEnd_3106853 : Nat := 4983230072969 + 3 ^ 40 * 3106853 * 2
def baseEnd_3106853 : Nat := 531769637287746052349783

theorem tailTrace_3106853 : CollatzResearch.WordTrace tailWord_3106853 prefixEnd_3106853 531769637287746052349783 := by
  unfold tailWord_3106853
  simp only [CollatzResearch.WordTrace]
  refine ⟨113316238213409664093629213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75544158808939776062419475 113316238213409664093629213)
  ·
    refine ⟨42493589330028624035110955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113316238213409664093629213 42493589330028624035110955)
    ·
      refine ⟨63740383995042936052666433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42493589330028624035110955 63740383995042936052666433)
      ·
        refine ⟨47805287996282202039499825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63740383995042936052666433 47805287996282202039499825)
        ·
          refine ⟨35853965997211651529624869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47805287996282202039499825 35853965997211651529624869)
          ·
            refine ⟨6722618624477184661804663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35853965997211651529624869 6722618624477184661804663)
            ·
              refine ⟨10083927936715776992706995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6722618624477184661804663 10083927936715776992706995)
              ·
                refine ⟨15125891905073665489060493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10083927936715776992706995 15125891905073665489060493)
                ·
                  refine ⟨5672209464402624558397685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15125891905073665489060493 5672209464402624558397685)
                  ·
                    refine ⟨531769637287746052349783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5672209464402624558397685 531769637287746052349783)
                    ·
                      rfl

theorem cell23_3106853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_3106853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106853 prefixEnd_3106853 := by exact prefixLift 3106853
  have htrace : WordTrace (prefixWord ++ tailWord_3106853) baseStart_3106853 baseEnd_3106853 := by
    simpa [prefixWord, tailWord_3106853, baseEnd_3106853] using wordTrace_append hprefix tailTrace_3106853
  have hstable : (prefixWord ++ tailWord_3106853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106853).length < 2 ^ (prefixWord ++ tailWord_3106853).sum := by decide
  have hdescent : baseEnd_3106853 < baseStart_3106853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106878 : List Nat := [4, 2, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_3106878 : Nat := 118140960795 + 3106878 * 2 ^ 59
def prefixEnd_3106878 : Nat := 4983230072969 + 3 ^ 40 * 3106878 * 2
def baseEnd_3106878 : Nat := 531773916293200186412245

theorem tailTrace_3106878 : CollatzResearch.WordTrace tailWord_3106878 prefixEnd_3106878 531773916293200186412245 := by
  unfold tailWord_3106878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164643754789886670411161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75544766692212728908859525 14164643754789886670411161)
  ·
    refine ⟨10623482816092415002808371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14164643754789886670411161 10623482816092415002808371)
    ·
      refine ⟨15935224224138622504212557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10623482816092415002808371 15935224224138622504212557)
      ·
        refine ⟨5975709084051983439079709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15935224224138622504212557 5975709084051983439079709)
        ·
          refine ⟨2240890906519493789654891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5975709084051983439079709 2240890906519493789654891)
          ·
            refine ⟨3361336359779240684482337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240890906519493789654891 3361336359779240684482337)
            ·
              refine ⟨2521002269834430513361753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3361336359779240684482337 2521002269834430513361753)
              ·
                refine ⟨1890751702375822885021315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521002269834430513361753 1890751702375822885021315)
                ·
                  refine ⟨2836127553563734327531973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890751702375822885021315 2836127553563734327531973)
                  ·
                    refine ⟨531773916293200186412245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2836127553563734327531973 531773916293200186412245)
                    ·
                      rfl

theorem cell23_3106878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_3106878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106878 prefixEnd_3106878 := by exact prefixLift 3106878
  have htrace : WordTrace (prefixWord ++ tailWord_3106878) baseStart_3106878 baseEnd_3106878 := by
    simpa [prefixWord, tailWord_3106878, baseEnd_3106878] using wordTrace_append hprefix tailTrace_3106878
  have hstable : (prefixWord ++ tailWord_3106878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106878).length < 2 ^ (prefixWord ++ tailWord_3106878).sum := by decide
  have hdescent : baseEnd_3106878 < baseStart_3106878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106903 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_3106903 : Nat := 118140960795 + 3106903 * 2 ^ 59
def prefixEnd_3106903 : Nat := 4983230072969 + 3 ^ 40 * 3106903 * 2
def baseEnd_3106903 : Nat := 1595334585895962961424119

theorem tailTrace_3106903 : CollatzResearch.WordTrace tailWord_3106903 prefixEnd_3106903 1595334585895962961424119 := by
  unfold tailWord_3106903
  simp only [CollatzResearch.WordTrace]
  refine ⟨113318061863228522632949363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75545374575485681755299575 113318061863228522632949363)
  ·
    refine ⟨169977092794842783949424045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113318061863228522632949363 169977092794842783949424045)
    ·
      refine ⟨63741409798066043981034017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169977092794842783949424045 63741409798066043981034017)
      ·
        refine ⟨47806057348549532985775513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63741409798066043981034017 47806057348549532985775513)
        ·
          refine ⟨35854543011412149739331635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47806057348549532985775513 35854543011412149739331635)
          ·
            refine ⟨53781814517118224608997453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35854543011412149739331635 53781814517118224608997453)
            ·
              refine ⟨20168180443919334228374045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53781814517118224608997453 20168180443919334228374045)
              ·
                refine ⟨7563067666469750335640267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20168180443919334228374045 7563067666469750335640267)
                ·
                  refine ⟨11344601499704625503460401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7563067666469750335640267 11344601499704625503460401)
                  ·
                    refine ⟨8508451124778469127595301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11344601499704625503460401 8508451124778469127595301)
                    ·
                      refine ⟨1595334585895962961424119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8508451124778469127595301 1595334585895962961424119)
                      ·
                        rfl

theorem cell23_3106903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_3106903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106903 prefixEnd_3106903 := by exact prefixLift 3106903
  have htrace : WordTrace (prefixWord ++ tailWord_3106903) baseStart_3106903 baseEnd_3106903 := by
    simpa [prefixWord, tailWord_3106903, baseEnd_3106903] using wordTrace_append hprefix tailTrace_3106903
  have hstable : (prefixWord ++ tailWord_3106903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106903).length < 2 ^ (prefixWord ++ tailWord_3106903).sum := by decide
  have hdescent : baseEnd_3106903 < baseStart_3106903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106924 : List Nat := [2, 2, 1, 1, 3, 3, 1, 5, 1, 2, 2]
def baseStart_3106924 : Nat := 118140960795 + 3106924 * 2 ^ 59
def prefixEnd_3106924 : Nat := 4983230072969 + 3 ^ 40 * 3106924 * 2
def baseEnd_3106924 : Nat := 1595345368989707379261523

theorem tailTrace_3106924 : CollatzResearch.WordTrace tailWord_3106924 prefixEnd_3106924 1595345368989707379261523 := by
  unfold tailWord_3106924
  simp only [CollatzResearch.WordTrace]
  refine ⟨56659413898076221609731913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75545885197434962146309217 56659413898076221609731913)
  ·
    refine ⟨42494560423557166207298935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56659413898076221609731913 42494560423557166207298935)
    ·
      refine ⟨63741840635335749310948403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42494560423557166207298935 63741840635335749310948403)
      ·
        refine ⟨95612760953003623966422605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63741840635335749310948403 95612760953003623966422605)
        ·
          refine ⟨35854785357376358987408477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95612760953003623966422605 35854785357376358987408477)
          ·
            refine ⟨13445544509016134620278179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35854785357376358987408477 13445544509016134620278179)
            ·
              refine ⟨20168316763524201930417269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13445544509016134620278179 20168316763524201930417269)
              ·
                refine ⟨1890779696580393930976619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20168316763524201930417269 1890779696580393930976619)
                ·
                  refine ⟨2836169544870590896464929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890779696580393930976619 2836169544870590896464929)
                  ·
                    refine ⟨2127127158652943172348697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2836169544870590896464929 2127127158652943172348697)
                    ·
                      refine ⟨1595345368989707379261523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127127158652943172348697 1595345368989707379261523)
                      ·
                        rfl

theorem cell23_3106924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 2, 2].length) (baseStart_3106924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106924 prefixEnd_3106924 := by exact prefixLift 3106924
  have htrace : WordTrace (prefixWord ++ tailWord_3106924) baseStart_3106924 baseEnd_3106924 := by
    simpa [prefixWord, tailWord_3106924, baseEnd_3106924] using wordTrace_append hprefix tailTrace_3106924
  have hstable : (prefixWord ++ tailWord_3106924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106924).length < 2 ^ (prefixWord ++ tailWord_3106924).sum := by decide
  have hdescent : baseEnd_3106924 < baseStart_3106924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106927 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 1, 2, 3]
def baseStart_3106927 : Nat := 118140960795 + 3106927 * 2 ^ 59
def prefixEnd_3106927 : Nat := 4983230072969 + 3 ^ 40 * 3106927 * 2
def baseEnd_3106927 : Nat := 1595346909431670867524009

theorem tailTrace_3106927 : CollatzResearch.WordTrace tailWord_3106927 prefixEnd_3106927 1595346909431670867524009 := by
  unfold tailWord_3106927
  simp only [CollatzResearch.WordTrace]
  refine ⟨113318937215141574731823035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75545958143427716487882023 113318937215141574731823035)
  ·
    refine ⟨169978405822712362097734553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113318937215141574731823035 169978405822712362097734553)
    ·
      refine ⟨127483804367034271573300915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169978405822712362097734553 127483804367034271573300915)
      ·
        refine ⟨191225706550551407359951373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127483804367034271573300915 191225706550551407359951373)
        ·
          refine ⟨71709639956456777759981765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191225706550551407359951373 71709639956456777759981765)
          ·
            refine ⟨13445557491835645829996581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71709639956456777759981765 13445557491835645829996581)
            ·
              refine ⟨2521042029719183593124359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13445557491835645829996581 2521042029719183593124359)
              ·
                refine ⟨3781563044578775389686539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521042029719183593124359 3781563044578775389686539)
                ·
                  refine ⟨5672344566868163084529809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781563044578775389686539 5672344566868163084529809)
                  ·
                    refine ⟨4254258425151122313397357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5672344566868163084529809 4254258425151122313397357)
                    ·
                      refine ⟨1595346909431670867524009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4254258425151122313397357 1595346909431670867524009)
                      ·
                        rfl

theorem cell23_3106927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 2, 3].length) (baseStart_3106927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106927 prefixEnd_3106927 := by exact prefixLift 3106927
  have htrace : WordTrace (prefixWord ++ tailWord_3106927) baseStart_3106927 baseEnd_3106927 := by
    simpa [prefixWord, tailWord_3106927, baseEnd_3106927] using wordTrace_append hprefix tailTrace_3106927
  have hstable : (prefixWord ++ tailWord_3106927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106927).length < 2 ^ (prefixWord ++ tailWord_3106927).sum := by decide
  have hdescent : baseEnd_3106927 < baseStart_3106927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106934 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_3106934 : Nat := 118140960795 + 3106934 * 2 ^ 59
def prefixEnd_3106934 : Nat := 4983230072969 + 3 ^ 40 * 3106934 * 2
def baseEnd_3106934 : Nat := 531783501265417446712159

theorem tailTrace_3106934 : CollatzResearch.WordTrace tailWord_3106934 prefixEnd_3106934 531783501265417446712159 := by
  unfold tailWord_3106934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7082449532882263432957991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75546128350744143284885237 7082449532882263432957991)
  ·
    refine ⟨10623674299323395149436987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7082449532882263432957991 10623674299323395149436987)
    ·
      refine ⟨15935511448985092724155481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10623674299323395149436987 15935511448985092724155481)
      ·
        refine ⟨11951633586738819543116611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15935511448985092724155481 11951633586738819543116611)
        ·
          refine ⟨17927450380108229314674917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11951633586738819543116611 17927450380108229314674917)
          ·
            refine ⟨3361396946270292996501547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17927450380108229314674917 3361396946270292996501547)
            ·
              refine ⟨5042095419405439494752321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361396946270292996501547 5042095419405439494752321)
              ·
                refine ⟨3781571564554079621064241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5042095419405439494752321 3781571564554079621064241)
                ·
                  refine ⟨2836178673415559715798181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3781571564554079621064241 2836178673415559715798181)
                  ·
                    refine ⟨531783501265417446712159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2836178673415559715798181 531783501265417446712159)
                    ·
                      rfl

theorem cell23_3106934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_3106934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106934 prefixEnd_3106934 := by exact prefixLift 3106934
  have htrace : WordTrace (prefixWord ++ tailWord_3106934) baseStart_3106934 baseEnd_3106934 := by
    simpa [prefixWord, tailWord_3106934, baseEnd_3106934] using wordTrace_append hprefix tailTrace_3106934
  have hstable : (prefixWord ++ tailWord_3106934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106934).length < 2 ^ (prefixWord ++ tailWord_3106934).sum := by decide
  have hdescent : baseEnd_3106934 < baseStart_3106934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106964 : List Nat := [2, 4, 2, 3, 1, 2, 2, 7]
def baseStart_3106964 : Nat := 118140960795 + 3106964 * 2 ^ 59
def prefixEnd_3106964 : Nat := 4983230072969 + 3 ^ 40 * 3106964 * 2
def baseEnd_3106964 : Nat := 59087626230218045287457

theorem tailTrace_3106964 : CollatzResearch.WordTrace tailWord_3106964 prefixEnd_3106964 59087626230218045287457 := by
  unfold tailWord_3106964
  simp only [CollatzResearch.WordTrace]
  refine ⟨56660143358003765025459973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75546857810671686700613297 56660143358003765025459973)
  ·
    refine ⟨10623776879625705942273745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56660143358003765025459973 10623776879625705942273745)
    ·
      refine ⟨7967832659719279456705309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10623776879625705942273745 7967832659719279456705309)
      ·
        refine ⟨2987937247394729796264491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7967832659719279456705309 2987937247394729796264491)
        ·
          refine ⟨4481905871092094694396737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987937247394729796264491 4481905871092094694396737)
          ·
            refine ⟨3361429403319071020797553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4481905871092094694396737 3361429403319071020797553)
            ·
              refine ⟨2521072052489303265598165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3361429403319071020797553 2521072052489303265598165)
              ·
                refine ⟨59087626230218045287457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2521072052489303265598165 59087626230218045287457)
                ·
                  rfl

theorem cell23_3106964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 7].length) (baseStart_3106964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3106964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3106964 prefixEnd_3106964 := by exact prefixLift 3106964
  have htrace : WordTrace (prefixWord ++ tailWord_3106964) baseStart_3106964 baseEnd_3106964 := by
    simpa [prefixWord, tailWord_3106964, baseEnd_3106964] using wordTrace_append hprefix tailTrace_3106964
  have hstable : (prefixWord ++ tailWord_3106964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106964).length < 2 ^ (prefixWord ++ tailWord_3106964).sum := by decide
  have hdescent : baseEnd_3106964 < baseStart_3106964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107033 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 1, 7]
def baseStart_3107033 : Nat := 118140960795 + 3107033 * 2 ^ 59
def prefixEnd_3107033 : Nat := 4983230072969 + 3 ^ 40 * 3107033 * 2
def baseEnd_3107033 : Nat := 531800446127015817599507

theorem tailTrace_3107033 : CollatzResearch.WordTrace tailWord_3107033 prefixEnd_3107033 531800446127015817599507 := by
  unfold tailWord_3107033
  simp only [CollatzResearch.WordTrace]
  refine ⟨113322803352757554835181753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75548535568505036556787835 113322803352757554835181753)
  ·
    refine ⟨84992102514568166126386315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113322803352757554835181753 84992102514568166126386315)
    ·
      refine ⟨127488153771852249189579473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84992102514568166126386315 127488153771852249189579473)
      ·
        refine ⟨95616115328889186892184605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127488153771852249189579473 95616115328889186892184605)
        ·
          refine ⟨35856043248333445084569227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95616115328889186892184605 35856043248333445084569227)
          ·
            refine ⟨53784064872500167626853841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35856043248333445084569227 53784064872500167626853841)
            ·
              refine ⟨40338048654375125720140381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53784064872500167626853841 40338048654375125720140381)
              ·
                refine ⟨15126768245390672145052643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40338048654375125720140381 15126768245390672145052643)
                ·
                  refine ⟨22690152368086008217578965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15126768245390672145052643 22690152368086008217578965)
                  ·
                    refine ⟨531800446127015817599507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22690152368086008217578965 531800446127015817599507)
                    ·
                      rfl

theorem cell23_3107033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_3107033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107033 prefixEnd_3107033 := by exact prefixLift 3107033
  have htrace : WordTrace (prefixWord ++ tailWord_3107033) baseStart_3107033 baseEnd_3107033 := by
    simpa [prefixWord, tailWord_3107033, baseEnd_3107033] using wordTrace_append hprefix tailTrace_3107033
  have hstable : (prefixWord ++ tailWord_3107033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107033).length < 2 ^ (prefixWord ++ tailWord_3107033).sum := by decide
  have hdescent : baseEnd_3107033 < baseStart_3107033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107050 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3107050 : Nat := 118140960795 + 3107050 * 2 ^ 59
def prefixEnd_3107050 : Nat := 4983230072969 + 3 ^ 40 * 3107050 * 2
def baseEnd_3107050 : Nat := 531803355850724628761981

theorem tailTrace_3107050 : CollatzResearch.WordTrace tailWord_3107050 prefixEnd_3107050 531803355850724628761981 := by
  unfold tailWord_3107050
  simp only [CollatzResearch.WordTrace]
  refine ⟨28330855848423991684637651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75548948929130644492367069 28330855848423991684637651)
  ·
    refine ⟨42496283772635987526956477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28330855848423991684637651 42496283772635987526956477)
    ·
      refine ⟨15936106414738495322608679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42496283772635987526956477 15936106414738495322608679)
      ·
        refine ⟨23904159622107742983913019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15936106414738495322608679 23904159622107742983913019)
        ·
          refine ⟨35856239433161614475869529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23904159622107742983913019 35856239433161614475869529)
          ·
            refine ⟨26892179574871210856902147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35856239433161614475869529 26892179574871210856902147)
            ·
              refine ⟨40338269362306816285353221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26892179574871210856902147 40338269362306816285353221)
              ·
                refine ⟨7563425505432528053503729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40338269362306816285353221 7563425505432528053503729)
                ·
                  refine ⟨5672569129074396040127797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7563425505432528053503729 5672569129074396040127797)
                  ·
                    refine ⟨531803355850724628761981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5672569129074396040127797 531803355850724628761981)
                    ·
                      rfl

theorem cell23_3107050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3107050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107050 prefixEnd_3107050 := by exact prefixLift 3107050
  have htrace : WordTrace (prefixWord ++ tailWord_3107050) baseStart_3107050 baseEnd_3107050 := by
    simpa [prefixWord, tailWord_3107050, baseEnd_3107050] using wordTrace_append hprefix tailTrace_3107050
  have hstable : (prefixWord ++ tailWord_3107050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107050).length < 2 ^ (prefixWord ++ tailWord_3107050).sum := by decide
  have hdescent : baseEnd_3107050 < baseStart_3107050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107187 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 2, 4]
def baseStart_3107187 : Nat := 118140960795 + 3107187 * 2 ^ 59
def prefixEnd_3107187 : Nat := 4983230072969 + 3 ^ 40 * 3107187 * 2
def baseEnd_3107187 : Nat := 531826804800613283424271

theorem tailTrace_3107187 : CollatzResearch.WordTrace tailWord_3107187 prefixEnd_3107187 531826804800613283424271 := by
  unfold tailWord_3107187
  simp only [CollatzResearch.WordTrace]
  refine ⟨113328420194199639136287815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75552280129466426090858543 113328420194199639136287815)
  ·
    refine ⟨169992630291299458704431723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113328420194199639136287815 169992630291299458704431723)
    ·
      refine ⟨254988945436949188056647585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169992630291299458704431723 254988945436949188056647585)
      ·
        refine ⟨191241709077711891042485689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254988945436949188056647585 191241709077711891042485689)
        ·
          refine ⟨143431281808283918281864267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191241709077711891042485689 143431281808283918281864267)
          ·
            refine ⟨215146922712425877422796401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143431281808283918281864267 215146922712425877422796401)
            ·
              refine ⟨161360192034319408067097301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215146922712425877422796401 161360192034319408067097301)
              ·
                refine ⟨3781879500804361126572593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161360192034319408067097301 3781879500804361126572593)
                ·
                  refine ⟨2836409625603270844929445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3781879500804361126572593 2836409625603270844929445)
                  ·
                    refine ⟨531826804800613283424271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2836409625603270844929445 531826804800613283424271)
                    ·
                      rfl

theorem cell23_3107187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 4].length) (baseStart_3107187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107187 prefixEnd_3107187 := by exact prefixLift 3107187
  have htrace : WordTrace (prefixWord ++ tailWord_3107187) baseStart_3107187 baseEnd_3107187 := by
    simpa [prefixWord, tailWord_3107187, baseEnd_3107187] using wordTrace_append hprefix tailTrace_3107187
  have hstable : (prefixWord ++ tailWord_3107187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107187).length < 2 ^ (prefixWord ++ tailWord_3107187).sum := by decide
  have hdescent : baseEnd_3107187 < baseStart_3107187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107207 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_3107207 : Nat := 118140960795 + 3107207 * 2 ^ 59
def prefixEnd_3107207 : Nat := 4983230072969 + 3 ^ 40 * 3107207 * 2
def baseEnd_3107207 : Nat := 1595490684014929772022721

theorem tailTrace_3107207 : CollatzResearch.WordTrace tailWord_3107207 prefixEnd_3107207 1595490684014929772022721 := by
  unfold tailWord_3107207
  simp only [CollatzResearch.WordTrace]
  refine ⟨113329149654127182552015875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75552766436084788368010583 113329149654127182552015875)
  ·
    refine ⟨169993724481190773828023813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113329149654127182552015875 169993724481190773828023813)
    ·
      refine ⟨31873823340223270092754465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169993724481190773828023813 31873823340223270092754465)
      ·
        refine ⟨23905367505167452569565849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31873823340223270092754465 23905367505167452569565849)
        ·
          refine ⟨17929025628875589427174387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23905367505167452569565849 17929025628875589427174387)
          ·
            refine ⟨26893538443313384140761581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17929025628875589427174387 26893538443313384140761581)
            ·
              refine ⟨10085076916242519052785593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26893538443313384140761581 10085076916242519052785593)
              ·
                refine ⟨7563807687181889289589195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10085076916242519052785593 7563807687181889289589195)
                ·
                  refine ⟨11345711530772833934383793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7563807687181889289589195 11345711530772833934383793)
                  ·
                    refine ⟨8509283648079625450787845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11345711530772833934383793 8509283648079625450787845)
                    ·
                      refine ⟨1595490684014929772022721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8509283648079625450787845 1595490684014929772022721)
                      ·
                        rfl

theorem cell23_3107207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_3107207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107207 prefixEnd_3107207 := by exact prefixLift 3107207
  have htrace : WordTrace (prefixWord ++ tailWord_3107207) baseStart_3107207 baseEnd_3107207 := by
    simpa [prefixWord, tailWord_3107207, baseEnd_3107207] using wordTrace_append hprefix tailTrace_3107207
  have hstable : (prefixWord ++ tailWord_3107207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107207).length < 2 ^ (prefixWord ++ tailWord_3107207).sum := by decide
  have hdescent : baseEnd_3107207 < baseStart_3107207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107214 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3107214 : Nat := 118140960795 + 3107214 * 2 ^ 59
def prefixEnd_3107214 : Nat := 4983230072969 + 3 ^ 40 * 3107214 * 2
def baseEnd_3107214 : Nat := 1595494278379511244635189

theorem tailTrace_3107214 : CollatzResearch.WordTrace tailWord_3107214 prefixEnd_3107214 1595494278379511244635189 := by
  unfold tailWord_3107214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14166175620637727843440087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75552936643401215165013797 14166175620637727843440087)
  ·
    refine ⟨21249263430956591765160131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14166175620637727843440087 21249263430956591765160131)
    ·
      refine ⟨31873895146434887647740197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21249263430956591765160131 31873895146434887647740197)
      ·
        refine ⟨5976355339956541433951287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31873895146434887647740197 5976355339956541433951287)
        ·
          refine ⟨8964533009934812150926931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5976355339956541433951287 8964533009934812150926931)
          ·
            refine ⟨13446799514902218226390397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8964533009934812150926931 13446799514902218226390397)
            ·
              refine ⟨5042549818088331834896399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13446799514902218226390397 5042549818088331834896399)
              ·
                refine ⟨7563824727132497752344599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5042549818088331834896399 7563824727132497752344599)
                ·
                  refine ⟨11345737090698746628516899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7563824727132497752344599 11345737090698746628516899)
                  ·
                    refine ⟨17018605636048119942775349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11345737090698746628516899 17018605636048119942775349)
                    ·
                      refine ⟨1595494278379511244635189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17018605636048119942775349 1595494278379511244635189)
                      ·
                        rfl

theorem cell23_3107214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3107214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107214 prefixEnd_3107214 := by exact prefixLift 3107214
  have htrace : WordTrace (prefixWord ++ tailWord_3107214) baseStart_3107214 baseEnd_3107214 := by
    simpa [prefixWord, tailWord_3107214, baseEnd_3107214] using wordTrace_append hprefix tailTrace_3107214
  have hstable : (prefixWord ++ tailWord_3107214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107214).length < 2 ^ (prefixWord ++ tailWord_3107214).sum := by decide
  have hdescent : baseEnd_3107214 < baseStart_3107214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107265 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3107265 : Nat := 118140960795 + 3107265 * 2 ^ 59
def prefixEnd_3107265 : Nat := 4983230072969 + 3 ^ 40 * 3107265 * 2
def baseEnd_3107265 : Nat := 1595520465892890545097455

theorem tailTrace_3107265 : CollatzResearch.WordTrace tailWord_3107265 prefixEnd_3107265 1595520465892890545097455 := by
  unfold tailWord_3107265
  simp only [CollatzResearch.WordTrace]
  refine ⟨113331265087917058457627249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75554176725278038971751499 113331265087917058457627249)
  ·
    refine ⟨84998448815937793843220437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113331265087917058457627249 84998448815937793843220437)
    ·
      refine ⟨1992151144123542043200479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 84998448815937793843220437 1992151144123542043200479)
      ·
        refine ⟨2988226716185313064800719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992151144123542043200479 2988226716185313064800719)
        ·
          refine ⟨4482340074277969597201079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988226716185313064800719 4482340074277969597201079)
          ·
            refine ⟨6723510111416954395801619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482340074277969597201079 6723510111416954395801619)
            ·
              refine ⟨10085265167125431593702429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723510111416954395801619 10085265167125431593702429)
              ·
                refine ⟨3781974437672036847638411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10085265167125431593702429 3781974437672036847638411)
                ·
                  refine ⟨5672961656508055271457617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781974437672036847638411 5672961656508055271457617)
                  ·
                    refine ⟨4254721242381041453593213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5672961656508055271457617 4254721242381041453593213)
                    ·
                      refine ⟨1595520465892890545097455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4254721242381041453593213 1595520465892890545097455)
                      ·
                        rfl

theorem cell23_3107265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3107265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107265 prefixEnd_3107265 := by exact prefixLift 3107265
  have htrace : WordTrace (prefixWord ++ tailWord_3107265) baseStart_3107265 baseEnd_3107265 := by
    simpa [prefixWord, tailWord_3107265, baseEnd_3107265] using wordTrace_append hprefix tailTrace_3107265
  have hstable : (prefixWord ++ tailWord_3107265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107265).length < 2 ^ (prefixWord ++ tailWord_3107265).sum := by decide
  have hdescent : baseEnd_3107265 < baseStart_3107265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107271 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_3107271 : Nat := 118140960795 + 3107271 * 2 ^ 59
def prefixEnd_3107271 : Nat := 4983230072969 + 3 ^ 40 * 3107271 * 2
def baseEnd_3107271 : Nat := 1595523546776817521622427

theorem tailTrace_3107271 : CollatzResearch.WordTrace tailWord_3107271 prefixEnd_3107271 1595523546776817521622427 := by
  unfold tailWord_3107271
  simp only [CollatzResearch.WordTrace]
  refine ⟨113331483925895321482345667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75554322617263547654897111 113331483925895321482345667)
  ·
    refine ⟨169997225888842982223518501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113331483925895321482345667 169997225888842982223518501)
    ·
      refine ⟨31874479854158059166909719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169997225888842982223518501 31874479854158059166909719)
      ·
        refine ⟨47811719781237088750364579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31874479854158059166909719 47811719781237088750364579)
        ·
          refine ⟨71717579671855633125546869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47811719781237088750364579 71717579671855633125546869)
          ·
            refine ⟨6723523094236465605520019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71717579671855633125546869 6723523094236465605520019)
            ·
              refine ⟨10085284641354698408280029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723523094236465605520019 10085284641354698408280029)
              ·
                refine ⟨3781981740508011903105011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10085284641354698408280029 3781981740508011903105011)
                ·
                  refine ⟨5672972610762017854657517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781981740508011903105011 5672972610762017854657517)
                  ·
                    refine ⟨2127364729035756695496569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5672972610762017854657517 2127364729035756695496569)
                    ·
                      refine ⟨1595523546776817521622427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127364729035756695496569 1595523546776817521622427)
                      ·
                        rfl

theorem cell23_3107271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_3107271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107271 prefixEnd_3107271 := by exact prefixLift 3107271
  have htrace : WordTrace (prefixWord ++ tailWord_3107271) baseStart_3107271 baseEnd_3107271 := by
    simpa [prefixWord, tailWord_3107271, baseEnd_3107271] using wordTrace_append hprefix tailTrace_3107271
  have hstable : (prefixWord ++ tailWord_3107271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107271).length < 2 ^ (prefixWord ++ tailWord_3107271).sum := by decide
  have hdescent : baseEnd_3107271 < baseStart_3107271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107280 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_3107280 : Nat := 118140960795 + 3107280 * 2 ^ 59
def prefixEnd_3107280 : Nat := 4983230072969 + 3 ^ 40 * 3107280 * 2
def baseEnd_3107280 : Nat := 1595528168102707986409885

theorem tailTrace_3107280 : CollatzResearch.WordTrace tailWord_3107280 prefixEnd_3107280 1595528168102707986409885 := by
  unfold tailWord_3107280
  simp only [CollatzResearch.WordTrace]
  refine ⟨56665906091431358009711647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75554541455241810679615529 56665906091431358009711647)
  ·
    refine ⟨84998859137147037014567471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56665906091431358009711647 84998859137147037014567471)
    ·
      refine ⟨127498288705720555521851207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84998859137147037014567471 127498288705720555521851207)
      ·
        refine ⟨191247433058580833282776811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127498288705720555521851207 191247433058580833282776811)
        ·
          refine ⟨286871149587871249924165217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191247433058580833282776811 286871149587871249924165217)
          ·
            refine ⟨215153362190903437443123913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286871149587871249924165217 215153362190903437443123913)
            ·
              refine ⟨161365021643177578082342935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215153362190903437443123913 161365021643177578082342935)
              ·
                refine ⟨242047532464766367123514403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161365021643177578082342935 242047532464766367123514403)
                ·
                  refine ⟨363071298697149550685271605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242047532464766367123514403 363071298697149550685271605)
                  ·
                    refine ⟨34037934252857770376744213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 363071298697149550685271605 34037934252857770376744213)
                    ·
                      refine ⟨1595528168102707986409885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34037934252857770376744213 1595528168102707986409885)
                      ·
                        rfl

theorem cell23_3107280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_3107280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107280 prefixEnd_3107280 := by exact prefixLift 3107280
  have htrace : WordTrace (prefixWord ++ tailWord_3107280) baseStart_3107280 baseEnd_3107280 := by
    simpa [prefixWord, tailWord_3107280, baseEnd_3107280] using wordTrace_append hprefix tailTrace_3107280
  have hstable : (prefixWord ++ tailWord_3107280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107280).length < 2 ^ (prefixWord ++ tailWord_3107280).sum := by decide
  have hdescent : baseEnd_3107280 < baseStart_3107280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107297 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_3107297 : Nat := 118140960795 + 3107297 * 2 ^ 59
def prefixEnd_3107297 : Nat := 4983230072969 + 3 ^ 40 * 3107297 * 2
def baseEnd_3107297 : Nat := 1595536897273834419897307

theorem tailTrace_3107297 : CollatzResearch.WordTrace tailWord_3107297 prefixEnd_3107297 1595536897273834419897307 := by
  unfold tailWord_3107297
  simp only [CollatzResearch.WordTrace]
  refine ⟨113332432223801127922792145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75554954815867418615194763 113332432223801127922792145)
  ·
    refine ⟨84999324167850845942094109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113332432223801127922792145 84999324167850845942094109)
    ·
      refine ⟨31874746562944067228285291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84999324167850845942094109 31874746562944067228285291)
      ·
        refine ⟨47812119844416100842427937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31874746562944067228285291 47812119844416100842427937)
        ·
          refine ⟨35859089883312075631820953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47812119844416100842427937 35859089883312075631820953)
          ·
            refine ⟨26894317412484056723865715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35859089883312075631820953 26894317412484056723865715)
            ·
              refine ⟨40341476118726085085798573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26894317412484056723865715 40341476118726085085798573)
              ·
                refine ⟨15128053544522281907174465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40341476118726085085798573 15128053544522281907174465)
                ·
                  refine ⟨11346040158391711430380849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15128053544522281907174465 11346040158391711430380849)
                  ·
                    refine ⟨8509530118793783572785637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11346040158391711430380849 8509530118793783572785637)
                    ·
                      refine ⟨1595536897273834419897307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8509530118793783572785637 1595536897273834419897307)
                      ·
                        rfl

theorem cell23_3107297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_3107297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107297 prefixEnd_3107297 := by exact prefixLift 3107297
  have htrace : WordTrace (prefixWord ++ tailWord_3107297) baseStart_3107297 baseEnd_3107297 := by
    simpa [prefixWord, tailWord_3107297, baseEnd_3107297] using wordTrace_append hprefix tailTrace_3107297
  have hstable : (prefixWord ++ tailWord_3107297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107297).length < 2 ^ (prefixWord ++ tailWord_3107297).sum := by decide
  have hdescent : baseEnd_3107297 < baseStart_3107297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107347 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 5]
def baseStart_3107347 : Nat := 118140960795 + 3107347 * 2 ^ 59
def prefixEnd_3107347 : Nat := 4983230072969 + 3 ^ 40 * 3107347 * 2
def baseEnd_3107347 : Nat := 1595562571306559224272077

theorem tailTrace_3107347 : CollatzResearch.WordTrace tailWord_3107347 prefixEnd_3107347 1595562571306559224272077 := by
  unfold tailWord_3107347
  simp only [CollatzResearch.WordTrace]
  refine ⟨113334255873619986462112295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75556170582413324308074863 113334255873619986462112295)
  ·
    refine ⟨170001383810429979693168443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113334255873619986462112295 170001383810429979693168443)
    ·
      refine ⟨255002075715644969539752665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170001383810429979693168443 255002075715644969539752665)
      ·
        refine ⟨191251556786733727154814499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255002075715644969539752665 191251556786733727154814499)
        ·
          refine ⟨286877335180100590732221749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191251556786733727154814499 286877335180100590732221749)
          ·
            refine ⟨26894750173134430381145789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286877335180100590732221749 26894750173134430381145789)
            ·
              refine ⟨10085531314925411392929671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26894750173134430381145789 10085531314925411392929671)
              ·
                refine ⟨15128296972388117089394507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10085531314925411392929671 15128296972388117089394507)
                ·
                  refine ⟨22692445458582175634091761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15128296972388117089394507 22692445458582175634091761)
                  ·
                    refine ⟨17019334093936631725568821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22692445458582175634091761 17019334093936631725568821)
                    ·
                      refine ⟨1595562571306559224272077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17019334093936631725568821 1595562571306559224272077)
                      ·
                        rfl

theorem cell23_3107347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_3107347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107347 prefixEnd_3107347 := by exact prefixLift 3107347
  have htrace : WordTrace (prefixWord ++ tailWord_3107347) baseStart_3107347 baseEnd_3107347 := by
    simpa [prefixWord, tailWord_3107347, baseEnd_3107347] using wordTrace_append hprefix tailTrace_3107347
  have hstable : (prefixWord ++ tailWord_3107347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107347).length < 2 ^ (prefixWord ++ tailWord_3107347).sum := by decide
  have hdescent : baseEnd_3107347 < baseStart_3107347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107422 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3107422 : Nat := 118140960795 + 3107422 * 2 ^ 59
def prefixEnd_3107422 : Nat := 4983230072969 + 3 ^ 40 * 3107422 * 2
def baseEnd_3107422 : Nat := 531867027451882143611411

theorem tailTrace_3107422 : CollatzResearch.WordTrace tailWord_3107422 prefixEnd_3107422 531867027451882143611411 := by
  unfold tailWord_3107422
  simp only [CollatzResearch.WordTrace]
  refine ⟨14167123918543534283886565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75557994232232182847395013 14167123918543534283886565)
  ·
    refine ⟨2656335734726912678228731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14167123918543534283886565 2656335734726912678228731)
    ·
      refine ⟨3984503602090369017343097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656335734726912678228731 3984503602090369017343097)
      ·
        refine ⟨2988377701567776763007323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3984503602090369017343097 2988377701567776763007323)
        ·
          refine ⟨4482566552351665144510985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988377701567776763007323 4482566552351665144510985)
          ·
            refine ⟨3361924914263748858383239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4482566552351665144510985 3361924914263748858383239)
            ·
              refine ⟨5042887371395623287574859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361924914263748858383239 5042887371395623287574859)
              ·
                refine ⟨7564331057093434931362289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5042887371395623287574859 7564331057093434931362289)
                ·
                  refine ⟨5673248292820076198521717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7564331057093434931362289 5673248292820076198521717)
                  ·
                    refine ⟨531867027451882143611411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5673248292820076198521717 531867027451882143611411)
                    ·
                      rfl

theorem cell23_3107422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3107422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107422 prefixEnd_3107422 := by exact prefixLift 3107422
  have htrace : WordTrace (prefixWord ++ tailWord_3107422) baseStart_3107422 baseEnd_3107422 := by
    simpa [prefixWord, tailWord_3107422, baseEnd_3107422] using wordTrace_append hprefix tailTrace_3107422
  have hstable : (prefixWord ++ tailWord_3107422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107422).length < 2 ^ (prefixWord ++ tailWord_3107422).sum := by decide
  have hdescent : baseEnd_3107422 < baseStart_3107422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107481 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 4]
def baseStart_3107481 : Nat := 118140960795 + 3107481 * 2 ^ 59
def prefixEnd_3107481 : Nat := 4983230072969 + 3 ^ 40 * 3107481 * 2
def baseEnd_3107481 : Nat := 1595631377714261699996461

theorem tailTrace_3107481 : CollatzResearch.WordTrace tailWord_3107481 prefixEnd_3107481 1595631377714261699996461 := by
  unfold tailWord_3107481
  simp only [CollatzResearch.WordTrace]
  refine ⟨113339143255134527347490297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75559428836756351564993531 113339143255134527347490297)
  ·
    refine ⟨85004357441350895510617723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113339143255134527347490297 85004357441350895510617723)
    ·
      refine ⟨127506536162026343265926585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85004357441350895510617723 127506536162026343265926585)
      ·
        refine ⟨95629902121519757449444939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127506536162026343265926585 95629902121519757449444939)
        ·
          refine ⟨143444853182279636174167409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95629902121519757449444939 143444853182279636174167409)
          ·
            refine ⟨107583639886709727130625557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143444853182279636174167409 107583639886709727130625557)
            ·
              refine ⟨5042983119689518459248073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107583639886709727130625557 5042983119689518459248073)
              ·
                refine ⟨3782237339767138844436055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5042983119689518459248073 3782237339767138844436055)
                ·
                  refine ⟨5673356009650708266654083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3782237339767138844436055 5673356009650708266654083)
                  ·
                    refine ⟨8510034014476062399981125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5673356009650708266654083 8510034014476062399981125)
                    ·
                      refine ⟨1595631377714261699996461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8510034014476062399981125 1595631377714261699996461)
                      ·
                        rfl

theorem cell23_3107481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_3107481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107481 prefixEnd_3107481 := by exact prefixLift 3107481
  have htrace : WordTrace (prefixWord ++ tailWord_3107481) baseStart_3107481 baseEnd_3107481 := by
    simpa [prefixWord, tailWord_3107481, baseEnd_3107481] using wordTrace_append hprefix tailTrace_3107481
  have hstable : (prefixWord ++ tailWord_3107481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107481).length < 2 ^ (prefixWord ++ tailWord_3107481).sum := by decide
  have hdescent : baseEnd_3107481 < baseStart_3107481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107501 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3107501 : Nat := 118140960795 + 3107501 * 2 ^ 59
def prefixEnd_3107501 : Nat := 4983230072969 + 3 ^ 40 * 3107501 * 2
def baseEnd_3107501 : Nat := 1595641647327351621746369

theorem tailTrace_3107501 : CollatzResearch.WordTrace tailWord_3107501 prefixEnd_3107501 1595641647327351621746369 := by
  unfold tailWord_3107501
  simp only [CollatzResearch.WordTrace]
  refine ⟨113339872715062070763218357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75559915143374713842145571 113339872715062070763218357)
  ·
    refine ⟨10625613067037069134051721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113339872715062070763218357 10625613067037069134051721)
    ·
      refine ⟨7969209800277801850538791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10625613067037069134051721 7969209800277801850538791)
      ·
        refine ⟨11953814700416702775808187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7969209800277801850538791 11953814700416702775808187)
        ·
          refine ⟨17930722050625054163712281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11953814700416702775808187 17930722050625054163712281)
          ·
            refine ⟨13448041537968790622784211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17930722050625054163712281 13448041537968790622784211)
            ·
              refine ⟨20172062306953185934176317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13448041537968790622784211 20172062306953185934176317)
              ·
                refine ⟨7564523365107444725316119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20172062306953185934176317 7564523365107444725316119)
                ·
                  refine ⟨11346785047661167087974179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7564523365107444725316119 11346785047661167087974179)
                  ·
                    refine ⟨17020177571491750631961269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11346785047661167087974179 17020177571491750631961269)
                    ·
                      refine ⟨1595641647327351621746369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17020177571491750631961269 1595641647327351621746369)
                      ·
                        rfl

theorem cell23_3107501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3107501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107501 prefixEnd_3107501 := by exact prefixLift 3107501
  have htrace : WordTrace (prefixWord ++ tailWord_3107501) baseStart_3107501 baseEnd_3107501 := by
    simpa [prefixWord, tailWord_3107501, baseEnd_3107501] using wordTrace_append hprefix tailTrace_3107501
  have hstable : (prefixWord ++ tailWord_3107501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107501).length < 2 ^ (prefixWord ++ tailWord_3107501).sum := by decide
  have hdescent : baseEnd_3107501 < baseStart_3107501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107548 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3107548 : Nat := 118140960795 + 3107548 * 2 ^ 59
def prefixEnd_3107548 : Nat := 4983230072969 + 3 ^ 40 * 3107548 * 2
def baseEnd_3107548 : Nat := 1595665780918112937858653

theorem tailTrace_3107548 : CollatzResearch.WordTrace tailWord_3107548 prefixEnd_3107548 1595665780918112937858653 := by
  unfold tailWord_3107548
  simp only [CollatzResearch.WordTrace]
  refine ⟨56670793472945898895089649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75561057963927865193452865 56670793472945898895089649)
  ·
    refine ⟨42503095104709424171317237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56670793472945898895089649 42503095104709424171317237)
    ·
      refine ⟨3984665166066508516060991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42503095104709424171317237 3984665166066508516060991)
      ·
        refine ⟨5976997749099762774091487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3984665166066508516060991 5976997749099762774091487)
        ·
          refine ⟨8965496623649644161137231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5976997749099762774091487 8965496623649644161137231)
          ·
            refine ⟨13448244935474466241705847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8965496623649644161137231 13448244935474466241705847)
            ·
              refine ⟨20172367403211699362558771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13448244935474466241705847 20172367403211699362558771)
              ·
                refine ⟨30258551104817549043838157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20172367403211699362558771 30258551104817549043838157)
                ·
                  refine ⟨11346956664306580891439309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30258551104817549043838157 11346956664306580891439309)
                  ·
                    refine ⟨4255108749114967834289741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11346956664306580891439309 4255108749114967834289741)
                    ·
                      refine ⟨1595665780918112937858653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4255108749114967834289741 1595665780918112937858653)
                      ·
                        rfl

theorem cell23_3107548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3107548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107548 prefixEnd_3107548 := by exact prefixLift 3107548
  have htrace : WordTrace (prefixWord ++ tailWord_3107548) baseStart_3107548 baseEnd_3107548 := by
    simpa [prefixWord, tailWord_3107548, baseEnd_3107548] using wordTrace_append hprefix tailTrace_3107548
  have hstable : (prefixWord ++ tailWord_3107548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107548).length < 2 ^ (prefixWord ++ tailWord_3107548).sum := by decide
  have hdescent : baseEnd_3107548 < baseStart_3107548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107564 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_3107564 : Nat := 118140960795 + 3107564 * 2 ^ 59
def prefixEnd_3107564 : Nat := 4983230072969 + 3 ^ 40 * 3107564 * 2
def baseEnd_3107564 : Nat := 531891332202861625086193

theorem tailTrace_3107564 : CollatzResearch.WordTrace tailWord_3107564 prefixEnd_3107564 531891332202861625086193 := by
  unfold tailWord_3107564
  simp only [CollatzResearch.WordTrace]
  refine ⟨56671085256916916261380873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75561447009222555015174497 56671085256916916261380873)
  ·
    refine ⟨42503313942687687196035655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56671085256916916261380873 42503313942687687196035655)
    ·
      refine ⟨63754970914031530794053483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42503313942687687196035655 63754970914031530794053483)
      ·
        refine ⟨95632456371047296191080225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63754970914031530794053483 95632456371047296191080225)
        ·
          refine ⟨71724342278285472143310169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95632456371047296191080225 71724342278285472143310169)
          ·
            refine ⟨53793256708714104107482627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71724342278285472143310169 53793256708714104107482627)
            ·
              refine ⟨80689885063071156161223941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53793256708714104107482627 80689885063071156161223941)
              ·
                refine ⟨15129353449325841780229489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80689885063071156161223941 15129353449325841780229489)
                ·
                  refine ⟨11347015086994381335172117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15129353449325841780229489 11347015086994381335172117)
                  ·
                    refine ⟨531891332202861625086193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11347015086994381335172117 531891332202861625086193)
                    ·
                      rfl

theorem cell23_3107564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_3107564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107564 prefixEnd_3107564 := by exact prefixLift 3107564
  have htrace : WordTrace (prefixWord ++ tailWord_3107564) baseStart_3107564 baseEnd_3107564 := by
    simpa [prefixWord, tailWord_3107564, baseEnd_3107564] using wordTrace_append hprefix tailTrace_3107564
  have hstable : (prefixWord ++ tailWord_3107564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107564).length < 2 ^ (prefixWord ++ tailWord_3107564).sum := by decide
  have hdescent : baseEnd_3107564 < baseStart_3107564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107565 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3107565 : Nat := 118140960795 + 3107565 * 2 ^ 59
def prefixEnd_3107565 : Nat := 4983230072969 + 3 ^ 40 * 3107565 * 2
def baseEnd_3107565 : Nat := 1595674510089239371346075

theorem tailTrace_3107565 : CollatzResearch.WordTrace tailWord_3107565 prefixEnd_3107565 1595674510089239371346075 := by
  unfold tailWord_3107565
  simp only [CollatzResearch.WordTrace]
  refine ⟨113342206986830209693548149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75561471324553473129032099 113342206986830209693548149)
  ·
    refine ⟨10625831905015332158770139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113342206986830209693548149 10625831905015332158770139)
    ·
      refine ⟨15938747857522998238155209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10625831905015332158770139 15938747857522998238155209)
      ·
        refine ⟨11954060893142248678616407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15938747857522998238155209 11954060893142248678616407)
        ·
          refine ⟨17931091339713373017924611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11954060893142248678616407 17931091339713373017924611)
          ·
            refine ⟨26896637009570059526886917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17931091339713373017924611 26896637009570059526886917)
            ·
              refine ⟨5043119439294386161291297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26896637009570059526886917 5043119439294386161291297)
              ·
                refine ⟨3782339579470789620968473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5043119439294386161291297 3782339579470789620968473)
                ·
                  refine ⟨2836754684603092215726355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3782339579470789620968473 2836754684603092215726355)
                  ·
                    refine ⟨4255132026904638323589533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2836754684603092215726355 4255132026904638323589533)
                    ·
                      refine ⟨1595674510089239371346075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4255132026904638323589533 1595674510089239371346075)
                      ·
                        rfl

theorem cell23_3107565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3107565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107565 prefixEnd_3107565 := by exact prefixLift 3107565
  have htrace : WordTrace (prefixWord ++ tailWord_3107565) baseStart_3107565 baseEnd_3107565 := by
    simpa [prefixWord, tailWord_3107565, baseEnd_3107565] using wordTrace_append hprefix tailTrace_3107565
  have hstable : (prefixWord ++ tailWord_3107565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107565).length < 2 ^ (prefixWord ++ tailWord_3107565).sum := by decide
  have hdescent : baseEnd_3107565 < baseStart_3107565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107571 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 5, 4, 2]
def baseStart_3107571 : Nat := 118140960795 + 3107571 * 2 ^ 59
def prefixEnd_3107571 : Nat := 4983230072969 + 3 ^ 40 * 3107571 * 2
def baseEnd_3107571 : Nat := 1595677590973166347871047

theorem tailTrace_3107571 : CollatzResearch.WordTrace tailWord_3107571 prefixEnd_3107571 1595677590973166347871047 := by
  unfold tailWord_3107571
  simp only [CollatzResearch.WordTrace]
  refine ⟨113342425824808472718266567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75561617216538981812177711 113342425824808472718266567)
  ·
    refine ⟨170013638737212709077399851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113342425824808472718266567 170013638737212709077399851)
    ·
      refine ⟨255020458105819063616099777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170013638737212709077399851 255020458105819063616099777)
      ·
        refine ⟨191265343579364297712074833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255020458105819063616099777 191265343579364297712074833)
        ·
          refine ⟨143449007684523223284056125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191265343579364297712074833 143449007684523223284056125)
          ·
            refine ⟨53793377881696208731521047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143449007684523223284056125 53793377881696208731521047)
            ·
              refine ⟨80690066822544313097281571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53793377881696208731521047 80690066822544313097281571)
              ·
                refine ⟨121035100233816469645922357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80690066822544313097281571 121035100233816469645922357)
                ·
                  refine ⟨11347040646920294029305221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121035100233816469645922357 11347040646920294029305221)
                  ·
                    refine ⟨2127570121297555130494729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11347040646920294029305221 2127570121297555130494729)
                    ·
                      refine ⟨1595677590973166347871047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127570121297555130494729 1595677590973166347871047)
                      ·
                        rfl

theorem cell23_3107571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 4, 2].length) (baseStart_3107571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107571 prefixEnd_3107571 := by exact prefixLift 3107571
  have htrace : WordTrace (prefixWord ++ tailWord_3107571) baseStart_3107571 baseEnd_3107571 := by
    simpa [prefixWord, tailWord_3107571, baseEnd_3107571] using wordTrace_append hprefix tailTrace_3107571
  have hstable : (prefixWord ++ tailWord_3107571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107571).length < 2 ^ (prefixWord ++ tailWord_3107571).sum := by decide
  have hdescent : baseEnd_3107571 < baseStart_3107571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107572 : List Nat := [2, 6, 1, 1, 3, 1, 1, 8]
def baseStart_3107572 : Nat := 118140960795 + 3107572 * 2 ^ 59
def prefixEnd_3107572 : Nat := 4983230072969 + 3 ^ 40 * 3107572 * 2
def baseEnd_3107572 : Nat := 59099189053845216442909

theorem tailTrace_3107572 : CollatzResearch.WordTrace tailWord_3107572 prefixEnd_3107572 59099189053845216442909 := by
  unfold tailWord_3107572
  simp only [CollatzResearch.WordTrace]
  refine ⟨56671231148902424944526485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75561641531869899926035313 56671231148902424944526485)
  ·
    refine ⟨2656463960104801169274679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56671231148902424944526485 2656463960104801169274679)
    ·
      refine ⟨3984695940157201753912019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656463960104801169274679 3984695940157201753912019)
      ·
        refine ⟨5977043910235802630868029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3984695940157201753912019 5977043910235802630868029)
        ·
          refine ⟨2241391466338425986575511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5977043910235802630868029 2241391466338425986575511)
          ·
            refine ⟨3362087199507638979863267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241391466338425986575511 3362087199507638979863267)
            ·
              refine ⟨5043130799261458469794901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362087199507638979863267 5043130799261458469794901)
              ·
                refine ⟨59099189053845216442909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5043130799261458469794901 59099189053845216442909)
                ·
                  rfl

theorem cell23_3107572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 8].length) (baseStart_3107572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107572 prefixEnd_3107572 := by exact prefixLift 3107572
  have htrace : WordTrace (prefixWord ++ tailWord_3107572) baseStart_3107572 baseEnd_3107572 := by
    simpa [prefixWord, tailWord_3107572, baseEnd_3107572] using wordTrace_append hprefix tailTrace_3107572
  have hstable : (prefixWord ++ tailWord_3107572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107572).length < 2 ^ (prefixWord ++ tailWord_3107572).sum := by decide
  have hdescent : baseEnd_3107572 < baseStart_3107572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107621 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_3107621 : Nat := 118140960795 + 3107621 * 2 ^ 59
def prefixEnd_3107621 : Nat := 4983230072969 + 3 ^ 40 * 3107621 * 2
def baseEnd_3107621 : Nat := 1595703265005891152245817

theorem tailTrace_3107621 : CollatzResearch.WordTrace tailWord_3107621 prefixEnd_3107621 1595703265005891152245817 := by
  unfold tailWord_3107621
  simp only [CollatzResearch.WordTrace]
  refine ⟨113344249474627331257586717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75562832983084887505057811 113344249474627331257586717)
  ·
    refine ⟨42504093552985249221595019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113344249474627331257586717 42504093552985249221595019)
    ·
      refine ⟨63756140329477873832392529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42504093552985249221595019 63756140329477873832392529)
      ·
        refine ⟨47817105247108405374294397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63756140329477873832392529 47817105247108405374294397)
        ·
          refine ⟨17931414467665652015360399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47817105247108405374294397 17931414467665652015360399)
          ·
            refine ⟨26897121701498478023040599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17931414467665652015360399 26897121701498478023040599)
            ·
              refine ⟨40345682552247717034560899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26897121701498478023040599 40345682552247717034560899)
              ·
                refine ⟨60518523828371575551841349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40345682552247717034560899 60518523828371575551841349)
                ·
                  refine ⟨11347223217819670415970253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60518523828371575551841349 11347223217819670415970253)
                  ·
                    refine ⟨4255208706682376405988845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11347223217819670415970253 4255208706682376405988845)
                    ·
                      refine ⟨1595703265005891152245817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4255208706682376405988845 1595703265005891152245817)
                      ·
                        rfl

theorem cell23_3107621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_3107621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107621 prefixEnd_3107621 := by exact prefixLift 3107621
  have htrace : WordTrace (prefixWord ++ tailWord_3107621) baseStart_3107621 baseEnd_3107621 := by
    simpa [prefixWord, tailWord_3107621, baseEnd_3107621] using wordTrace_append hprefix tailTrace_3107621
  have hstable : (prefixWord ++ tailWord_3107621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107621).length < 2 ^ (prefixWord ++ tailWord_3107621).sum := by decide
  have hdescent : baseEnd_3107621 < baseStart_3107621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107681 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_3107681 : Nat := 118140960795 + 3107681 * 2 ^ 59
def prefixEnd_3107681 : Nat := 4983230072969 + 3 ^ 40 * 3107681 * 2
def baseEnd_3107681 : Nat := 1595734073845160917495541

theorem tailTrace_3107681 : CollatzResearch.WordTrace tailWord_3107681 prefixEnd_3107681 1595734073845160917495541 := by
  unfold tailWord_3107681
  simp only [CollatzResearch.WordTrace]
  refine ⟨113346437854409961504770897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75564291902939974336513931 113346437854409961504770897)
  ·
    refine ⟨85009828390807471128578173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113346437854409961504770897 85009828390807471128578173)
    ·
      refine ⟨31878685646552801673216815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85009828390807471128578173 31878685646552801673216815)
      ·
        refine ⟨47818028469829202509825223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31878685646552801673216815 47818028469829202509825223)
        ·
          refine ⟨71727042704743803764737835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47818028469829202509825223 71727042704743803764737835)
          ·
            refine ⟨107590564057115705647106753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71727042704743803764737835 107590564057115705647106753)
            ·
              refine ⟨80692923042836779235330065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107590564057115705647106753 80692923042836779235330065)
              ·
                refine ⟨60519692282127584426497549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80692923042836779235330065 60519692282127584426497549)
                ·
                  refine ⟨22694884605797844159936581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60519692282127584426497549 22694884605797844159936581)
                  ·
                    refine ⟨4255290863587095779988109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22694884605797844159936581 4255290863587095779988109)
                    ·
                      refine ⟨1595734073845160917495541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4255290863587095779988109 1595734073845160917495541)
                      ·
                        rfl

theorem cell23_3107681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_3107681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107681 prefixEnd_3107681 := by exact prefixLift 3107681
  have htrace : WordTrace (prefixWord ++ tailWord_3107681) baseStart_3107681 baseEnd_3107681 := by
    simpa [prefixWord, tailWord_3107681, baseEnd_3107681] using wordTrace_append hprefix tailTrace_3107681
  have hstable : (prefixWord ++ tailWord_3107681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107681).length < 2 ^ (prefixWord ++ tailWord_3107681).sum := by decide
  have hdescent : baseEnd_3107681 < baseStart_3107681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107711 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 3]
def baseStart_3107711 : Nat := 118140960795 + 3107711 * 2 ^ 59
def prefixEnd_3107711 : Nat := 4983230072969 + 3 ^ 40 * 3107711 * 2
def baseEnd_3107711 : Nat := 1595749478264795800120403

theorem tailTrace_3107711 : CollatzResearch.WordTrace tailWord_3107711 prefixEnd_3107711 1595749478264795800120403 := by
  unfold tailWord_3107711
  simp only [CollatzResearch.WordTrace]
  refine ⟨113347532044301276628362987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75565021362867517752241991 113347532044301276628362987)
  ·
    refine ⟨170021298066451914942544481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113347532044301276628362987 170021298066451914942544481)
    ·
      refine ⟨127515973549838936206908361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170021298066451914942544481 127515973549838936206908361)
      ·
        refine ⟨95636980162379202155181271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127515973549838936206908361 95636980162379202155181271)
        ·
          refine ⟨143455470243568803232771907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95636980162379202155181271 143455470243568803232771907)
          ·
            refine ⟨215183205365353204849157861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143455470243568803232771907 215183205365353204849157861)
            ·
              refine ⟨40346851006003725909217099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215183205365353204849157861 40346851006003725909217099)
              ·
                refine ⟨60520276509005588863825649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40346851006003725909217099 60520276509005588863825649)
                ·
                  refine ⟨45390207381754191647869237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60520276509005588863825649 45390207381754191647869237)
                  ·
                    refine ⟨4255331942039455466987741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45390207381754191647869237 4255331942039455466987741)
                    ·
                      refine ⟨1595749478264795800120403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4255331942039455466987741 1595749478264795800120403)
                      ·
                        rfl

theorem cell23_3107711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_3107711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107711 prefixEnd_3107711 := by exact prefixLift 3107711
  have htrace : WordTrace (prefixWord ++ tailWord_3107711) baseStart_3107711 baseEnd_3107711 := by
    simpa [prefixWord, tailWord_3107711, baseEnd_3107711] using wordTrace_append hprefix tailTrace_3107711
  have hstable : (prefixWord ++ tailWord_3107711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107711).length < 2 ^ (prefixWord ++ tailWord_3107711).sum := by decide
  have hdescent : baseEnd_3107711 < baseStart_3107711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107768 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_3107768 : Nat := 118140960795 + 3107768 * 2 ^ 59
def prefixEnd_3107768 : Nat := 4983230072969 + 3 ^ 40 * 3107768 * 2
def baseEnd_3107768 : Nat := 1595778746662102077107641

theorem tailTrace_3107768 : CollatzResearch.WordTrace tailWord_3107768 prefixEnd_3107768 1595778746662102077107641 := by
  unfold tailWord_3107768
  simp only [CollatzResearch.WordTrace]
  refine ⟨56674805502547387681593979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75566407336729850242125305 56674805502547387681593979)
  ·
    refine ⟨85012208253821081522390969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56674805502547387681593979 85012208253821081522390969)
    ·
      refine ⟨63759156190365811141793227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85012208253821081522390969 63759156190365811141793227)
      ·
        refine ⟨95638734285548716712689841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63759156190365811141793227 95638734285548716712689841)
        ·
          refine ⟨71729050714161537534517381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95638734285548716712689841 71729050714161537534517381)
          ·
            refine ⟨13449197008905288287722009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71729050714161537534517381 13449197008905288287722009)
            ·
              refine ⟨10086897756678966215791507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13449197008905288287722009 10086897756678966215791507)
              ·
                refine ⟨15130346635018449323687261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10086897756678966215791507 15130346635018449323687261)
                ·
                  refine ⟨5673879988131918496382723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15130346635018449323687261 5673879988131918496382723)
                  ·
                    refine ⟨8510819982197877744574085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5673879988131918496382723 8510819982197877744574085)
                    ·
                      refine ⟨1595778746662102077107641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8510819982197877744574085 1595778746662102077107641)
                      ·
                        rfl

theorem cell23_3107768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_3107768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107768 prefixEnd_3107768 := by exact prefixLift 3107768
  have htrace : WordTrace (prefixWord ++ tailWord_3107768) baseStart_3107768 baseEnd_3107768 := by
    simpa [prefixWord, tailWord_3107768, baseEnd_3107768] using wordTrace_append hprefix tailTrace_3107768
  have hstable : (prefixWord ++ tailWord_3107768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107768).length < 2 ^ (prefixWord ++ tailWord_3107768).sum := by decide
  have hdescent : baseEnd_3107768 < baseStart_3107768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107781 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_3107781 : Nat := 118140960795 + 3107781 * 2 ^ 59
def prefixEnd_3107781 : Nat := 4983230072969 + 3 ^ 40 * 3107781 * 2
def baseEnd_3107781 : Nat := 1595785421910610526245081

theorem tailTrace_3107781 : CollatzResearch.WordTrace tailWord_3107781 prefixEnd_3107781 1595785421910610526245081 := by
  unfold tailWord_3107781
  simp only [CollatzResearch.WordTrace]
  refine ⟨113350085154047678583411197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75566723436031785722274131 113350085154047678583411197)
  ·
    refine ⟨42506281932767879468779199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113350085154047678583411197 42506281932767879468779199)
    ·
      refine ⟨63759422899151819203168799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42506281932767879468779199 63759422899151819203168799)
      ·
        refine ⟨95639134348727728804753199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63759422899151819203168799 95639134348727728804753199)
        ·
          refine ⟨143458701523091593207129799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95639134348727728804753199 143458701523091593207129799)
          ·
            refine ⟨215188052284637389810694699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143458701523091593207129799 215188052284637389810694699)
            ·
              refine ⟨322782078426956084716042049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215188052284637389810694699 322782078426956084716042049)
              ·
                refine ⟨242086558820217063537031537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322782078426956084716042049 242086558820217063537031537)
                ·
                  refine ⟨181564919115162797652773653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242086558820217063537031537 181564919115162797652773653)
                  ·
                    refine ⟨8510855583523256139973765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181564919115162797652773653 8510855583523256139973765)
                    ·
                      refine ⟨1595785421910610526245081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8510855583523256139973765 1595785421910610526245081)
                      ·
                        rfl

theorem cell23_3107781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_3107781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107781 prefixEnd_3107781 := by exact prefixLift 3107781
  have htrace : WordTrace (prefixWord ++ tailWord_3107781) baseStart_3107781 baseEnd_3107781 := by
    simpa [prefixWord, tailWord_3107781, baseEnd_3107781] using wordTrace_append hprefix tailTrace_3107781
  have hstable : (prefixWord ++ tailWord_3107781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107781).length < 2 ^ (prefixWord ++ tailWord_3107781).sum := by decide
  have hdescent : baseEnd_3107781 < baseStart_3107781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107788 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3107788 : Nat := 118140960795 + 3107788 * 2 ^ 59
def prefixEnd_3107788 : Nat := 4983230072969 + 3 ^ 40 * 3107788 * 2
def baseEnd_3107788 : Nat := 1595789016275191998857549

theorem tailTrace_3107788 : CollatzResearch.WordTrace tailWord_3107788 prefixEnd_3107788 1595789016275191998857549 := by
  unfold tailWord_3107788
  simp only [CollatzResearch.WordTrace]
  refine ⟨56675170232511159389458009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75566893643348212519277345 56675170232511159389458009)
  ·
    refine ⟨42506377674383369542093507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56675170232511159389458009 42506377674383369542093507)
    ·
      refine ⟨63759566511575054313140261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42506377674383369542093507 63759566511575054313140261)
      ·
        refine ⟨11954918720920322683713799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63759566511575054313140261 11954918720920322683713799)
        ·
          refine ⟨17932378081380484025570699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11954918720920322683713799 17932378081380484025570699)
          ·
            refine ⟨26898567122070726038356049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17932378081380484025570699 26898567122070726038356049)
            ·
              refine ⟨20173925341553044528767037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26898567122070726038356049 20173925341553044528767037)
              ·
                refine ⟨7565222003082391698287639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20173925341553044528767037 7565222003082391698287639)
                ·
                  refine ⟨11347833004623587547431459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565222003082391698287639 11347833004623587547431459)
                  ·
                    refine ⟨17021749506935381321147189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11347833004623587547431459 17021749506935381321147189)
                    ·
                      refine ⟨1595789016275191998857549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17021749506935381321147189 1595789016275191998857549)
                      ·
                        rfl

theorem cell23_3107788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3107788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107788 prefixEnd_3107788 := by exact prefixLift 3107788
  have htrace : WordTrace (prefixWord ++ tailWord_3107788) baseStart_3107788 baseEnd_3107788 := by
    simpa [prefixWord, tailWord_3107788, baseEnd_3107788] using wordTrace_append hprefix tailTrace_3107788
  have hstable : (prefixWord ++ tailWord_3107788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107788).length < 2 ^ (prefixWord ++ tailWord_3107788).sum := by decide
  have hdescent : baseEnd_3107788 < baseStart_3107788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107791 : List Nat := [1, 1, 2, 1, 1, 7, 10]
def baseStart_3107791 : Nat := 118140960795 + 3107791 * 2 ^ 59
def prefixEnd_3107791 : Nat := 4983230072969 + 3 ^ 40 * 3107791 * 2
def baseEnd_3107791 : Nat := 19701117984162413421235

theorem tailTrace_3107791 : CollatzResearch.WordTrace tailWord_3107791 prefixEnd_3107791 19701117984162413421235 := by
  unfold tailWord_3107791
  simp only [CollatzResearch.WordTrace]
  refine ⟨113350449884011450291275227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75566966589340966860850151 113350449884011450291275227)
  ·
    refine ⟨170025674826017175436912841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113350449884011450291275227 170025674826017175436912841)
    ·
      refine ⟨127519256119512881577684631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170025674826017175436912841 127519256119512881577684631)
      ·
        refine ⟨191278884179269322366526947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127519256119512881577684631 191278884179269322366526947)
        ·
          refine ⟨286918326268903983549790421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191278884179269322366526947 286918326268903983549790421)
          ·
            refine ⟨6724648271927437114448213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 286918326268903983549790421 6724648271927437114448213)
            ·
              refine ⟨19701117984162413421235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6724648271927437114448213 19701117984162413421235)
              ·
                rfl

theorem cell23_3107791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 10].length) (baseStart_3107791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107791 prefixEnd_3107791 := by exact prefixLift 3107791
  have htrace : WordTrace (prefixWord ++ tailWord_3107791) baseStart_3107791 baseEnd_3107791 := by
    simpa [prefixWord, tailWord_3107791, baseEnd_3107791] using wordTrace_append hprefix tailTrace_3107791
  have hstable : (prefixWord ++ tailWord_3107791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107791).length < 2 ^ (prefixWord ++ tailWord_3107791).sum := by decide
  have hdescent : baseEnd_3107791 < baseStart_3107791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107802 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2]
def baseStart_3107802 : Nat := 118140960795 + 3107802 * 2 ^ 59
def prefixEnd_3107802 : Nat := 4983230072969 + 3 ^ 40 * 3107802 * 2
def baseEnd_3107802 : Nat := 1595796205004354944082485

theorem tailTrace_3107802 : CollatzResearch.WordTrace tailWord_3107802 prefixEnd_3107802 1595796205004354944082485 := by
  unfold tailWord_3107802
  simp only [CollatzResearch.WordTrace]
  refine ⟨28337712771742899792481415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75567234057981066113283773 28337712771742899792481415)
  ·
    refine ⟨42506569157614349688722123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28337712771742899792481415 42506569157614349688722123)
    ·
      refine ⟨63759853736421524533083185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42506569157614349688722123 63759853736421524533083185)
      ·
        refine ⟨47819890302316143399812389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63759853736421524533083185 47819890302316143399812389)
        ·
          refine ⟨8966229431684276887464823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47819890302316143399812389 8966229431684276887464823)
          ·
            refine ⟨13449344147526415331197235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8966229431684276887464823 13449344147526415331197235)
            ·
              refine ⟨20174016221289622996795853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13449344147526415331197235 20174016221289622996795853)
              ·
                refine ⟨7565256082983608623798445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20174016221289622996795853 7565256082983608623798445)
                ·
                  refine ⟨2836971031118853233924417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7565256082983608623798445 2836971031118853233924417)
                  ·
                    refine ⟨2127728273339139925443313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2836971031118853233924417 2127728273339139925443313)
                    ·
                      refine ⟨1595796205004354944082485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127728273339139925443313 1595796205004354944082485)
                      ·
                        rfl

theorem cell23_3107802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_3107802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107802 prefixEnd_3107802 := by exact prefixLift 3107802
  have htrace : WordTrace (prefixWord ++ tailWord_3107802) baseStart_3107802 baseEnd_3107802 := by
    simpa [prefixWord, tailWord_3107802, baseEnd_3107802] using wordTrace_append hprefix tailTrace_3107802
  have hstable : (prefixWord ++ tailWord_3107802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107802).length < 2 ^ (prefixWord ++ tailWord_3107802).sum := by decide
  have hdescent : baseEnd_3107802 < baseStart_3107802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107805 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3107805 : Nat := 118140960795 + 3107805 * 2 ^ 59
def prefixEnd_3107805 : Nat := 4983230072969 + 3 ^ 40 * 3107805 * 2
def baseEnd_3107805 : Nat := 1595797745446318432344971

theorem tailTrace_3107805 : CollatzResearch.WordTrace tailWord_3107805 prefixEnd_3107805 1595797745446318432344971 := by
  unfold tailWord_3107805
  simp only [CollatzResearch.WordTrace]
  refine ⟨113350960505960730682284869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75567307003973820454856579 113350960505960730682284869)
  ·
    refine ⟨21253305094867637002928413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113350960505960730682284869 21253305094867637002928413)
    ·
      refine ⟨7969989410575363876098155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21253305094867637002928413 7969989410575363876098155)
      ·
        refine ⟨11954984115863045814147233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7969989410575363876098155 11954984115863045814147233)
        ·
          refine ⟨8966238086897284360610425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11954984115863045814147233 8966238086897284360610425)
          ·
            refine ⟨6724678565172963270457819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8966238086897284360610425 6724678565172963270457819)
            ·
              refine ⟨10087017847759444905686729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6724678565172963270457819 10087017847759444905686729)
              ·
                refine ⟨7565263385819583679265047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10087017847759444905686729 7565263385819583679265047)
                ·
                  refine ⟨11347895078729375518897571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565263385819583679265047 11347895078729375518897571)
                  ·
                    refine ⟨17021842618094063278346357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11347895078729375518897571 17021842618094063278346357)
                    ·
                      refine ⟨1595797745446318432344971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17021842618094063278346357 1595797745446318432344971)
                      ·
                        rfl

theorem cell23_3107805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3107805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107805 prefixEnd_3107805 := by exact prefixLift 3107805
  have htrace : WordTrace (prefixWord ++ tailWord_3107805) baseStart_3107805 baseEnd_3107805 := by
    simpa [prefixWord, tailWord_3107805, baseEnd_3107805] using wordTrace_append hprefix tailTrace_3107805
  have hstable : (prefixWord ++ tailWord_3107805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107805).length < 2 ^ (prefixWord ++ tailWord_3107805).sum := by decide
  have hdescent : baseEnd_3107805 < baseStart_3107805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107815 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3107815 : Nat := 118140960795 + 3107815 * 2 ^ 59
def prefixEnd_3107815 : Nat := 4983230072969 + 3 ^ 40 * 3107815 * 2
def baseEnd_3107815 : Nat := 1595802880252863393219925

theorem tailTrace_3107815 : CollatzResearch.WordTrace tailWord_3107815 prefixEnd_3107815 1595802880252863393219925 := by
  unfold tailWord_3107815
  simp only [CollatzResearch.WordTrace]
  refine ⟨113351325235924502390148899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75567550157283001593432599 113351325235924502390148899)
  ·
    refine ⟨170026987853886753585223349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113351325235924502390148899 170026987853886753585223349)
    ·
      refine ⟨15940030111301883148614689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170026987853886753585223349 15940030111301883148614689)
      ·
        refine ⟨11955022583476412361461017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15940030111301883148614689 11955022583476412361461017)
        ·
          refine ⟨8966266937607309271095763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11955022583476412361461017 8966266937607309271095763)
          ·
            refine ⟨13449400406410963906643645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8966266937607309271095763 13449400406410963906643645)
            ·
              refine ⟨5043525152404111464991367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13449400406410963906643645 5043525152404111464991367)
              ·
                refine ⟨7565287728606167197487051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043525152404111464991367 7565287728606167197487051)
                ·
                  refine ⟨11347931592909250796230577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565287728606167197487051 11347931592909250796230577)
                  ·
                    refine ⟨8510948694681938097172933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11347931592909250796230577 8510948694681938097172933)
                    ·
                      refine ⟨1595802880252863393219925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8510948694681938097172933 1595802880252863393219925)
                      ·
                        rfl

theorem cell23_3107815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3107815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107815 prefixEnd_3107815 := by exact prefixLift 3107815
  have htrace : WordTrace (prefixWord ++ tailWord_3107815) baseStart_3107815 baseEnd_3107815 := by
    simpa [prefixWord, tailWord_3107815, baseEnd_3107815] using wordTrace_append hprefix tailTrace_3107815
  have hstable : (prefixWord ++ tailWord_3107815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107815).length < 2 ^ (prefixWord ++ tailWord_3107815).sum := by decide
  have hdescent : baseEnd_3107815 < baseStart_3107815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107825 : List Nat := [1, 2, 2, 2, 4, 3, 2, 7]
def baseStart_3107825 : Nat := 118140960795 + 3107825 * 2 ^ 59
def prefixEnd_3107825 : Nat := 4983230072969 + 3 ^ 40 * 3107825 * 2
def baseEnd_3107825 : Nat := 59104000557755864966477

theorem tailTrace_3107825 : CollatzResearch.WordTrace tailWord_3107825 prefixEnd_3107825 59104000557755864966477 := by
  unfold tailWord_3107825
  simp only [CollatzResearch.WordTrace]
  refine ⟨113351689965888274098012929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75567793310592182732008619 113351689965888274098012929)
  ·
    refine ⟨85013767474416205573509697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113351689965888274098012929 85013767474416205573509697)
    ·
      refine ⟨63760325605812154180132273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85013767474416205573509697 63760325605812154180132273)
      ·
        refine ⟨47820244204359115635099205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63760325605812154180132273 47820244204359115635099205)
        ·
          refine ⟨8966295788317334181581101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47820244204359115635099205 8966295788317334181581101)
          ·
            refine ⟨3362360920619000318092913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8966295788317334181581101 3362360920619000318092913)
            ·
              refine ⟨2521770690464250238569685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362360920619000318092913 2521770690464250238569685)
              ·
                refine ⟨59104000557755864966477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2521770690464250238569685 59104000557755864966477)
                ·
                  rfl

theorem cell23_3107825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 7].length) (baseStart_3107825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107825 prefixEnd_3107825 := by exact prefixLift 3107825
  have htrace : WordTrace (prefixWord ++ tailWord_3107825) baseStart_3107825 baseEnd_3107825 := by
    simpa [prefixWord, tailWord_3107825, baseEnd_3107825] using wordTrace_append hprefix tailTrace_3107825
  have hstable : (prefixWord ++ tailWord_3107825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107825).length < 2 ^ (prefixWord ++ tailWord_3107825).sum := by decide
  have hdescent : baseEnd_3107825 < baseStart_3107825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107836 : List Nat := [2, 2, 2, 1, 2, 5, 1, 3, 1, 2, 2]
def baseStart_3107836 : Nat := 118140960795 + 3107836 * 2 ^ 59
def prefixEnd_3107836 : Nat := 4983230072969 + 3 ^ 40 * 3107836 * 2
def baseEnd_3107836 : Nat := 1595813663346607811057329

theorem tailTrace_3107836 : CollatzResearch.WordTrace tailWord_3107836 prefixEnd_3107836 1595813663346607811057329 := by
  unfold tailWord_3107836
  simp only [CollatzResearch.WordTrace]
  refine ⟨56676045584424211488331681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75568060779232281984442241 56676045584424211488331681)
  ·
    refine ⟨42507034188318158616248761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56676045584424211488331681 42507034188318158616248761)
    ·
      refine ⟨31880275641238618962186571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42507034188318158616248761 31880275641238618962186571)
      ·
        refine ⟨47820413461857928443279857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31880275641238618962186571 47820413461857928443279857)
        ·
          refine ⟨35865310096393446332459893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47820413461857928443279857 35865310096393446332459893)
          ·
            refine ⟨3362372821536885593668115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35865310096393446332459893 3362372821536885593668115)
            ·
              refine ⟨5043559232305328390502173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362372821536885593668115 5043559232305328390502173)
              ·
                refine ⟨1891334712114498146438315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5043559232305328390502173 1891334712114498146438315)
                ·
                  refine ⟨2837002068171747219657473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891334712114498146438315 2837002068171747219657473)
                  ·
                    refine ⟨2127751551128810414743105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2837002068171747219657473 2127751551128810414743105)
                    ·
                      refine ⟨1595813663346607811057329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127751551128810414743105 1595813663346607811057329)
                      ·
                        rfl

theorem cell23_3107836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_3107836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107836 prefixEnd_3107836 := by exact prefixLift 3107836
  have htrace : WordTrace (prefixWord ++ tailWord_3107836) baseStart_3107836 baseEnd_3107836 := by
    simpa [prefixWord, tailWord_3107836, baseEnd_3107836] using wordTrace_append hprefix tailTrace_3107836
  have hstable : (prefixWord ++ tailWord_3107836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107836).length < 2 ^ (prefixWord ++ tailWord_3107836).sum := by decide
  have hdescent : baseEnd_3107836 < baseStart_3107836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107842 : List Nat := [3, 4, 1, 3, 1, 2, 9]
def baseStart_3107842 : Nat := 118140960795 + 3107842 * 2 ^ 59
def prefixEnd_3107842 : Nat := 4983230072969 + 3 ^ 40 * 3107842 * 2
def baseEnd_3107842 : Nat := 19701441286796725772621

theorem tailTrace_3107842 : CollatzResearch.WordTrace tailWord_3107842 prefixEnd_3107842 19701441286796725772621 := by
  unfold tailWord_3107842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28338077501706671500345445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75568206671217790667587853 28338077501706671500345445)
  ·
    refine ⟨5313389531570000906314771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28338077501706671500345445 5313389531570000906314771)
    ·
      refine ⟨7970084297355001359472157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5313389531570000906314771 7970084297355001359472157)
      ·
        refine ⟨2988781611508125509802059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7970084297355001359472157 2988781611508125509802059)
        ·
          refine ⟨4483172417262188264703089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988781611508125509802059 4483172417262188264703089)
          ·
            refine ⟨3362379312946641198527317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483172417262188264703089 3362379312946641198527317)
            ·
              refine ⟨19701441286796725772621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3362379312946641198527317 19701441286796725772621)
              ·
                rfl

theorem cell23_3107842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 9].length) (baseStart_3107842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107842 prefixEnd_3107842 := by exact prefixLift 3107842
  have htrace : WordTrace (prefixWord ++ tailWord_3107842) baseStart_3107842 baseEnd_3107842 := by
    simpa [prefixWord, tailWord_3107842, baseEnd_3107842] using wordTrace_append hprefix tailTrace_3107842
  have hstable : (prefixWord ++ tailWord_3107842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107842).length < 2 ^ (prefixWord ++ tailWord_3107842).sum := by decide
  have hdescent : baseEnd_3107842 < baseStart_3107842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107869 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3107869 : Nat := 118140960795 + 3107869 * 2 ^ 59
def prefixEnd_3107869 : Nat := 4983230072969 + 3 ^ 40 * 3107869 * 2
def baseEnd_3107869 : Nat := 1595830608208206181944677

theorem tailTrace_3107869 : CollatzResearch.WordTrace tailWord_3107869 prefixEnd_3107869 1595830608208206181944677 := by
  unfold tailWord_3107869
  simp only [CollatzResearch.WordTrace]
  refine ⟨113353294777728869612614661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75568863185152579741743107 113353294777728869612614661)
  ·
    refine ⟨21253742770824163052365249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113353294777728869612614661 21253742770824163052365249)
    ·
      refine ⟨15940307078118122289273937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21253742770824163052365249 15940307078118122289273937)
      ·
        refine ⟨11955230308588591716955453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15940307078118122289273937 11955230308588591716955453)
        ·
          refine ⟨4483211365720721893858295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11955230308588591716955453 4483211365720721893858295)
          ·
            refine ⟨6724817048581082840787443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483211365720721893858295 6724817048581082840787443)
            ·
              refine ⟨10087225572871624261181165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6724817048581082840787443 10087225572871624261181165)
              ·
                refine ⟨3782709589826859097942937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10087225572871624261181165 3782709589826859097942937)
                ·
                  refine ⟨2837032192370144323457203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3782709589826859097942937 2837032192370144323457203)
                  ·
                    refine ⟨4255548288555216485185805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2837032192370144323457203 4255548288555216485185805)
                    ·
                      refine ⟨1595830608208206181944677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4255548288555216485185805 1595830608208206181944677)
                      ·
                        rfl

theorem cell23_3107869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3107869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107869 prefixEnd_3107869 := by exact prefixLift 3107869
  have htrace : WordTrace (prefixWord ++ tailWord_3107869) baseStart_3107869 baseEnd_3107869 := by
    simpa [prefixWord, tailWord_3107869, baseEnd_3107869] using wordTrace_append hprefix tailTrace_3107869
  have hstable : (prefixWord ++ tailWord_3107869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107869).length < 2 ^ (prefixWord ++ tailWord_3107869).sum := by decide
  have hdescent : baseEnd_3107869 < baseStart_3107869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107879 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_3107879 : Nat := 118140960795 + 3107879 * 2 ^ 59
def prefixEnd_3107879 : Nat := 4983230072969 + 3 ^ 40 * 3107879 * 2
def baseEnd_3107879 : Nat := 1595835743014751142819631

theorem tailTrace_3107879 : CollatzResearch.WordTrace tailWord_3107879 prefixEnd_3107879 1595835743014751142819631 := by
  unfold tailWord_3107879
  simp only [CollatzResearch.WordTrace]
  refine ⟨113353659507692641320478691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75569106338461760880319127 113353659507692641320478691)
  ·
    refine ⟨170030489261538961980718037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113353659507692641320478691 170030489261538961980718037)
    ·
      refine ⟨3985089592067319421423079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 170030489261538961980718037 3985089592067319421423079)
      ·
        refine ⟨5977634388100979132134619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3985089592067319421423079 5977634388100979132134619)
        ·
          refine ⟨8966451582151468698201929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5977634388100979132134619 8966451582151468698201929)
          ·
            refine ⟨6724838686613601523651447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8966451582151468698201929 6724838686613601523651447)
            ·
              refine ⟨10087258029920402285477171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6724838686613601523651447 10087258029920402285477171)
              ·
                refine ⟨15130887044880603428215757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10087258029920402285477171 15130887044880603428215757)
                ·
                  refine ⟨5674082641830226285580909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15130887044880603428215757 5674082641830226285580909)
                  ·
                    refine ⟨2127780990686334857092841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5674082641830226285580909 2127780990686334857092841)
                    ·
                      refine ⟨1595835743014751142819631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127780990686334857092841 1595835743014751142819631)
                      ·
                        rfl

theorem cell23_3107879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_3107879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107879 prefixEnd_3107879 := by exact prefixLift 3107879
  have htrace : WordTrace (prefixWord ++ tailWord_3107879) baseStart_3107879 baseEnd_3107879 := by
    simpa [prefixWord, tailWord_3107879, baseEnd_3107879] using wordTrace_append hprefix tailTrace_3107879
  have hstable : (prefixWord ++ tailWord_3107879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107879).length < 2 ^ (prefixWord ++ tailWord_3107879).sum := by decide
  have hdescent : baseEnd_3107879 < baseStart_3107879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107925 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_3107925 : Nat := 118140960795 + 3107925 * 2 ^ 59
def prefixEnd_3107925 : Nat := 4983230072969 + 3 ^ 40 * 3107925 * 2
def baseEnd_3107925 : Nat := 1595859363124857962844419

theorem tailTrace_3107925 : CollatzResearch.WordTrace tailWord_3107925 prefixEnd_3107925 1595859363124857962844419 := by
  unfold tailWord_3107925
  simp only [CollatzResearch.WordTrace]
  refine ⟨113355337265525991176653229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75570224843683994117768819 113355337265525991176653229)
  ·
    refine ⟨42508251474572246691244961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113355337265525991176653229 42508251474572246691244961)
    ·
      refine ⟨31881188605929185018433721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42508251474572246691244961 31881188605929185018433721)
      ·
        refine ⟨23910891454446888763825291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31881188605929185018433721 23910891454446888763825291)
        ·
          refine ⟨35866337181670333145737937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23910891454446888763825291 35866337181670333145737937)
          ·
            refine ⟨26899752886252749859303453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35866337181670333145737937 26899752886252749859303453)
            ·
              refine ⟨10087407332344781197238795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26899752886252749859303453 10087407332344781197238795)
              ·
                refine ⟨15131110998517171795858193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10087407332344781197238795 15131110998517171795858193)
                ·
                  refine ⟨11348333248887878846893645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15131110998517171795858193 11348333248887878846893645)
                  ·
                    refine ⟨4255624968332954567585117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11348333248887878846893645 4255624968332954567585117)
                    ·
                      refine ⟨1595859363124857962844419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4255624968332954567585117 1595859363124857962844419)
                      ·
                        rfl

theorem cell23_3107925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_3107925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107925 prefixEnd_3107925 := by exact prefixLift 3107925
  have htrace : WordTrace (prefixWord ++ tailWord_3107925) baseStart_3107925 baseEnd_3107925 := by
    simpa [prefixWord, tailWord_3107925, baseEnd_3107925] using wordTrace_append hprefix tailTrace_3107925
  have hstable : (prefixWord ++ tailWord_3107925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107925).length < 2 ^ (prefixWord ++ tailWord_3107925).sum := by decide
  have hdescent : baseEnd_3107925 < baseStart_3107925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107928 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 1, 7]
def baseStart_3107928 : Nat := 118140960795 + 3107928 * 2 ^ 59
def prefixEnd_3107928 : Nat := 4983230072969 + 3 ^ 40 * 3107928 * 2
def baseEnd_3107928 : Nat := 531953634522273817035635

theorem tailTrace_3107928 : CollatzResearch.WordTrace tailWord_3107928 prefixEnd_3107928 531953634522273817035635 := by
  unfold tailWord_3107928
  simp only [CollatzResearch.WordTrace]
  refine ⟨56677723342257561344506219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75570297789676748459341625 56677723342257561344506219)
  ·
    refine ⟨85016585013386342016759329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56677723342257561344506219 85016585013386342016759329)
    ·
      refine ⟨63762438760039756512569497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85016585013386342016759329 63762438760039756512569497)
      ·
        refine ⟨47821829070029817384427123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63762438760039756512569497 47821829070029817384427123)
        ·
          refine ⟨71732743605044726076640685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47821829070029817384427123 71732743605044726076640685)
          ·
            refine ⟨26899778851891772278740257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71732743605044726076640685 26899778851891772278740257)
            ·
              refine ⟨20174834138918829209055193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26899778851891772278740257 20174834138918829209055193)
              ·
                refine ⟨15131125604189121906791395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20174834138918829209055193 15131125604189121906791395)
                ·
                  refine ⟨22696688406283682860187093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15131125604189121906791395 22696688406283682860187093)
                  ·
                    refine ⟨531953634522273817035635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22696688406283682860187093 531953634522273817035635)
                    ·
                      rfl

theorem cell23_3107928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_3107928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107928 prefixEnd_3107928 := by exact prefixLift 3107928
  have htrace : WordTrace (prefixWord ++ tailWord_3107928) baseStart_3107928 baseEnd_3107928 := by
    simpa [prefixWord, tailWord_3107928, baseEnd_3107928] using wordTrace_append hprefix tailTrace_3107928
  have hstable : (prefixWord ++ tailWord_3107928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107928).length < 2 ^ (prefixWord ++ tailWord_3107928).sum := by decide
  have hdescent : baseEnd_3107928 < baseStart_3107928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107935 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 2, 5, 2]
def baseStart_3107935 : Nat := 118140960795 + 3107935 * 2 ^ 59
def prefixEnd_3107935 : Nat := 4983230072969 + 3 ^ 40 * 3107935 * 2
def baseEnd_3107935 : Nat := 1595864497931402923719373

theorem tailTrace_3107935 : CollatzResearch.WordTrace tailWord_3107935 prefixEnd_3107935 1595864497931402923719373 := by
  unfold tailWord_3107935
  simp only [CollatzResearch.WordTrace]
  refine ⟨113355701995489762884517259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75570467996993175256344839 113355701995489762884517259)
  ·
    refine ⟨170033552993234644326775889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113355701995489762884517259 170033552993234644326775889)
    ·
      refine ⟨127525164744925983245081917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170033552993234644326775889 127525164744925983245081917)
      ·
        refine ⟨47821936779347243716905719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127525164744925983245081917 47821936779347243716905719)
        ·
          refine ⟨71732905169020865575358579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47821936779347243716905719 71732905169020865575358579)
          ·
            refine ⟨107599357753531298363037869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71732905169020865575358579 107599357753531298363037869)
            ·
              refine ⟨40349759157574236886139201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107599357753531298363037869 40349759157574236886139201)
              ·
                refine ⟨30262319368180677664604401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40349759157574236886139201 30262319368180677664604401)
                ·
                  refine ⟨22696739526135508248453301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30262319368180677664604401 22696739526135508248453301)
                  ·
                    refine ⟨2127819330575203898292497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22696739526135508248453301 2127819330575203898292497)
                    ·
                      refine ⟨1595864497931402923719373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127819330575203898292497 1595864497931402923719373)
                      ·
                        rfl

theorem cell23_3107935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_3107935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107935 prefixEnd_3107935 := by exact prefixLift 3107935
  have htrace : WordTrace (prefixWord ++ tailWord_3107935) baseStart_3107935 baseEnd_3107935 := by
    simpa [prefixWord, tailWord_3107935, baseEnd_3107935] using wordTrace_append hprefix tailTrace_3107935
  have hstable : (prefixWord ++ tailWord_3107935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107935).length < 2 ^ (prefixWord ++ tailWord_3107935).sum := by decide
  have hdescent : baseEnd_3107935 < baseStart_3107935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107945 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 2, 5]
def baseStart_3107945 : Nat := 118140960795 + 3107945 * 2 ^ 59
def prefixEnd_3107945 : Nat := 4983230072969 + 3 ^ 40 * 3107945 * 2
def baseEnd_3107945 : Nat := 531956544245982628198109

theorem tailTrace_3107945 : CollatzResearch.WordTrace tailWord_3107945 prefixEnd_3107945 531956544245982628198109 := by
  unfold tailWord_3107945
  simp only [CollatzResearch.WordTrace]
  refine ⟨113356066725453534592381289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75570711150302356394920859 113356066725453534592381289)
  ·
    refine ⟨85017050044090150944285967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113356066725453534592381289 85017050044090150944285967)
    ·
      refine ⟨127525575066135226416428951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85017050044090150944285967 127525575066135226416428951)
      ·
        refine ⟨191288362599202839624643427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127525575066135226416428951 191288362599202839624643427)
        ·
          refine ⟨286932543898804259436965141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191288362599202839624643427 286932543898804259436965141)
          ·
            refine ⟨13449962995256449661107741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 286932543898804259436965141 13449962995256449661107741)
            ·
              refine ⟨5043736123221168622915403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13449962995256449661107741 5043736123221168622915403)
              ·
                refine ⟨7565604184831752934373105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043736123221168622915403 7565604184831752934373105)
                ·
                  refine ⟨5674203138623814700779829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7565604184831752934373105 5674203138623814700779829)
                  ·
                    refine ⟨531956544245982628198109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5674203138623814700779829 531956544245982628198109)
                    ·
                      rfl

theorem cell23_3107945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_3107945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107945 prefixEnd_3107945 := by exact prefixLift 3107945
  have htrace : WordTrace (prefixWord ++ tailWord_3107945) baseStart_3107945 baseEnd_3107945 := by
    simpa [prefixWord, tailWord_3107945, baseEnd_3107945] using wordTrace_append hprefix tailTrace_3107945
  have hstable : (prefixWord ++ tailWord_3107945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107945).length < 2 ^ (prefixWord ++ tailWord_3107945).sum := by decide
  have hdescent : baseEnd_3107945 < baseStart_3107945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107965 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_3107965 : Nat := 118140960795 + 3107965 * 2 ^ 59
def prefixEnd_3107965 : Nat := 4983230072969 + 3 ^ 40 * 3107965 * 2
def baseEnd_3107965 : Nat := 1595879902351037806344235

theorem tailTrace_3107965 : CollatzResearch.WordTrace tailWord_3107965 prefixEnd_3107965 1595879902351037806344235 := by
  unfold tailWord_3107965
  simp only [CollatzResearch.WordTrace]
  refine ⟨113356796185381078008109349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75571197456920718672072899 113356796185381078008109349)
  ·
    refine ⟨21254399284758952126520503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113356796185381078008109349 21254399284758952126520503)
    ·
      refine ⟨31881598927138428189780755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21254399284758952126520503 31881598927138428189780755)
      ·
        refine ⟨47822398390707642284671133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31881598927138428189780755 47822398390707642284671133)
        ·
          refine ⟨17933399396515365856751675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47822398390707642284671133 17933399396515365856751675)
          ·
            refine ⟨26900099094773048785127513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17933399396515365856751675 26900099094773048785127513)
            ·
              refine ⟨20175074321079786588845635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26900099094773048785127513 20175074321079786588845635)
              ·
                refine ⟨30262611481619679883268453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20175074321079786588845635 30262611481619679883268453)
                ·
                  refine ⟨5674239652803689978112835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30262611481619679883268453 5674239652803689978112835)
                  ·
                    refine ⟨8511359479205534967169253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5674239652803689978112835 8511359479205534967169253)
                    ·
                      refine ⟨1595879902351037806344235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8511359479205534967169253 1595879902351037806344235)
                      ·
                        rfl

theorem cell23_3107965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_3107965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107965 prefixEnd_3107965 := by exact prefixLift 3107965
  have htrace : WordTrace (prefixWord ++ tailWord_3107965) baseStart_3107965 baseEnd_3107965 := by
    simpa [prefixWord, tailWord_3107965, baseEnd_3107965] using wordTrace_append hprefix tailTrace_3107965
  have hstable : (prefixWord ++ tailWord_3107965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107965).length < 2 ^ (prefixWord ++ tailWord_3107965).sum := by decide
  have hdescent : baseEnd_3107965 < baseStart_3107965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107966 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_3107966 : Nat := 118140960795 + 3107966 * 2 ^ 59
def prefixEnd_3107966 : Nat := 4983230072969 + 3 ^ 40 * 3107966 * 2
def baseEnd_3107966 : Nat := 177320046203521366936859

theorem tailTrace_3107966 : CollatzResearch.WordTrace tailWord_3107966 prefixEnd_3107966 177320046203521366936859 := by
  unfold tailWord_3107966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169604082297181897361969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75571221772251636785930501 14169604082297181897361969)
  ·
    refine ⟨10627203061722886423021477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14169604082297181897361969 10627203061722886423021477)
    ·
      refine ⟨1992600574073041204316527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10627203061722886423021477 1992600574073041204316527)
      ·
        refine ⟨2988900861109561806474791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992600574073041204316527 2988900861109561806474791)
        ·
          refine ⟨4483351291664342709712187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988900861109561806474791 4483351291664342709712187)
          ·
            refine ⟨6725026937496514064568281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483351291664342709712187 6725026937496514064568281)
            ·
              refine ⟨5043770203122385548426211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6725026937496514064568281 5043770203122385548426211)
              ·
                refine ⟨7565655304683578322639317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043770203122385548426211 7565655304683578322639317)
                ·
                  refine ⟨177320046203521366936859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7565655304683578322639317 177320046203521366936859)
                  ·
                    rfl

theorem cell23_3107966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_3107966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107966 prefixEnd_3107966 := by exact prefixLift 3107966
  have htrace : WordTrace (prefixWord ++ tailWord_3107966) baseStart_3107966 baseEnd_3107966 := by
    simpa [prefixWord, tailWord_3107966, baseEnd_3107966] using wordTrace_append hprefix tailTrace_3107966
  have hstable : (prefixWord ++ tailWord_3107966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107966).length < 2 ^ (prefixWord ++ tailWord_3107966).sum := by decide
  have hdescent : baseEnd_3107966 < baseStart_3107966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107968 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_3107968 : Nat := 118140960795 + 3107968 * 2 ^ 59
def prefixEnd_3107968 : Nat := 4983230072969 + 3 ^ 40 * 3107968 * 2
def baseEnd_3107968 : Nat := 1595881442793001294606721

theorem tailTrace_3107968 : CollatzResearch.WordTrace tailWord_3107968 prefixEnd_3107968 1595881442793001294606721 := by
  unfold tailWord_3107968
  simp only [CollatzResearch.WordTrace]
  refine ⟨56678452802185104760234279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75571270402913473013645705 56678452802185104760234279)
  ·
    refine ⟨85017679203277657140351419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56678452802185104760234279 85017679203277657140351419)
    ·
      refine ⟨127526518804916485710527129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85017679203277657140351419 127526518804916485710527129)
      ·
        refine ⟨95644889103687364282895347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127526518804916485710527129 95644889103687364282895347)
        ·
          refine ⟨143467333655531046424343021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95644889103687364282895347 143467333655531046424343021)
          ·
            refine ⟨53800250120824142409128633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143467333655531046424343021 53800250120824142409128633)
            ·
              refine ⟨40350187590618106806846475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53800250120824142409128633 40350187590618106806846475)
              ·
                refine ⟨60525281385927160210269713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40350187590618106806846475 60525281385927160210269713)
                ·
                  refine ⟨45393961039445370157702285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60525281385927160210269713 45393961039445370157702285)
                  ·
                    refine ⟨17022735389792013809138357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45393961039445370157702285 17022735389792013809138357)
                    ·
                      refine ⟨1595881442793001294606721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17022735389792013809138357 1595881442793001294606721)
                      ·
                        rfl

theorem cell23_3107968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_3107968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107968 prefixEnd_3107968 := by exact prefixLift 3107968
  have htrace : WordTrace (prefixWord ++ tailWord_3107968) baseStart_3107968 baseEnd_3107968 := by
    simpa [prefixWord, tailWord_3107968, baseEnd_3107968] using wordTrace_append hprefix tailTrace_3107968
  have hstable : (prefixWord ++ tailWord_3107968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107968).length < 2 ^ (prefixWord ++ tailWord_3107968).sum := by decide
  have hdescent : baseEnd_3107968 < baseStart_3107968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107992 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 3, 4]
def baseStart_3107992 : Nat := 118140960795 + 3107992 * 2 ^ 59
def prefixEnd_3107992 : Nat := 4983230072969 + 3 ^ 40 * 3107992 * 2
def baseEnd_3107992 : Nat := 531964588776236400235537

theorem tailTrace_3107992 : CollatzResearch.WordTrace tailWord_3107992 prefixEnd_3107992 531964588776236400235537 := by
  unfold tailWord_3107992
  simp only [CollatzResearch.WordTrace]
  refine ⟨56678890478141630809671115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75571853970855507746228153 56678890478141630809671115)
  ·
    refine ⟨85018335717212446214506673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56678890478141630809671115 85018335717212446214506673)
    ·
      refine ⟨63763751787909334660880005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85018335717212446214506673 63763751787909334660880005)
      ·
        refine ⟨11955703460233000248915001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63763751787909334660880005 11955703460233000248915001)
        ·
          refine ⟨8966777595174750186686251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11955703460233000248915001 8966777595174750186686251)
          ·
            refine ⟨13450166392762125280029377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8966777595174750186686251 13450166392762125280029377)
            ·
              refine ⟨10087624794571593960022033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13450166392762125280029377 10087624794571593960022033)
              ·
                refine ⟨7565718595928695470016525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10087624794571593960022033 7565718595928695470016525)
                ·
                  refine ⟨2837144473473260801256197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7565718595928695470016525 2837144473473260801256197)
                  ·
                    refine ⟨531964588776236400235537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2837144473473260801256197 531964588776236400235537)
                    ·
                      rfl

theorem cell23_3107992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_3107992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3107992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3107992 prefixEnd_3107992 := by exact prefixLift 3107992
  have htrace : WordTrace (prefixWord ++ tailWord_3107992) baseStart_3107992 baseEnd_3107992 := by
    simpa [prefixWord, tailWord_3107992, baseEnd_3107992] using wordTrace_append hprefix tailTrace_3107992
  have hstable : (prefixWord ++ tailWord_3107992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107992).length < 2 ^ (prefixWord ++ tailWord_3107992).sum := by decide
  have hdescent : baseEnd_3107992 < baseStart_3107992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108065 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 3, 6]
def baseStart_3108065 : Nat := 118140960795 + 3108065 * 2 ^ 59
def prefixEnd_3108065 : Nat := 4983230072969 + 3 ^ 40 * 3108065 * 2
def baseEnd_3108065 : Nat := 531977083472162471697925

theorem tailTrace_3108065 : CollatzResearch.WordTrace tailWord_3108065 prefixEnd_3108065 531977083472162471697925 := by
  unfold tailWord_3108065
  simp only [CollatzResearch.WordTrace]
  refine ⟨113360443485018795086749649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75573628990012530057833099 113360443485018795086749649)
  ·
    refine ⟨85020332613764096315062237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113360443485018795086749649 85020332613764096315062237)
    ·
      refine ⟨31882624730161536118148339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85020332613764096315062237 31882624730161536118148339)
      ·
        refine ⟨47823937095242304177222509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31882624730161536118148339 47823937095242304177222509)
        ·
          refine ⟨17933976410715864066458441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47823937095242304177222509 17933976410715864066458441)
          ·
            refine ⟨13450482308036898049843831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17933976410715864066458441 13450482308036898049843831)
            ·
              refine ⟨20175723462055347074765747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13450482308036898049843831 20175723462055347074765747)
              ·
                refine ⟨30263585193083020612148621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20175723462055347074765747 30263585193083020612148621)
                ·
                  refine ⟨11348844447406132729555733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30263585193083020612148621 11348844447406132729555733)
                  ·
                    refine ⟨531977083472162471697925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11348844447406132729555733 531977083472162471697925)
                    ·
                      rfl

theorem cell23_3108065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_3108065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108065 prefixEnd_3108065 := by exact prefixLift 3108065
  have htrace : WordTrace (prefixWord ++ tailWord_3108065) baseStart_3108065 baseEnd_3108065 := by
    simpa [prefixWord, tailWord_3108065, baseEnd_3108065] using wordTrace_append hprefix tailTrace_3108065
  have hstable : (prefixWord ++ tailWord_3108065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108065).length < 2 ^ (prefixWord ++ tailWord_3108065).sum := by decide
  have hdescent : baseEnd_3108065 < baseStart_3108065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108083 : List Nat := [1, 1, 1, 2, 2, 7, 2, 2, 1, 1, 3]
def baseStart_3108083 : Nat := 118140960795 + 3108083 * 2 ^ 59
def prefixEnd_3108083 : Nat := 4983230072969 + 3 ^ 40 * 3108083 * 2
def baseEnd_3108083 : Nat := 1595940493068268344668693

theorem tailTrace_3108083 : CollatzResearch.WordTrace tailWord_3108083 prefixEnd_3108083 1595940493068268344668693 := by
  unfold tailWord_3108083
  simp only [CollatzResearch.WordTrace]
  refine ⟨113361099998953584160904903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75574066665969056107269935 113361099998953584160904903)
  ·
    refine ⟨170041649998430376241357355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113361099998953584160904903 170041649998430376241357355)
    ·
      refine ⟨255062474997645564362036033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170041649998430376241357355 255062474997645564362036033)
      ·
        refine ⟨191296856248234173271527025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255062474997645564362036033 191296856248234173271527025)
        ·
          refine ⟨143472642186175629953645269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191296856248234173271527025 143472642186175629953645269)
          ·
            refine ⟨3362640051238491327038561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 143472642186175629953645269 3362640051238491327038561)
            ·
              refine ⟨2521980038428868495278921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362640051238491327038561 2521980038428868495278921)
              ·
                refine ⟨1891485028821651371459191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521980038428868495278921 1891485028821651371459191)
                ·
                  refine ⟨2837227543232477057188787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891485028821651371459191 2837227543232477057188787)
                  ·
                    refine ⟨4255841314848715585783181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2837227543232477057188787 4255841314848715585783181)
                    ·
                      refine ⟨1595940493068268344668693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4255841314848715585783181 1595940493068268344668693)
                      ·
                        rfl

theorem cell23_3108083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 1, 3].length) (baseStart_3108083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108083 prefixEnd_3108083 := by exact prefixLift 3108083
  have htrace : WordTrace (prefixWord ++ tailWord_3108083) baseStart_3108083 baseEnd_3108083 := by
    simpa [prefixWord, tailWord_3108083, baseEnd_3108083] using wordTrace_append hprefix tailTrace_3108083
  have hstable : (prefixWord ++ tailWord_3108083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108083).length < 2 ^ (prefixWord ++ tailWord_3108083).sum := by decide
  have hdescent : baseEnd_3108083 < baseStart_3108083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108089 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 3, 2, 2]
def baseStart_3108089 : Nat := 118140960795 + 3108089 * 2 ^ 59
def prefixEnd_3108089 : Nat := 4983230072969 + 3 ^ 40 * 3108089 * 2
def baseEnd_3108089 : Nat := 1595943573952195321193665

theorem tailTrace_3108089 : CollatzResearch.WordTrace tailWord_3108089 prefixEnd_3108089 1595943573952195321193665 := by
  unfold tailWord_3108089
  simp only [CollatzResearch.WordTrace]
  refine ⟨113361318836931847185623321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75574212557954564790415547 113361318836931847185623321)
  ·
    refine ⟨85020989127698885389217491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113361318836931847185623321 85020989127698885389217491)
    ·
      refine ⟨127531483691548328083826237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85020989127698885389217491 127531483691548328083826237)
      ·
        refine ⟨47824306384330623031434839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127531483691548328083826237 47824306384330623031434839)
        ·
          refine ⟨71736459576495934547152259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47824306384330623031434839 71736459576495934547152259)
          ·
            refine ⟨107604689364743901820728389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71736459576495934547152259 107604689364743901820728389)
            ·
              refine ⟨20175879255889481591386573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107604689364743901820728389 20175879255889481591386573)
              ·
                refine ⟨7565954720958555596769965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20175879255889481591386573 7565954720958555596769965)
                ·
                  refine ⟨2837233020359458348788737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7565954720958555596769965 2837233020359458348788737)
                  ·
                    refine ⟨2127924765269593761591553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2837233020359458348788737 2127924765269593761591553)
                    ·
                      refine ⟨1595943573952195321193665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127924765269593761591553 1595943573952195321193665)
                      ·
                        rfl

theorem cell23_3108089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_3108089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108089 prefixEnd_3108089 := by exact prefixLift 3108089
  have htrace : WordTrace (prefixWord ++ tailWord_3108089) baseStart_3108089 baseEnd_3108089 := by
    simpa [prefixWord, tailWord_3108089, baseEnd_3108089] using wordTrace_append hprefix tailTrace_3108089
  have hstable : (prefixWord ++ tailWord_3108089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108089).length < 2 ^ (prefixWord ++ tailWord_3108089).sum := by decide
  have hdescent : baseEnd_3108089 < baseStart_3108089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108095 : List Nat := [1, 1, 2, 2, 1, 5, 3, 8]
def baseStart_3108095 : Nat := 118140960795 + 3108095 * 2 ^ 59
def prefixEnd_3108095 : Nat := 4983230072969 + 3 ^ 40 * 3108095 * 2
def baseEnd_3108095 : Nat := 59109135364300825841431

theorem tailTrace_3108095 : CollatzResearch.WordTrace tailWord_3108095 prefixEnd_3108095 59109135364300825841431 := by
  unfold tailWord_3108095
  simp only [CollatzResearch.WordTrace]
  refine ⟨113361537674910110210341739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75574358449940073473561159 113361537674910110210341739)
  ·
    refine ⟨170042306512365165315512609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113361537674910110210341739 170042306512365165315512609)
    ·
      refine ⟨127531729884273873986634457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170042306512365165315512609 127531729884273873986634457)
      ·
        refine ⟨95648797413205405489975843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127531729884273873986634457 95648797413205405489975843)
        ·
          refine ⟨143473196119808108234963765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95648797413205405489975843 143473196119808108234963765)
          ·
            refine ⟨13450612136232010147027853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143473196119808108234963765 13450612136232010147027853)
            ·
              refine ⟨5043979551087003805135445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13450612136232010147027853 5043979551087003805135445)
              ·
                refine ⟨59109135364300825841431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5043979551087003805135445 59109135364300825841431)
                ·
                  rfl

theorem cell23_3108095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 8].length) (baseStart_3108095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108095 prefixEnd_3108095 := by exact prefixLift 3108095
  have htrace : WordTrace (prefixWord ++ tailWord_3108095) baseStart_3108095 baseEnd_3108095 := by
    simpa [prefixWord, tailWord_3108095, baseEnd_3108095] using wordTrace_append hprefix tailTrace_3108095
  have hstable : (prefixWord ++ tailWord_3108095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108095).length < 2 ^ (prefixWord ++ tailWord_3108095).sum := by decide
  have hdescent : baseEnd_3108095 < baseStart_3108095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108150 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_3108150 : Nat := 118140960795 + 3108150 * 2 ^ 59
def prefixEnd_3108150 : Nat := 4983230072969 + 3 ^ 40 * 3108150 * 2
def baseEnd_3108150 : Nat := 531991632090706527510295

theorem tailTrace_3108150 : CollatzResearch.WordTrace tailWord_3108150 prefixEnd_3108150 531991632090706527510295 := by
  unfold tailWord_3108150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7085221480606928412724619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75575695793140569735729269 7085221480606928412724619)
  ·
    refine ⟨10627832220910392619086929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7085221480606928412724619 10627832220910392619086929)
    ·
      refine ⟨7970874165682794464315197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10627832220910392619086929 7970874165682794464315197)
      ·
        refine ⟨2989077812131047924118199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7970874165682794464315197 2989077812131047924118199)
        ·
          refine ⟨4483616718196571886177299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989077812131047924118199 4483616718196571886177299)
          ·
            refine ⟨6725425077294857829265949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483616718196571886177299 6725425077294857829265949)
            ·
              refine ⟨2522034403985571685974731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6725425077294857829265949 2522034403985571685974731)
              ·
                refine ⟨3783051605978357528962097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2522034403985571685974731 3783051605978357528962097)
                ·
                  refine ⟨2837288704483768146721573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3783051605978357528962097 2837288704483768146721573)
                  ·
                    refine ⟨531991632090706527510295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2837288704483768146721573 531991632090706527510295)
                    ·
                      rfl

theorem cell23_3108150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_3108150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108150 prefixEnd_3108150 := by exact prefixLift 3108150
  have htrace : WordTrace (prefixWord ++ tailWord_3108150) baseStart_3108150 baseEnd_3108150 := by
    simpa [prefixWord, tailWord_3108150, baseEnd_3108150] using wordTrace_append hprefix tailTrace_3108150
  have hstable : (prefixWord ++ tailWord_3108150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108150).length < 2 ^ (prefixWord ++ tailWord_3108150).sum := by decide
  have hdescent : baseEnd_3108150 < baseStart_3108150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108165 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_3108165 : Nat := 118140960795 + 3108165 * 2 ^ 59
def prefixEnd_3108165 : Nat := 4983230072969 + 3 ^ 40 * 3108165 * 2
def baseEnd_3108165 : Nat := 1595982598481937023843315

theorem tailTrace_3108165 : CollatzResearch.WordTrace tailWord_3108165 prefixEnd_3108165 1595982598481937023843315 := by
  unfold tailWord_3108165
  simp only [CollatzResearch.WordTrace]
  refine ⟨113364090784656512165389949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75576060523104341443593299 113364090784656512165389949)
  ·
    refine ⟨42511534044246192062021231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113364090784656512165389949 42511534044246192062021231)
    ·
      refine ⟨63767301066369288093031847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42511534044246192062021231 63767301066369288093031847)
      ·
        refine ⟨95650951599553932139547771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63767301066369288093031847 95650951599553932139547771)
        ·
          refine ⟨143476427399330898209321657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95650951599553932139547771 143476427399330898209321657)
          ·
            refine ⟨107607320549498173656991243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143476427399330898209321657 107607320549498173656991243)
            ·
              refine ⟨161410980824247260485486865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107607320549498173656991243 161410980824247260485486865)
              ·
                refine ⟨121058235618185445364115149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161410980824247260485486865 121058235618185445364115149)
                ·
                  refine ⟨45396838356819542011543181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121058235618185445364115149 45396838356819542011543181)
                  ·
                    refine ⟨17023814383807328254328693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45396838356819542011543181 17023814383807328254328693)
                    ·
                      refine ⟨1595982598481937023843315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17023814383807328254328693 1595982598481937023843315)
                      ·
                        rfl

theorem cell23_3108165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_3108165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108165 prefixEnd_3108165 := by exact prefixLift 3108165
  have htrace : WordTrace (prefixWord ++ tailWord_3108165) baseStart_3108165 baseEnd_3108165 := by
    simpa [prefixWord, tailWord_3108165, baseEnd_3108165] using wordTrace_append hprefix tailTrace_3108165
  have hstable : (prefixWord ++ tailWord_3108165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108165).length < 2 ^ (prefixWord ++ tailWord_3108165).sum := by decide
  have hdescent : baseEnd_3108165 < baseStart_3108165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108179 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 6, 2, 2]
def baseStart_3108179 : Nat := 118140960795 + 3108179 * 2 ^ 59
def prefixEnd_3108179 : Nat := 4983230072969 + 3 ^ 40 * 3108179 * 2
def baseEnd_3108179 : Nat := 1595989787211099969068251

theorem tailTrace_3108179 : CollatzResearch.WordTrace tailWord_3108179 prefixEnd_3108179 1595989787211099969068251 := by
  unfold tailWord_3108179
  simp only [CollatzResearch.WordTrace]
  refine ⟨113364601406605792556399591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75576400937737195037599727 113364601406605792556399591)
  ·
    refine ⟨170046902109908688834599387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113364601406605792556399591 170046902109908688834599387)
    ·
      refine ⟨255070353164863033251899081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170046902109908688834599387 255070353164863033251899081)
      ·
        refine ⟨191302764873647274938924311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255070353164863033251899081 191302764873647274938924311)
        ·
          refine ⟨286954147310470912408386467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191302764873647274938924311 286954147310470912408386467)
          ·
            refine ⟨430431220965706368612579701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286954147310470912408386467 430431220965706368612579701)
            ·
              refine ⟨40352926965534972057429347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 430431220965706368612579701 40352926965534972057429347)
              ·
                refine ⟨60529390448302458086144021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40352926965534972057429347 60529390448302458086144021)
                ·
                  refine ⟨2837315177264177722788001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60529390448302458086144021 2837315177264177722788001)
                  ·
                    refine ⟨2127986382948133292091001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2837315177264177722788001 2127986382948133292091001)
                    ·
                      refine ⟨1595989787211099969068251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127986382948133292091001 1595989787211099969068251)
                      ·
                        rfl

theorem cell23_3108179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 2, 2].length) (baseStart_3108179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108179 prefixEnd_3108179 := by exact prefixLift 3108179
  have htrace : WordTrace (prefixWord ++ tailWord_3108179) baseStart_3108179 baseEnd_3108179 := by
    simpa [prefixWord, tailWord_3108179, baseEnd_3108179] using wordTrace_append hprefix tailTrace_3108179
  have hstable : (prefixWord ++ tailWord_3108179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108179).length < 2 ^ (prefixWord ++ tailWord_3108179).sum := by decide
  have hdescent : baseEnd_3108179 < baseStart_3108179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108185 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 9]
def baseStart_3108185 : Nat := 118140960795 + 3108185 * 2 ^ 59
def prefixEnd_3108185 : Nat := 4983230072969 + 3 ^ 40 * 3108185 * 2
def baseEnd_3108185 : Nat := 177332540899447438399247

theorem tailTrace_3108185 : CollatzResearch.WordTrace tailWord_3108185 prefixEnd_3108185 177332540899447438399247 := by
  unfold tailWord_3108185
  simp only [CollatzResearch.WordTrace]
  refine ⟨113364820244584055581118009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75576546829722703720745339 113364820244584055581118009)
  ·
    refine ⟨85023615183438041685838507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113364820244584055581118009 85023615183438041685838507)
    ·
      refine ⟨127535422775157062528757761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85023615183438041685838507 127535422775157062528757761)
      ·
        refine ⟨95651567081367796896568321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127535422775157062528757761 95651567081367796896568321)
        ·
          refine ⟨71738675311025847672426241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95651567081367796896568321 71738675311025847672426241)
          ·
            refine ⟨53804006483269385754319681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71738675311025847672426241 53804006483269385754319681)
            ·
              refine ⟨40353004862452039315739761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53804006483269385754319681 40353004862452039315739761)
              ·
                refine ⟨30264753646839029486804821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40353004862452039315739761 30264753646839029486804821)
                ·
                  refine ⟨177332540899447438399247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30264753646839029486804821 177332540899447438399247)
                  ·
                    rfl

theorem cell23_3108185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 9].length) (baseStart_3108185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108185 prefixEnd_3108185 := by exact prefixLift 3108185
  have htrace : WordTrace (prefixWord ++ tailWord_3108185) baseStart_3108185 baseEnd_3108185 := by
    simpa [prefixWord, tailWord_3108185, baseEnd_3108185] using wordTrace_append hprefix tailTrace_3108185
  have hstable : (prefixWord ++ tailWord_3108185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108185).length < 2 ^ (prefixWord ++ tailWord_3108185).sum := by decide
  have hdescent : baseEnd_3108185 < baseStart_3108185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108196 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_3108196 : Nat := 118140960795 + 3108196 * 2 ^ 59
def prefixEnd_3108196 : Nat := 4983230072969 + 3 ^ 40 * 3108196 * 2
def baseEnd_3108196 : Nat := 1595998516382226402555673

theorem tailTrace_3108196 : CollatzResearch.WordTrace tailWord_3108196 prefixEnd_3108196 1595998516382226402555673 := by
  unfold tailWord_3108196
  simp only [CollatzResearch.WordTrace]
  refine ⟨56682610723772102229884221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75576814298362802973178961 56682610723772102229884221)
  ·
    refine ⟨21255979021414538336206583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56682610723772102229884221 21255979021414538336206583)
    ·
      refine ⟨31883968532121807504309875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21255979021414538336206583 31883968532121807504309875)
      ·
        refine ⟨47825952798182711256464813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31883968532121807504309875 47825952798182711256464813)
        ·
          refine ⟨17934732299318516721174305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47825952798182711256464813 17934732299318516721174305)
          ·
            refine ⟨13451049224488887540880729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17934732299318516721174305 13451049224488887540880729)
            ·
              refine ⟨10088286918366665655660547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13451049224488887540880729 10088286918366665655660547)
              ·
                refine ⟨15132430377549998483490821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10088286918366665655660547 15132430377549998483490821)
                ·
                  refine ⟨2837330695790624715654529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15132430377549998483490821 2837330695790624715654529)
                  ·
                    refine ⟨2127998021842968536740897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2837330695790624715654529 2127998021842968536740897)
                    ·
                      refine ⟨1595998516382226402555673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2127998021842968536740897 1595998516382226402555673)
                      ·
                        rfl

theorem cell23_3108196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_3108196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108196 prefixEnd_3108196 := by exact prefixLift 3108196
  have htrace : WordTrace (prefixWord ++ tailWord_3108196) baseStart_3108196 baseEnd_3108196 := by
    simpa [prefixWord, tailWord_3108196, baseEnd_3108196] using wordTrace_append hprefix tailTrace_3108196
  have hstable : (prefixWord ++ tailWord_3108196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108196).length < 2 ^ (prefixWord ++ tailWord_3108196).sum := by decide
  have hdescent : baseEnd_3108196 < baseStart_3108196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108253 : List Nat := [1, 4, 2, 1, 3, 3, 2, 2, 5]
def baseStart_3108253 : Nat := 118140960795 + 3108253 * 2 ^ 59
def prefixEnd_3108253 : Nat := 4983230072969 + 3 ^ 40 * 3108253 * 2
def baseEnd_3108253 : Nat := 177336420531059186615879

theorem tailTrace_3108253 : CollatzResearch.WordTrace tailWord_3108253 prefixEnd_3108253 177336420531059186615879 := by
  unfold tailWord_3108253
  simp only [CollatzResearch.WordTrace]
  refine ⟨113367300408337703194593413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75578200272225135463062275 113367300408337703194593413)
  ·
    refine ⟨21256368826563319348986265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113367300408337703194593413 21256368826563319348986265)
    ·
      refine ⟨15942276619922489511739699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21256368826563319348986265 15942276619922489511739699)
      ·
        refine ⟨23913414929883734267609549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15942276619922489511739699 23913414929883734267609549)
        ·
          refine ⟨8967530598706400350353581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23913414929883734267609549 8967530598706400350353581)
          ·
            refine ⟨3362823974514900131382593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8967530598706400350353581 3362823974514900131382593)
            ·
              refine ⟨2522117980886175098536945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362823974514900131382593 2522117980886175098536945)
              ·
                refine ⟨1891588485664631323902709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522117980886175098536945 1891588485664631323902709)
                ·
                  refine ⟨177336420531059186615879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1891588485664631323902709 177336420531059186615879)
                  ·
                    rfl

theorem cell23_3108253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_3108253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108253 prefixEnd_3108253 := by exact prefixLift 3108253
  have htrace : WordTrace (prefixWord ++ tailWord_3108253) baseStart_3108253 baseEnd_3108253 := by
    simpa [prefixWord, tailWord_3108253, baseEnd_3108253] using wordTrace_append hprefix tailTrace_3108253
  have hstable : (prefixWord ++ tailWord_3108253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108253).length < 2 ^ (prefixWord ++ tailWord_3108253).sum := by decide
  have hdescent : baseEnd_3108253 < baseStart_3108253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108279 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 3, 4]
def baseStart_3108279 : Nat := 118140960795 + 3108279 * 2 ^ 59
def prefixEnd_3108279 : Nat := 4983230072969 + 3 ^ 40 * 3108279 * 2
def baseEnd_3108279 : Nat := 532013711758849859272597

theorem tailTrace_3108279 : CollatzResearch.WordTrace tailWord_3108279 prefixEnd_3108279 532013711758849859272597 := by
  unfold tailWord_3108279
  simp only [CollatzResearch.WordTrace]
  refine ⟨113368248706243509635039891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75578832470829006423359927 113368248706243509635039891)
  ·
    refine ⟨170052373059365264452559837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113368248706243509635039891 170052373059365264452559837)
    ·
      refine ⟨63769639897261974169709939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170052373059365264452559837 63769639897261974169709939)
      ·
        refine ⟨95654459845892961254564909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63769639897261974169709939 95654459845892961254564909)
        ·
          refine ⟨35870422442209860470461841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95654459845892961254564909 35870422442209860470461841)
          ·
            refine ⟨26902816831657395352846381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35870422442209860470461841 26902816831657395352846381)
            ·
              refine ⟨10088556311871523257317393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26902816831657395352846381 10088556311871523257317393)
              ·
                refine ⟨7566417233903642442988045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10088556311871523257317393 7566417233903642442988045)
                ·
                  refine ⟨2837406462713865916120517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7566417233903642442988045 2837406462713865916120517)
                  ·
                    refine ⟨532013711758849859272597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2837406462713865916120517 532013711758849859272597)
                    ·
                      rfl

theorem cell23_3108279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_3108279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108279 prefixEnd_3108279 := by exact prefixLift 3108279
  have htrace : WordTrace (prefixWord ++ tailWord_3108279) baseStart_3108279 baseEnd_3108279 := by
    simpa [prefixWord, tailWord_3108279, baseEnd_3108279] using wordTrace_append hprefix tailTrace_3108279
  have hstable : (prefixWord ++ tailWord_3108279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108279).length < 2 ^ (prefixWord ++ tailWord_3108279).sum := by decide
  have hdescent : baseEnd_3108279 < baseStart_3108279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108312 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3108312 : Nat := 118140960795 + 3108312 * 2 ^ 59
def prefixEnd_3108312 : Nat := 4983230072969 + 3 ^ 40 * 3108312 * 2
def baseEnd_3108312 : Nat := 1596058080138147948705139

theorem tailTrace_3108312 : CollatzResearch.WordTrace tailWord_3108312 prefixEnd_3108312 1596058080138147948705139 := by
  unfold tailWord_3108312
  simp only [CollatzResearch.WordTrace]
  refine ⟨56684726157561978135495595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75579634876749304180660793 56684726157561978135495595)
  ·
    refine ⟨85027089236342967203243393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56684726157561978135495595 85027089236342967203243393)
    ·
      refine ⟨63770316927257225402432545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85027089236342967203243393 63770316927257225402432545)
      ·
        refine ⟨47827737695442919051824409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63770316927257225402432545 47827737695442919051824409)
        ·
          refine ⟨35870803271582189288868307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47827737695442919051824409 35870803271582189288868307)
          ·
            refine ⟨53806204907373283933302461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35870803271582189288868307 53806204907373283933302461)
            ·
              refine ⟨20177326840264981474988423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53806204907373283933302461 20177326840264981474988423)
              ·
                refine ⟨30265990260397472212482635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20177326840264981474988423 30265990260397472212482635)
                ·
                  refine ⟨45398985390596208318723953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30265990260397472212482635 45398985390596208318723953)
                  ·
                    refine ⟨34049239042947156239042965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45398985390596208318723953 34049239042947156239042965)
                    ·
                      refine ⟨1596058080138147948705139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34049239042947156239042965 1596058080138147948705139)
                      ·
                        rfl

theorem cell23_3108312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3108312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108312 prefixEnd_3108312 := by exact prefixLift 3108312
  have htrace : WordTrace (prefixWord ++ tailWord_3108312) baseStart_3108312 baseEnd_3108312 := by
    simpa [prefixWord, tailWord_3108312, baseEnd_3108312] using wordTrace_append hprefix tailTrace_3108312
  have hstable : (prefixWord ++ tailWord_3108312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108312).length < 2 ^ (prefixWord ++ tailWord_3108312).sum := by decide
  have hdescent : baseEnd_3108312 < baseStart_3108312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108336 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 3, 1, 3]
def baseStart_3108336 : Nat := 118140960795 + 3108336 * 2 ^ 59
def prefixEnd_3108336 : Nat := 4983230072969 + 3 ^ 40 * 3108336 * 2
def baseEnd_3108336 : Nat := 1596070403673855854805029

theorem tailTrace_3108336 : CollatzResearch.WordTrace tailWord_3108336 prefixEnd_3108336 1596070403673855854805029 := by
  unfold tailWord_3108336
  simp only [CollatzResearch.WordTrace]
  refine ⟨56685163833518504184932431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75580218444691338913243241 56685163833518504184932431)
  ·
    refine ⟨85027745750277756277398647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56685163833518504184932431 85027745750277756277398647)
    ·
      refine ⟨127541618625416634416097971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85027745750277756277398647 127541618625416634416097971)
      ·
        refine ⟨191312427938124951624146957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127541618625416634416097971 191312427938124951624146957)
        ·
          refine ⟨71742160476796856859055109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191312427938124951624146957 71742160476796856859055109)
          ·
            refine ⟨13451655089399410661072833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71742160476796856859055109 13451655089399410661072833)
            ·
              refine ⟨10088741317049557995804625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13451655089399410661072833 10088741317049557995804625)
              ·
                refine ⟨7566555987787168496853469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10088741317049557995804625 7566555987787168496853469)
                ·
                  refine ⟨2837458495420188186320051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7566555987787168496853469 2837458495420188186320051)
                  ·
                    refine ⟨4256187743130282279480077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2837458495420188186320051 4256187743130282279480077)
                    ·
                      refine ⟨1596070403673855854805029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4256187743130282279480077 1596070403673855854805029)
                      ·
                        rfl

theorem cell23_3108336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 1, 3].length) (baseStart_3108336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108336 prefixEnd_3108336 := by exact prefixLift 3108336
  have htrace : WordTrace (prefixWord ++ tailWord_3108336) baseStart_3108336 baseEnd_3108336 := by
    simpa [prefixWord, tailWord_3108336, baseEnd_3108336] using wordTrace_append hprefix tailTrace_3108336
  have hstable : (prefixWord ++ tailWord_3108336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108336).length < 2 ^ (prefixWord ++ tailWord_3108336).sum := by decide
  have hdescent : baseEnd_3108336 < baseStart_3108336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108346 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2]
def baseStart_3108346 : Nat := 118140960795 + 3108346 * 2 ^ 59
def prefixEnd_3108346 : Nat := 4983230072969 + 3 ^ 40 * 3108346 * 2
def baseEnd_3108346 : Nat := 1596075538480400815679983

theorem tailTrace_3108346 : CollatzResearch.WordTrace tailWord_3108346 prefixEnd_3108346 1596075538480400815679983 := by
  unfold tailWord_3108346
  simp only [CollatzResearch.WordTrace]
  refine ⟨28342673099250195019432223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75580461598000520051819261 28342673099250195019432223)
  ·
    refine ⟨42514009648875292529148335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28342673099250195019432223 42514009648875292529148335)
    ·
      refine ⟨63771014473312938793722503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42514009648875292529148335 63771014473312938793722503)
      ·
        refine ⟨95656521709969408190583755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63771014473312938793722503 95656521709969408190583755)
        ·
          refine ⟨143484782564954112285875633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95656521709969408190583755 143484782564954112285875633)
          ·
            refine ⟨107613586923715584214406725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143484782564954112285875633 107613586923715584214406725)
            ·
              refine ⟨20177547548196672040201261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107613586923715584214406725 20177547548196672040201261)
              ·
                refine ⟨7566580330573752015075473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20177547548196672040201261 7566580330573752015075473)
                ·
                  refine ⟨5674935247930314011306605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7566580330573752015075473 5674935247930314011306605)
                  ·
                    refine ⟨2128100717973867754239977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5674935247930314011306605 2128100717973867754239977)
                    ·
                      refine ⟨1596075538480400815679983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128100717973867754239977 1596075538480400815679983)
                      ·
                        rfl

theorem cell23_3108346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_3108346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108346 prefixEnd_3108346 := by exact prefixLift 3108346
  have htrace : WordTrace (prefixWord ++ tailWord_3108346) baseStart_3108346 baseEnd_3108346 := by
    simpa [prefixWord, tailWord_3108346, baseEnd_3108346] using wordTrace_append hprefix tailTrace_3108346
  have hstable : (prefixWord ++ tailWord_3108346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108346).length < 2 ^ (prefixWord ++ tailWord_3108346).sum := by decide
  have hdescent : baseEnd_3108346 < baseStart_3108346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108363 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 2, 3, 2]
def baseStart_3108363 : Nat := 118140960795 + 3108363 * 2 ^ 59
def prefixEnd_3108363 : Nat := 4983230072969 + 3 ^ 40 * 3108363 * 2
def baseEnd_3108363 : Nat := 1596084267651527249167405

theorem tailTrace_3108363 : CollatzResearch.WordTrace tailWord_3108363 prefixEnd_3108363 1596084267651527249167405 := by
  unfold tailWord_3108363
  simp only [CollatzResearch.WordTrace]
  refine ⟨113371312437939191981097743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75580874958626127987398495 113371312437939191981097743)
  ·
    refine ⟨170056968656908787971646615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113371312437939191981097743 170056968656908787971646615)
    ·
      refine ⟨255085452985363181957469923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170056968656908787971646615 255085452985363181957469923)
      ·
        refine ⟨382628179478044772936204885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255085452985363181957469923 382628179478044772936204885)
        ·
          refine ⟨4483923978258337182846151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 382628179478044772936204885 4483923978258337182846151)
          ·
            refine ⟨6725885967387505774269227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483923978258337182846151 6725885967387505774269227)
            ·
              refine ⟨10088828951081258661403841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6725885967387505774269227 10088828951081258661403841)
              ·
                refine ⟨7566621713310943996052881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10088828951081258661403841 7566621713310943996052881)
                ·
                  refine ⟨5674966284983207997039661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7566621713310943996052881 5674966284983207997039661)
                  ·
                    refine ⟨2128112356868702998889873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5674966284983207997039661 2128112356868702998889873)
                    ·
                      refine ⟨1596084267651527249167405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128112356868702998889873 1596084267651527249167405)
                      ·
                        rfl

theorem cell23_3108363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 3, 2].length) (baseStart_3108363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108363 prefixEnd_3108363 := by exact prefixLift 3108363
  have htrace : WordTrace (prefixWord ++ tailWord_3108363) baseStart_3108363 baseEnd_3108363 := by
    simpa [prefixWord, tailWord_3108363, baseEnd_3108363] using wordTrace_append hprefix tailTrace_3108363
  have hstable : (prefixWord ++ tailWord_3108363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108363).length < 2 ^ (prefixWord ++ tailWord_3108363).sum := by decide
  have hdescent : baseEnd_3108363 < baseStart_3108363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108369 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 4, 4]
def baseStart_3108369 : Nat := 118140960795 + 3108369 * 2 ^ 59
def prefixEnd_3108369 : Nat := 4983230072969 + 3 ^ 40 * 3108369 * 2
def baseEnd_3108369 : Nat := 532029116178484741897459

theorem tailTrace_3108369 : CollatzResearch.WordTrace tailWord_3108369 prefixEnd_3108369 532029116178484741897459 := by
  unfold tailWord_3108369
  simp only [CollatzResearch.WordTrace]
  refine ⟨113371531275917455005816161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75581020850611636670544107 113371531275917455005816161)
  ·
    refine ⟨85028648456938091254362121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113371531275917455005816161 85028648456938091254362121)
    ·
      refine ⟨63771486342703568440771591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85028648456938091254362121 63771486342703568440771591)
      ·
        refine ⟨95657229514055352661157387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63771486342703568440771591 95657229514055352661157387)
        ·
          refine ⟨143485844271083028991736081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95657229514055352661157387 143485844271083028991736081)
          ·
            refine ⟨107614383203312271743802061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143485844271083028991736081 107614383203312271743802061)
            ·
              refine ⟨40355393701242101903925773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107614383203312271743802061 40355393701242101903925773)
              ·
                refine ⟨15133272637965788213972165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40355393701242101903925773 15133272637965788213972165)
                ·
                  refine ⟨2837488619618585290119781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15133272637965788213972165 2837488619618585290119781)
                  ·
                    refine ⟨532029116178484741897459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2837488619618585290119781 532029116178484741897459)
                    ·
                      rfl

theorem cell23_3108369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_3108369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108369 prefixEnd_3108369 := by exact prefixLift 3108369
  have htrace : WordTrace (prefixWord ++ tailWord_3108369) baseStart_3108369 baseEnd_3108369 := by
    simpa [prefixWord, tailWord_3108369, baseEnd_3108369] using wordTrace_append hprefix tailTrace_3108369
  have hstable : (prefixWord ++ tailWord_3108369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108369).length < 2 ^ (prefixWord ++ tailWord_3108369).sum := by decide
  have hdescent : baseEnd_3108369 < baseStart_3108369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108389 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_3108389 : Nat := 118140960795 + 3108389 * 2 ^ 59
def prefixEnd_3108389 : Nat := 4983230072969 + 3 ^ 40 * 3108389 * 2
def baseEnd_3108389 : Nat := 1596097618148544147442285

theorem tailTrace_3108389 : CollatzResearch.WordTrace tailWord_3108389 prefixEnd_3108389 1596097618148544147442285 := by
  unfold tailWord_3108389
  simp only [CollatzResearch.WordTrace]
  refine ⟨113372260735844998421544221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75581507157229998947696147 113372260735844998421544221)
  ·
    refine ⟨42514597775941874408079083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113372260735844998421544221 42514597775941874408079083)
    ·
      refine ⟨63771896663912811612118625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42514597775941874408079083 63771896663912811612118625)
      ·
        refine ⟨47828922497934608709088969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63771896663912811612118625 47828922497934608709088969)
        ·
          refine ⟨35871691873450956531816727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47828922497934608709088969 35871691873450956531816727)
          ·
            refine ⟨53807537810176434797725091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35871691873450956531816727 53807537810176434797725091)
            ·
              refine ⟨80711306715264652196587637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53807537810176434797725091 80711306715264652196587637)
              ·
                refine ⟨7566685004556061143430091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80711306715264652196587637 7566685004556061143430091)
                ·
                  refine ⟨11350027506834091715145137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7566685004556061143430091 11350027506834091715145137)
                  ·
                    refine ⟨8512520630125568786358853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11350027506834091715145137 8512520630125568786358853)
                    ·
                      refine ⟨1596097618148544147442285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8512520630125568786358853 1596097618148544147442285)
                      ·
                        rfl

theorem cell23_3108389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_3108389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108389 prefixEnd_3108389 := by exact prefixLift 3108389
  have htrace : WordTrace (prefixWord ++ tailWord_3108389) baseStart_3108389 baseEnd_3108389 := by
    simpa [prefixWord, tailWord_3108389, baseEnd_3108389] using wordTrace_append hprefix tailTrace_3108389
  have hstable : (prefixWord ++ tailWord_3108389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108389).length < 2 ^ (prefixWord ++ tailWord_3108389).sum := by decide
  have hdescent : baseEnd_3108389 < baseStart_3108389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108410 : List Nat := [3, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2]
def baseStart_3108410 : Nat := 118140960795 + 3108410 * 2 ^ 59
def prefixEnd_3108410 : Nat := 4983230072969 + 3 ^ 40 * 3108410 * 2
def baseEnd_3108410 : Nat := 1596108401242288565279689

theorem tailTrace_3108410 : CollatzResearch.WordTrace tailWord_3108410 prefixEnd_3108410 1596108401242288565279689 := by
  unfold tailWord_3108410
  simp only [CollatzResearch.WordTrace]
  refine ⟨28343256667192229752014671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75582017779179279338705789 28343256667192229752014671)
  ·
    refine ⟨42514885000788344628022007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28343256667192229752014671 42514885000788344628022007)
    ·
      refine ⟨63772327501182516942033011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42514885000788344628022007 63772327501182516942033011)
      ·
        refine ⟨95658491251773775413049517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63772327501182516942033011 95658491251773775413049517)
        ·
          refine ⟨35871934219415165779893569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95658491251773775413049517 35871934219415165779893569)
          ·
            refine ⟨26903950664561374334920177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35871934219415165779893569 26903950664561374334920177)
            ·
              refine ⟨20177962998421030751190133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26903950664561374334920177 20177962998421030751190133)
              ·
                refine ⟨1891684031101971632924075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20177962998421030751190133 1891684031101971632924075)
                ·
                  refine ⟨2837526046652957449386113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891684031101971632924075 2837526046652957449386113)
                  ·
                    refine ⟨2128144534989718087039585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2837526046652957449386113 2128144534989718087039585)
                    ·
                      refine ⟨1596108401242288565279689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128144534989718087039585 1596108401242288565279689)
                      ·
                        rfl

theorem cell23_3108410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2].length) (baseStart_3108410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108410 prefixEnd_3108410 := by exact prefixLift 3108410
  have htrace : WordTrace (prefixWord ++ tailWord_3108410) baseStart_3108410 baseEnd_3108410 := by
    simpa [prefixWord, tailWord_3108410, baseEnd_3108410] using wordTrace_append hprefix tailTrace_3108410
  have hstable : (prefixWord ++ tailWord_3108410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108410).length < 2 ^ (prefixWord ++ tailWord_3108410).sum := by decide
  have hdescent : baseEnd_3108410 < baseStart_3108410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108413 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3108413 : Nat := 118140960795 + 3108413 * 2 ^ 59
def prefixEnd_3108413 : Nat := 4983230072969 + 3 ^ 40 * 3108413 * 2
def baseEnd_3108413 : Nat := 1596109941684252053542175

theorem tailTrace_3108413 : CollatzResearch.WordTrace tailWord_3108413 prefixEnd_3108413 1596109941684252053542175 := by
  unfold tailWord_3108413
  simp only [CollatzResearch.WordTrace]
  refine ⟨113373136087758050520417893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75582090725172033680278595 113373136087758050520417893)
  ·
    refine ⟨21257463016454634472578355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113373136087758050520417893 21257463016454634472578355)
    ·
      refine ⟨31886194524681951708867533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21257463016454634472578355 31886194524681951708867533)
      ·
        refine ⟨11957322946755731890825325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31886194524681951708867533 11957322946755731890825325)
        ·
          refine ⟨4483996105033399459059497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11957322946755731890825325 4483996105033399459059497)
          ·
            refine ⟨3362997078775049594294623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483996105033399459059497 3362997078775049594294623)
            ·
              refine ⟨5044495618162574391441935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362997078775049594294623 5044495618162574391441935)
              ·
                refine ⟨7566743427243861587162903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5044495618162574391441935 7566743427243861587162903)
                ·
                  refine ⟨11350115140865792380744355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7566743427243861587162903 11350115140865792380744355)
                  ·
                    refine ⟨17025172711298688571116533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11350115140865792380744355 17025172711298688571116533)
                    ·
                      refine ⟨1596109941684252053542175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17025172711298688571116533 1596109941684252053542175)
                      ·
                        rfl

theorem cell23_3108413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3108413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108413 prefixEnd_3108413 := by exact prefixLift 3108413
  have htrace : WordTrace (prefixWord ++ tailWord_3108413) baseStart_3108413 baseEnd_3108413 := by
    simpa [prefixWord, tailWord_3108413, baseEnd_3108413] using wordTrace_append hprefix tailTrace_3108413
  have hstable : (prefixWord ++ tailWord_3108413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108413).length < 2 ^ (prefixWord ++ tailWord_3108413).sum := by decide
  have hdescent : baseEnd_3108413 < baseStart_3108413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108449 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_3108449 : Nat := 118140960795 + 3108449 * 2 ^ 59
def prefixEnd_3108449 : Nat := 4983230072969 + 3 ^ 40 * 3108449 * 2
def baseEnd_3108449 : Nat := 1596128426987813912692009

theorem tailTrace_3108449 : CollatzResearch.WordTrace tailWord_3108449 prefixEnd_3108449 1596128426987813912692009 := by
  unfold tailWord_3108449
  simp only [CollatzResearch.WordTrace]
  refine ⟨113374449115627628668728401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75582966077085085779152267 113374449115627628668728401)
  ·
    refine ⟨85030836836720721501546301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113374449115627628668728401 85030836836720721501546301)
    ·
      refine ⟨31886563813770270563079863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85030836836720721501546301 31886563813770270563079863)
      ·
        refine ⟨47829845720655405844619795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31886563813770270563079863 47829845720655405844619795)
        ·
          refine ⟨71744768580983108766929693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47829845720655405844619795 71744768580983108766929693)
          ·
            refine ⟨26904288217868665787598635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71744768580983108766929693 26904288217868665787598635)
            ·
              refine ⟨40356432326802998681397953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26904288217868665787598635 40356432326802998681397953)
              ·
                refine ⟨30267324245102249011048465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40356432326802998681397953 30267324245102249011048465)
                ·
                  refine ⟨22700493183826686758286349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30267324245102249011048465 22700493183826686758286349)
                  ·
                    refine ⟨8512684943935007534357381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22700493183826686758286349 8512684943935007534357381)
                    ·
                      refine ⟨1596128426987813912692009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8512684943935007534357381 1596128426987813912692009)
                      ·
                        rfl

theorem cell23_3108449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_3108449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108449 prefixEnd_3108449 := by exact prefixLift 3108449
  have htrace : WordTrace (prefixWord ++ tailWord_3108449) baseStart_3108449 baseEnd_3108449 := by
    simpa [prefixWord, tailWord_3108449, baseEnd_3108449] using wordTrace_append hprefix tailTrace_3108449
  have hstable : (prefixWord ++ tailWord_3108449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108449).length < 2 ^ (prefixWord ++ tailWord_3108449).sum := by decide
  have hdescent : baseEnd_3108449 < baseStart_3108449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108453 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 3, 3, 2]
def baseStart_3108453 : Nat := 118140960795 + 3108453 * 2 ^ 59
def prefixEnd_3108453 : Nat := 4983230072969 + 3 ^ 40 * 3108453 * 2
def baseEnd_3108453 : Nat := 1596130480910431897041991

theorem tailTrace_3108453 : CollatzResearch.WordTrace tailWord_3108453 prefixEnd_3108453 1596130480910431897041991 := by
  unfold tailWord_3108453
  simp only [CollatzResearch.WordTrace]
  refine ⟨113374595007613137351874013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75583063338408758234582675 113374595007613137351874013)
  ·
    refine ⟨42515473127854926506952755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113374595007613137351874013 42515473127854926506952755)
    ·
      refine ⟨63773209691782389760429133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42515473127854926506952755 63773209691782389760429133)
      ·
        refine ⟨23914953634418396160160925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63773209691782389760429133 23914953634418396160160925)
        ·
          refine ⟨8968107612906898560060347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23914953634418396160160925 8968107612906898560060347)
          ·
            refine ⟨13452161419360347840090521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8968107612906898560060347 13452161419360347840090521)
            ·
              refine ⟨10089121064520260880067891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13452161419360347840090521 10089121064520260880067891)
              ·
                refine ⟨15133681596780391320101837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10089121064520260880067891 15133681596780391320101837)
                ·
                  refine ⟨5675130598792646745038189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15133681596780391320101837 5675130598792646745038189)
                  ·
                    refine ⟨2128173974547242529389321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5675130598792646745038189 2128173974547242529389321)
                    ·
                      refine ⟨1596130480910431897041991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128173974547242529389321 1596130480910431897041991)
                      ·
                        rfl

theorem cell23_3108453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_3108453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108453 prefixEnd_3108453 := by exact prefixLift 3108453
  have htrace : WordTrace (prefixWord ++ tailWord_3108453) baseStart_3108453 baseEnd_3108453 := by
    simpa [prefixWord, tailWord_3108453, baseEnd_3108453] using wordTrace_append hprefix tailTrace_3108453
  have hstable : (prefixWord ++ tailWord_3108453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108453).length < 2 ^ (prefixWord ++ tailWord_3108453).sum := by decide
  have hdescent : baseEnd_3108453 < baseStart_3108453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108489 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 7]
def baseStart_3108489 : Nat := 118140960795 + 3108489 * 2 ^ 59
def prefixEnd_3108489 : Nat := 4983230072969 + 3 ^ 40 * 3108489 * 2
def baseEnd_3108489 : Nat := 177349885134888195132425

theorem tailTrace_3108489 : CollatzResearch.WordTrace tailWord_3108489 prefixEnd_3108489 177349885134888195132425 := by
  unfold tailWord_3108489
  simp only [CollatzResearch.WordTrace]
  refine ⟨113375908035482715500184521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75583938690321810333456347 113375908035482715500184521)
  ·
    refine ⟨85031931026612036625138391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113375908035482715500184521 85031931026612036625138391)
    ·
      refine ⟨127547896539918054937707587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85031931026612036625138391 127547896539918054937707587)
      ·
        refine ⟨191321844809877082406561381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127547896539918054937707587 191321844809877082406561381)
        ·
          refine ⟨35872845901851952951230259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191321844809877082406561381 35872845901851952951230259)
          ·
            refine ⟨53809268852777929426845389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35872845901851952951230259 53809268852777929426845389)
            ·
              refine ⟨20178475819791723535067021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53809268852777929426845389 20178475819791723535067021)
              ·
                refine ⟨7566928432421896325650133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20178475819791723535067021 7566928432421896325650133)
                ·
                  refine ⟨177349885134888195132425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7566928432421896325650133 177349885134888195132425)
                  ·
                    rfl

theorem cell23_3108489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 7].length) (baseStart_3108489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108489 prefixEnd_3108489 := by exact prefixLift 3108489
  have htrace : WordTrace (prefixWord ++ tailWord_3108489) baseStart_3108489 baseEnd_3108489 := by
    simpa [prefixWord, tailWord_3108489, baseEnd_3108489] using wordTrace_append hprefix tailTrace_3108489
  have hstable : (prefixWord ++ tailWord_3108489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108489).length < 2 ^ (prefixWord ++ tailWord_3108489).sum := by decide
  have hdescent : baseEnd_3108489 < baseStart_3108489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108540 : List Nat := [2, 2, 2, 3, 1, 3, 3, 2, 5]
def baseStart_3108540 : Nat := 118140960795 + 3108540 * 2 ^ 59
def prefixEnd_3108540 : Nat := 4983230072969 + 3 ^ 40 * 3108540 * 2
def baseEnd_3108540 : Nat := 177352794858597006294899

theorem tailTrace_3108540 : CollatzResearch.WordTrace tailWord_3108540 prefixEnd_3108540 177352794858597006294899 := by
  unfold tailWord_3108540
  simp only [CollatzResearch.WordTrace]
  refine ⟨56688884079148975605145537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75585178772198634140194049 56688884079148975605145537)
  ·
    refine ⟨42516663059361731703859153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56688884079148975605145537 42516663059361731703859153)
    ·
      refine ⟨31887497294521298777894365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42516663059361731703859153 31887497294521298777894365)
      ·
        refine ⟨11957811485445487041710387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31887497294521298777894365 11957811485445487041710387)
        ·
          refine ⟨17936717228168230562565581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11957811485445487041710387 17936717228168230562565581)
          ·
            refine ⟨6726268960563086460962093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17936717228168230562565581 6726268960563086460962093)
            ·
              refine ⟨2522350860211157422860785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6726268960563086460962093 2522350860211157422860785)
              ·
                refine ⟨1891763145158368067145589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522350860211157422860785 1891763145158368067145589)
                ·
                  refine ⟨177352794858597006294899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1891763145158368067145589 177352794858597006294899)
                  ·
                    rfl

theorem cell23_3108540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_3108540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108540 prefixEnd_3108540 := by exact prefixLift 3108540
  have htrace : WordTrace (prefixWord ++ tailWord_3108540) baseStart_3108540 baseEnd_3108540 := by
    simpa [prefixWord, tailWord_3108540, baseEnd_3108540] using wordTrace_append hprefix tailTrace_3108540
  have hstable : (prefixWord ++ tailWord_3108540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108540).length < 2 ^ (prefixWord ++ tailWord_3108540).sum := by decide
  have hdescent : baseEnd_3108540 < baseStart_3108540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108559 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_3108559 : Nat := 118140960795 + 3108559 * 2 ^ 59
def prefixEnd_3108559 : Nat := 4983230072969 + 3 ^ 40 * 3108559 * 2
def baseEnd_3108559 : Nat := 1596184909859808482316503

theorem tailTrace_3108559 : CollatzResearch.WordTrace tailWord_3108559 prefixEnd_3108559 1596184909859808482316503 := by
  unfold tailWord_3108559
  simp only [CollatzResearch.WordTrace]
  refine ⟨113378461145229117455232731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75585640763486078303488487 113378461145229117455232731)
  ·
    refine ⟨170067691717843676182849097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113378461145229117455232731 170067691717843676182849097)
    ·
      refine ⟨127550768788382757137136823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170067691717843676182849097 127550768788382757137136823)
      ·
        refine ⟨191326153182574135705705235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127550768788382757137136823 191326153182574135705705235)
        ·
          refine ⟨286989229773861203558557853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191326153182574135705705235 286989229773861203558557853)
          ·
            refine ⟨107620961165197951334459195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286989229773861203558557853 107620961165197951334459195)
            ·
              refine ⟨161431441747796927001688793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107620961165197951334459195 161431441747796927001688793)
              ·
                refine ⟨121073581310847695251266595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161431441747796927001688793 121073581310847695251266595)
                ·
                  refine ⟨181610371966271542876899893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121073581310847695251266595 181610371966271542876899893)
                  ·
                    refine ⟨17025972371837957144709365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181610371966271542876899893 17025972371837957144709365)
                    ·
                      refine ⟨1596184909859808482316503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17025972371837957144709365 1596184909859808482316503)
                      ·
                        rfl

theorem cell23_3108559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_3108559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108559 prefixEnd_3108559 := by exact prefixLift 3108559
  have htrace : WordTrace (prefixWord ++ tailWord_3108559) baseStart_3108559 baseEnd_3108559 := by
    simpa [prefixWord, tailWord_3108559, baseEnd_3108559] using wordTrace_append hprefix tailTrace_3108559
  have hstable : (prefixWord ++ tailWord_3108559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108559).length < 2 ^ (prefixWord ++ tailWord_3108559).sum := by decide
  have hdescent : baseEnd_3108559 < baseStart_3108559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108576 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 3]
def baseStart_3108576 : Nat := 118140960795 + 3108576 * 2 ^ 59
def prefixEnd_3108576 : Nat := 4983230072969 + 3 ^ 40 * 3108576 * 2
def baseEnd_3108576 : Nat := 1596193639030934915803925

theorem tailTrace_3108576 : CollatzResearch.WordTrace tailWord_3108576 prefixEnd_3108576 1596193639030934915803925 := by
  unfold tailWord_3108576
  simp only [CollatzResearch.WordTrace]
  refine ⟨56689540593083764679300791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75586054124111686239067721 56689540593083764679300791)
  ·
    refine ⟨85034310889625647018951187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56689540593083764679300791 85034310889625647018951187)
    ·
      refine ⟨127551466334438470528426781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85034310889625647018951187 127551466334438470528426781)
      ·
        refine ⟨47831799875414426448160043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127551466334438470528426781 47831799875414426448160043)
        ·
          refine ⟨71747699813121639672240065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47831799875414426448160043 71747699813121639672240065)
          ·
            refine ⟨53810774859841229754180049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71747699813121639672240065 53810774859841229754180049)
            ·
              refine ⟨40358081144880922315635037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53810774859841229754180049 40358081144880922315635037)
              ·
                refine ⟨15134280429330345868363139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40358081144880922315635037 15134280429330345868363139)
                ·
                  refine ⟨22701420643995518802544709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15134280429330345868363139 22701420643995518802544709)
                  ·
                    refine ⟨4256516370749159775477133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22701420643995518802544709 4256516370749159775477133)
                    ·
                      refine ⟨1596193639030934915803925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4256516370749159775477133 1596193639030934915803925)
                      ·
                        rfl

theorem cell23_3108576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_3108576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108576 prefixEnd_3108576 := by exact prefixLift 3108576
  have htrace : WordTrace (prefixWord ++ tailWord_3108576) baseStart_3108576 baseEnd_3108576 := by
    simpa [prefixWord, tailWord_3108576, baseEnd_3108576] using wordTrace_append hprefix tailTrace_3108576
  have hstable : (prefixWord ++ tailWord_3108576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108576).length < 2 ^ (prefixWord ++ tailWord_3108576).sum := by decide
  have hdescent : baseEnd_3108576 < baseStart_3108576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108593 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_3108593 : Nat := 118140960795 + 3108593 * 2 ^ 59
def prefixEnd_3108593 : Nat := 4983230072969 + 3 ^ 40 * 3108593 * 2
def baseEnd_3108593 : Nat := 1596202368202061349291347

theorem tailTrace_3108593 : CollatzResearch.WordTrace tailWord_3108593 prefixEnd_3108593 1596202368202061349291347 := by
  unfold tailWord_3108593
  simp only [CollatzResearch.WordTrace]
  refine ⟨113379701227105941261970433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75586467484737294174646955 113379701227105941261970433)
  ·
    refine ⟨85034775920329455946477825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113379701227105941261970433 85034775920329455946477825)
    ·
      refine ⟨63776081940247091959858369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85034775920329455946477825 63776081940247091959858369)
      ·
        refine ⟨47832061455185318969893777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63776081940247091959858369 47832061455185318969893777)
        ·
          refine ⟨35874046091388989227420333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47832061455185318969893777 35874046091388989227420333)
          ·
            refine ⟨13452767284270870960282625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35874046091388989227420333 13452767284270870960282625)
            ·
              refine ⟨10089575463203153220211969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13452767284270870960282625 10089575463203153220211969)
              ·
                refine ⟨7567181597402364915158977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10089575463203153220211969 7567181597402364915158977)
                ·
                  refine ⟨5675386198051773686369233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7567181597402364915158977 5675386198051773686369233)
                  ·
                    refine ⟨4256539648538830264776925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675386198051773686369233 4256539648538830264776925)
                    ·
                      refine ⟨1596202368202061349291347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4256539648538830264776925 1596202368202061349291347)
                      ·
                        rfl

theorem cell23_3108593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_3108593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108593 prefixEnd_3108593 := by exact prefixLift 3108593
  have htrace : WordTrace (prefixWord ++ tailWord_3108593) baseStart_3108593 baseEnd_3108593 := by
    simpa [prefixWord, tailWord_3108593, baseEnd_3108593] using wordTrace_append hprefix tailTrace_3108593
  have hstable : (prefixWord ++ tailWord_3108593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108593).length < 2 ^ (prefixWord ++ tailWord_3108593).sum := by decide
  have hdescent : baseEnd_3108593 < baseStart_3108593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108621 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3108621 : Nat := 118140960795 + 3108621 * 2 ^ 59
def prefixEnd_3108621 : Nat := 4983230072969 + 3 ^ 40 * 3108621 * 2
def baseEnd_3108621 : Nat := 532072248553462413247073

theorem tailTrace_3108621 : CollatzResearch.WordTrace tailWord_3108621 prefixEnd_3108621 532072248553462413247073 := by
  unfold tailWord_3108621
  simp only [CollatzResearch.WordTrace]
  refine ⟨113380722471004502043989717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75587148314003001362659811 113380722471004502043989717)
  ·
    refine ⟨2657360682914168016656009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 113380722471004502043989717 2657360682914168016656009)
    ·
      refine ⟨1993020512185626012492007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2657360682914168016656009 1993020512185626012492007)
      ·
        refine ⟨2989530768278439018738011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993020512185626012492007 2989530768278439018738011)
        ·
          refine ⟨4484296152417658528107017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989530768278439018738011 4484296152417658528107017)
          ·
            refine ⟨3363222114313243896080263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4484296152417658528107017 3363222114313243896080263)
            ·
              refine ⟨5044833171469865844120395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363222114313243896080263 5044833171469865844120395)
              ·
                refine ⟨7567249757204798766180593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5044833171469865844120395 7567249757204798766180593)
                ·
                  refine ⟨5675437317903599074635445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7567249757204798766180593 5675437317903599074635445)
                  ·
                    refine ⟨532072248553462413247073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5675437317903599074635445 532072248553462413247073)
                    ·
                      rfl

theorem cell23_3108621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3108621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108621 prefixEnd_3108621 := by exact prefixLift 3108621
  have htrace : WordTrace (prefixWord ++ tailWord_3108621) baseStart_3108621 baseEnd_3108621 := by
    simpa [prefixWord, tailWord_3108621, baseEnd_3108621] using wordTrace_append hprefix tailTrace_3108621
  have hstable : (prefixWord ++ tailWord_3108621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108621).length < 2 ^ (prefixWord ++ tailWord_3108621).sum := by decide
  have hdescent : baseEnd_3108621 < baseStart_3108621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108657 : List Nat := [1, 2, 2, 3, 2, 2, 2, 4, 1, 1, 3]
def baseStart_3108657 : Nat := 118140960795 + 3108657 * 2 ^ 59
def prefixEnd_3108657 : Nat := 4983230072969 + 3 ^ 40 * 3108657 * 2
def baseEnd_3108657 : Nat := 1596235230963949098891053

theorem tailTrace_3108657 : CollatzResearch.WordTrace tailWord_3108657 prefixEnd_3108657 1596235230963949098891053 := by
  unfold tailWord_3108657
  simp only [CollatzResearch.WordTrace]
  refine ⟨113382035498874080192300225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75588023665916053461533483 113382035498874080192300225)
  ·
    refine ⟨85036526624155560144225169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113382035498874080192300225 85036526624155560144225169)
    ·
      refine ⟨63777394968116670108168877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85036526624155560144225169 63777394968116670108168877)
      ·
        refine ⟨23916523113043751290563329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63777394968116670108168877 23916523113043751290563329)
        ·
          refine ⟨17937392334782813467922497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23916523113043751290563329 17937392334782813467922497)
          ·
            refine ⟨13453044251087110100941873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17937392334782813467922497 13453044251087110100941873)
            ·
              refine ⟨10089783188315332575706405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13453044251087110100941873 10089783188315332575706405)
              ·
                refine ⟨1891834347809124857944951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10089783188315332575706405 1891834347809124857944951)
                ·
                  refine ⟨2837751521713687286917427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891834347809124857944951 2837751521713687286917427)
                  ·
                    refine ⟨4256627282570530930376141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2837751521713687286917427 4256627282570530930376141)
                    ·
                      refine ⟨1596235230963949098891053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4256627282570530930376141 1596235230963949098891053)
                      ·
                        rfl

theorem cell23_3108657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_3108657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108657 prefixEnd_3108657 := by exact prefixLift 3108657
  have htrace : WordTrace (prefixWord ++ tailWord_3108657) baseStart_3108657 baseEnd_3108657 := by
    simpa [prefixWord, tailWord_3108657, baseEnd_3108657] using wordTrace_append hprefix tailTrace_3108657
  have hstable : (prefixWord ++ tailWord_3108657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108657).length < 2 ^ (prefixWord ++ tailWord_3108657).sum := by decide
  have hdescent : baseEnd_3108657 < baseStart_3108657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108680 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_3108680 : Nat := 118140960795 + 3108680 * 2 ^ 59
def prefixEnd_3108680 : Nat := 4983230072969 + 3 ^ 40 * 3108680 * 2
def baseEnd_3108680 : Nat := 1596247041019002508903447

theorem tailTrace_3108680 : CollatzResearch.WordTrace tailWord_3108680 prefixEnd_3108680 1596247041019002508903447 := by
  unfold tailWord_3108680
  simp only [CollatzResearch.WordTrace]
  refine ⟨56691437188895377560193747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75588582918527170080258329 56691437188895377560193747)
  ·
    refine ⟨85037155783343066340290621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56691437188895377560193747 85037155783343066340290621)
    ·
      refine ⟨31888933418753649877608983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85037155783343066340290621 31888933418753649877608983)
      ·
        refine ⟨47833400128130474816413475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31888933418753649877608983 47833400128130474816413475)
        ·
          refine ⟨71750100192195712224620213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47833400128130474816413475 71750100192195712224620213)
          ·
            refine ⟨6726571893018348021058145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71750100192195712224620213 6726571893018348021058145)
            ·
              refine ⟨5044928919763761015793609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6726571893018348021058145 5044928919763761015793609)
              ·
                refine ⟨3783696689822820761845207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5044928919763761015793609 3783696689822820761845207)
                ·
                  refine ⟨5675545034734231142767811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783696689822820761845207 5675545034734231142767811)
                  ·
                    refine ⟨8513317552101346714151717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5675545034734231142767811 8513317552101346714151717)
                    ·
                      refine ⟨1596247041019002508903447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8513317552101346714151717 1596247041019002508903447)
                      ·
                        rfl

theorem cell23_3108680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_3108680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108680 prefixEnd_3108680 := by exact prefixLift 3108680
  have htrace : WordTrace (prefixWord ++ tailWord_3108680) baseStart_3108680 baseEnd_3108680 := by
    simpa [prefixWord, tailWord_3108680, baseEnd_3108680] using wordTrace_append hprefix tailTrace_3108680
  have hstable : (prefixWord ++ tailWord_3108680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108680).length < 2 ^ (prefixWord ++ tailWord_3108680).sum := by decide
  have hdescent : baseEnd_3108680 < baseStart_3108680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108723 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 2, 7, 2]
def baseStart_3108723 : Nat := 118140960795 + 3108723 * 2 ^ 59
def prefixEnd_3108723 : Nat := 4983230072969 + 3 ^ 40 * 3108723 * 2
def baseEnd_3108723 : Nat := 1596269120687145840665749

theorem tailTrace_3108723 : CollatzResearch.WordTrace tailWord_3108723 prefixEnd_3108723 1596269120687145840665749 := by
  unfold tailWord_3108723
  simp only [CollatzResearch.WordTrace]
  refine ⟨113384442716634973464202823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75589628477756648976135215 113384442716634973464202823)
  ·
    refine ⟨170076664074952460196304235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113384442716634973464202823 170076664074952460196304235)
    ·
      refine ⟨255114996112428690294456353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170076664074952460196304235 255114996112428690294456353)
      ·
        refine ⟨191336247084321517720842265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255114996112428690294456353 191336247084321517720842265)
        ·
          refine ⟨143502185313241138290631699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191336247084321517720842265 143502185313241138290631699)
          ·
            refine ⟨215253277969861707435947549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143502185313241138290631699 215253277969861707435947549)
            ·
              refine ⟨80719979238698140288480331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215253277969861707435947549 80719979238698140288480331)
              ·
                refine ⟨121079968858047210432720497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80719979238698140288480331 121079968858047210432720497)
                ·
                  refine ⟨90809976643535407824540373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121079968858047210432720497 90809976643535407824540373)
                  ·
                    refine ⟨2128358827582861120887665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 90809976643535407824540373 2128358827582861120887665)
                    ·
                      refine ⟨1596269120687145840665749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128358827582861120887665 1596269120687145840665749)
                      ·
                        rfl

theorem cell23_3108723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 7, 2].length) (baseStart_3108723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108723 prefixEnd_3108723 := by exact prefixLift 3108723
  have htrace : WordTrace (prefixWord ++ tailWord_3108723) baseStart_3108723 baseEnd_3108723 := by
    simpa [prefixWord, tailWord_3108723, baseEnd_3108723] using wordTrace_append hprefix tailTrace_3108723
  have hstable : (prefixWord ++ tailWord_3108723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108723).length < 2 ^ (prefixWord ++ tailWord_3108723).sum := by decide
  have hdescent : baseEnd_3108723 < baseStart_3108723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108734 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3108734 : Nat := 118140960795 + 3108734 * 2 ^ 59
def prefixEnd_3108734 : Nat := 4983230072969 + 3 ^ 40 * 3108734 * 2
def baseEnd_3108734 : Nat := 1596274768974345297628199

theorem tailTrace_3108734 : CollatzResearch.WordTrace tailWord_3108734 prefixEnd_3108734 1596274768974345297628199 := by
  unfold tailWord_3108734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14173105489949390292856657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75589895946396748228568837 14173105489949390292856657)
  ·
    refine ⟨10629829117462042719642493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14173105489949390292856657 10629829117462042719642493)
    ·
      refine ⟨3986185919048266019865935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10629829117462042719642493 3986185919048266019865935)
      ·
        refine ⟨5979278878572399029798903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3986185919048266019865935 5979278878572399029798903)
        ·
          refine ⟨8968918317858598544698355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979278878572399029798903 8968918317858598544698355)
          ·
            refine ⟨13453377476787897817047533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8968918317858598544698355 13453377476787897817047533)
            ·
              refine ⟨5045016553795461681392825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13453377476787897817047533 5045016553795461681392825)
              ·
                refine ⟨3783762415346596261044619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045016553795461681392825 3783762415346596261044619)
                ·
                  refine ⟨5675643623019894391566929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783762415346596261044619 5675643623019894391566929)
                  ·
                    refine ⟨4256732717264920793675197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675643623019894391566929 4256732717264920793675197)
                    ·
                      refine ⟨1596274768974345297628199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4256732717264920793675197 1596274768974345297628199)
                      ·
                        rfl

theorem cell23_3108734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3108734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108734 prefixEnd_3108734 := by exact prefixLift 3108734
  have htrace : WordTrace (prefixWord ++ tailWord_3108734) baseStart_3108734 baseEnd_3108734 := by
    simpa [prefixWord, tailWord_3108734, baseEnd_3108734] using wordTrace_append hprefix tailTrace_3108734
  have hstable : (prefixWord ++ tailWord_3108734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108734).length < 2 ^ (prefixWord ++ tailWord_3108734).sum := by decide
  have hdescent : baseEnd_3108734 < baseStart_3108734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108764 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3108764 : Nat := 118140960795 + 3108764 * 2 ^ 59
def prefixEnd_3108764 : Nat := 4983230072969 + 3 ^ 40 * 3108764 * 2
def baseEnd_3108764 : Nat := 1596290173393980180253061

theorem tailTrace_3108764 : CollatzResearch.WordTrace tailWord_3108764 prefixEnd_3108764 1596290173393980180253061 := by
  unfold tailWord_3108764
  simp only [CollatzResearch.WordTrace]
  refine ⟨56692969054743218733222673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75590625406324291644296897 56692969054743218733222673)
  ·
    refine ⟨42519726791057414049917005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56692969054743218733222673 42519726791057414049917005)
    ·
      refine ⟨15944897546646530268718877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42519726791057414049917005 15944897546646530268718877)
      ·
        refine ⟨5979336579992448850769579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15944897546646530268718877 5979336579992448850769579)
        ·
          refine ⟨8969004869988673276154369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979336579992448850769579 8969004869988673276154369)
          ·
            refine ⟨6726753652491504957115777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8969004869988673276154369 6726753652491504957115777)
            ·
              refine ⟨5045065239368628717836833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6726753652491504957115777 5045065239368628717836833)
              ·
                refine ⟨3783798929526471538377625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045065239368628717836833 3783798929526471538377625)
                ·
                  refine ⟨2837849197144853653783219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3783798929526471538377625 2837849197144853653783219)
                  ·
                    refine ⟨4256773795717280480674829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2837849197144853653783219 4256773795717280480674829)
                    ·
                      refine ⟨1596290173393980180253061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4256773795717280480674829 1596290173393980180253061)
                      ·
                        rfl

theorem cell23_3108764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3108764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108764 prefixEnd_3108764 := by exact prefixLift 3108764
  have htrace : WordTrace (prefixWord ++ tailWord_3108764) baseStart_3108764 baseEnd_3108764 := by
    simpa [prefixWord, tailWord_3108764, baseEnd_3108764] using wordTrace_append hprefix tailTrace_3108764
  have hstable : (prefixWord ++ tailWord_3108764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108764).length < 2 ^ (prefixWord ++ tailWord_3108764).sum := by decide
  have hdescent : baseEnd_3108764 < baseStart_3108764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108783 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_3108783 : Nat := 118140960795 + 3108783 * 2 ^ 59
def prefixEnd_3108783 : Nat := 4983230072969 + 3 ^ 40 * 3108783 * 2
def baseEnd_3108783 : Nat := 1596299929526415605915473

theorem tailTrace_3108783 : CollatzResearch.WordTrace tailWord_3108783 prefixEnd_3108783 1596299929526415605915473 := by
  unfold tailWord_3108783
  simp only [CollatzResearch.WordTrace]
  refine ⟨113386631096417603711387003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75591087397611735807591335 113386631096417603711387003)
  ·
    refine ⟨170079946644626405567080505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113386631096417603711387003 170079946644626405567080505)
    ·
      refine ⟨127559959983469804175310379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170079946644626405567080505 127559959983469804175310379)
      ·
        refine ⟨191339939975204706262965569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127559959983469804175310379 191339939975204706262965569)
        ·
          refine ⟨143504954981403529697224177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191339939975204706262965569 143504954981403529697224177)
          ·
            refine ⟨107628716236052647272918133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143504954981403529697224177 107628716236052647272918133)
            ·
              refine ⟨10090192147129935681836075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107628716236052647272918133 10090192147129935681836075)
              ·
                refine ⟨15135288220694903522754113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10090192147129935681836075 15135288220694903522754113)
                ·
                  refine ⟨11351466165521177642065585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15135288220694903522754113 11351466165521177642065585)
                  ·
                    refine ⟨8513599624140883231549189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11351466165521177642065585 8513599624140883231549189)
                    ·
                      refine ⟨1596299929526415605915473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8513599624140883231549189 1596299929526415605915473)
                      ·
                        rfl

theorem cell23_3108783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_3108783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108783 prefixEnd_3108783 := by exact prefixLift 3108783
  have htrace : WordTrace (prefixWord ++ tailWord_3108783) baseStart_3108783 baseEnd_3108783 := by
    simpa [prefixWord, tailWord_3108783, baseEnd_3108783] using wordTrace_append hprefix tailTrace_3108783
  have hstable : (prefixWord ++ tailWord_3108783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108783).length < 2 ^ (prefixWord ++ tailWord_3108783).sum := by decide
  have hdescent : baseEnd_3108783 < baseStart_3108783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108787 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 2, 2, 2]
def baseStart_3108787 : Nat := 118140960795 + 3108787 * 2 ^ 59
def prefixEnd_3108787 : Nat := 4983230072969 + 3 ^ 40 * 3108787 * 2
def baseEnd_3108787 : Nat := 1596301983449033590265455

theorem tailTrace_3108787 : CollatzResearch.WordTrace tailWord_3108787 prefixEnd_3108787 1596301983449033590265455 := by
  unfold tailWord_3108787
  simp only [CollatzResearch.WordTrace]
  refine ⟨113386776988403112394532615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75591184658935408263021743 113386776988403112394532615)
  ·
    refine ⟨170080165482604668591798923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113386776988403112394532615 170080165482604668591798923)
    ·
      refine ⟨255120248223907002887698385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170080165482604668591798923 255120248223907002887698385)
      ·
        refine ⟨191340186167930252165773789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255120248223907002887698385 191340186167930252165773789)
        ·
          refine ⟨71752569812973844562165171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191340186167930252165773789 71752569812973844562165171)
          ·
            refine ⟨107628854719460766843247757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71752569812973844562165171 107628854719460766843247757)
            ·
              refine ⟨40360820519797787566217909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107628854719460766843247757 40360820519797787566217909)
              ·
                refine ⟨3783826923731042584332929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40360820519797787566217909 3783826923731042584332929)
                ·
                  refine ⟨2837870192798281938249697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3783826923731042584332929 2837870192798281938249697)
                  ·
                    refine ⟨2128402644598711453687273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2837870192798281938249697 2128402644598711453687273)
                    ·
                      refine ⟨1596301983449033590265455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128402644598711453687273 1596301983449033590265455)
                      ·
                        rfl

theorem cell23_3108787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 2, 2].length) (baseStart_3108787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108787 prefixEnd_3108787 := by exact prefixLift 3108787
  have htrace : WordTrace (prefixWord ++ tailWord_3108787) baseStart_3108787 baseEnd_3108787 := by
    simpa [prefixWord, tailWord_3108787, baseEnd_3108787] using wordTrace_append hprefix tailTrace_3108787
  have hstable : (prefixWord ++ tailWord_3108787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108787).length < 2 ^ (prefixWord ++ tailWord_3108787).sum := by decide
  have hdescent : baseEnd_3108787 < baseStart_3108787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108793 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 7]
def baseStart_3108793 : Nat := 118140960795 + 3108793 * 2 ^ 59
def prefixEnd_3108793 : Nat := 4983230072969 + 3 ^ 40 * 3108793 * 2
def baseEnd_3108793 : Nat := 177367229370328951865603

theorem tailTrace_3108793 : CollatzResearch.WordTrace tailWord_3108793 prefixEnd_3108793 177367229370328951865603 := by
  unfold tailWord_3108793
  simp only [CollatzResearch.WordTrace]
  refine ⟨113386995826381375419251033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75591330550920916946167355 113386995826381375419251033)
  ·
    refine ⟨85040246869786031564438275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113386995826381375419251033 85040246869786031564438275)
    ·
      refine ⟨127560370304679047346657413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85040246869786031564438275 127560370304679047346657413)
      ·
        refine ⟨23917569432127321377498265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127560370304679047346657413 23917569432127321377498265)
        ·
          refine ⟨17938177074095491033123699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23917569432127321377498265 17938177074095491033123699)
          ·
            refine ⟨26907265611143236549685549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17938177074095491033123699 26907265611143236549685549)
            ·
              refine ⟨10090224604178713706132081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26907265611143236549685549 10090224604178713706132081)
              ·
                refine ⟨7567668453134035279599061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10090224604178713706132081 7567668453134035279599061)
                ·
                  refine ⟨177367229370328951865603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7567668453134035279599061 177367229370328951865603)
                  ·
                    rfl

theorem cell23_3108793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 7].length) (baseStart_3108793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108793 prefixEnd_3108793 := by exact prefixLift 3108793
  have htrace : WordTrace (prefixWord ++ tailWord_3108793) baseStart_3108793 baseEnd_3108793 := by
    simpa [prefixWord, tailWord_3108793, baseEnd_3108793] using wordTrace_append hprefix tailTrace_3108793
  have hstable : (prefixWord ++ tailWord_3108793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108793).length < 2 ^ (prefixWord ++ tailWord_3108793).sum := by decide
  have hdescent : baseEnd_3108793 < baseStart_3108793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108803 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 3]
def baseStart_3108803 : Nat := 118140960795 + 3108803 * 2 ^ 59
def prefixEnd_3108803 : Nat := 4983230072969 + 3 ^ 40 * 3108803 * 2
def baseEnd_3108803 : Nat := 1596310199139505527665381

theorem tailTrace_3108803 : CollatzResearch.WordTrace tailWord_3108803 prefixEnd_3108803 1596310199139505527665381 := by
  unfold tailWord_3108803
  simp only [CollatzResearch.WordTrace]
  refine ⟨113387360556345147127115063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75591573704230098084743375 113387360556345147127115063)
  ·
    refine ⟨170081040834517720690672595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113387360556345147127115063 170081040834517720690672595)
    ·
      refine ⟨255121561251776581036008893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170081040834517720690672595 255121561251776581036008893)
      ·
        refine ⟨95670585469416217888503335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255121561251776581036008893 95670585469416217888503335)
        ·
          refine ⟨143505878204124326832755003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95670585469416217888503335 143505878204124326832755003)
          ·
            refine ⟨215258817306186490249132505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143505878204124326832755003 215258817306186490249132505)
            ·
              refine ⟨161444112979639867686849379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215258817306186490249132505 161444112979639867686849379)
              ·
                refine ⟨242166169469459801530274069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161444112979639867686849379 242166169469459801530274069)
                ·
                  refine ⟨11351539193880928196731597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 242166169469459801530274069 11351539193880928196731597)
                  ·
                    refine ⟨4256827197705348073774349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11351539193880928196731597 4256827197705348073774349)
                    ·
                      refine ⟨1596310199139505527665381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4256827197705348073774349 1596310199139505527665381)
                      ·
                        rfl

theorem cell23_3108803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_3108803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108803 prefixEnd_3108803 := by exact prefixLift 3108803
  have htrace : WordTrace (prefixWord ++ tailWord_3108803) baseStart_3108803 baseEnd_3108803 := by
    simpa [prefixWord, tailWord_3108803, baseEnd_3108803] using wordTrace_append hprefix tailTrace_3108803
  have hstable : (prefixWord ++ tailWord_3108803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108803).length < 2 ^ (prefixWord ++ tailWord_3108803).sum := by decide
  have hdescent : baseEnd_3108803 < baseStart_3108803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108810 : List Nat := [3, 1, 2, 1, 2, 1, 3, 5, 5]
def baseStart_3108810 : Nat := 118140960795 + 3108810 * 2 ^ 59
def prefixEnd_3108810 : Nat := 4983230072969 + 3 ^ 40 * 3108810 * 2
def baseEnd_3108810 : Nat := 177368199278231888919761

theorem tailTrace_3108810 : CollatzResearch.WordTrace tailWord_3108810 prefixEnd_3108810 177368199278231888919761 := by
  unfold tailWord_3108810
  simp only [CollatzResearch.WordTrace]
  refine ⟨28346903966829946830654971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75591743911546524881746589 28346903966829946830654971)
  ·
    refine ⟨42520355950244920245982457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28346903966829946830654971 42520355950244920245982457)
    ·
      refine ⟨31890266962683690184486843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42520355950244920245982457 31890266962683690184486843)
      ·
        refine ⟨47835400444025535276730265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31890266962683690184486843 47835400444025535276730265)
        ·
          refine ⟨35876550333019151457547699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47835400444025535276730265 35876550333019151457547699)
          ·
            refine ⟨53814825499528727186321549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35876550333019151457547699 53814825499528727186321549)
            ·
              refine ⟨20180559562323272694870581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53814825499528727186321549 20180559562323272694870581)
              ·
                refine ⟨1891927458967806815144117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20180559562323272694870581 1891927458967806815144117)
                ·
                  refine ⟨177368199278231888919761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1891927458967806815144117 177368199278231888919761)
                  ·
                    rfl

theorem cell23_3108810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_3108810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108810 prefixEnd_3108810 := by exact prefixLift 3108810
  have htrace : WordTrace (prefixWord ++ tailWord_3108810) baseStart_3108810 baseEnd_3108810 := by
    simpa [prefixWord, tailWord_3108810, baseEnd_3108810] using wordTrace_append hprefix tailTrace_3108810
  have hstable : (prefixWord ++ tailWord_3108810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108810).length < 2 ^ (prefixWord ++ tailWord_3108810).sum := by decide
  have hdescent : baseEnd_3108810 < baseStart_3108810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108820 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3108820 : Nat := 118140960795 + 3108820 * 2 ^ 59
def prefixEnd_3108820 : Nat := 4983230072969 + 3 ^ 40 * 3108820 * 2
def baseEnd_3108820 : Nat := 1596318928310631961152803

theorem tailTrace_3108820 : CollatzResearch.WordTrace tailWord_3108820 prefixEnd_3108820 1596318928310631961152803 := by
  unfold tailWord_3108820
  simp only [CollatzResearch.WordTrace]
  refine ⟨56693990298641779515241957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75591987064855706020322609 56693990298641779515241957)
  ·
    refine ⟨10630123180995333659107867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56693990298641779515241957 10630123180995333659107867)
    ·
      refine ⟨15945184771493000488661801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10630123180995333659107867 15945184771493000488661801)
      ·
        refine ⟨11958888578619750366496351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15945184771493000488661801 11958888578619750366496351)
        ·
          refine ⟨17938332867929625549744527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11958888578619750366496351 17938332867929625549744527)
          ·
            refine ⟨26907499301894438324616791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17938332867929625549744527 26907499301894438324616791)
            ·
              refine ⟨40361248952841657486925187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26907499301894438324616791 40361248952841657486925187)
              ·
                refine ⟨60541873429262486230387781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40361248952841657486925187 60541873429262486230387781)
                ·
                  refine ⟨11351601267986716168197709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60541873429262486230387781 11351601267986716168197709)
                  ·
                    refine ⟨4256850475495018563074141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11351601267986716168197709 4256850475495018563074141)
                    ·
                      refine ⟨1596318928310631961152803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4256850475495018563074141 1596318928310631961152803)
                      ·
                        rfl

theorem cell23_3108820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3108820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108820 prefixEnd_3108820 := by exact prefixLift 3108820
  have htrace : WordTrace (prefixWord ++ tailWord_3108820) baseStart_3108820 baseEnd_3108820 := by
    simpa [prefixWord, tailWord_3108820, baseEnd_3108820] using wordTrace_append hprefix tailTrace_3108820
  have hstable : (prefixWord ++ tailWord_3108820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108820).length < 2 ^ (prefixWord ++ tailWord_3108820).sum := by decide
  have hdescent : baseEnd_3108820 < baseStart_3108820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108821 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_3108821 : Nat := 118140960795 + 3108821 * 2 ^ 59
def prefixEnd_3108821 : Nat := 4983230072969 + 3 ^ 40 * 3108821 * 2
def baseEnd_3108821 : Nat := 1596319441791286457240299

theorem tailTrace_3108821 : CollatzResearch.WordTrace tailWord_3108821 prefixEnd_3108821 1596319441791286457240299 := by
  unfold tailWord_3108821
  simp only [CollatzResearch.WordTrace]
  refine ⟨113388017070279936201270317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75592011380186624134180211 113388017070279936201270317)
  ·
    refine ⟨42520506401354976075476369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113388017070279936201270317 42520506401354976075476369)
    ·
      refine ⟨31890379801016232056607277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42520506401354976075476369 31890379801016232056607277)
      ·
        refine ⟨11958892425381087021227729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31890379801016232056607277 11958892425381087021227729)
        ·
          refine ⟨8969169319035815265920797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11958892425381087021227729 8969169319035815265920797)
          ·
            refine ⟨3363438494638430724720299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8969169319035815265920797 3363438494638430724720299)
            ·
              refine ⟨5045157741957646087080449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363438494638430724720299 5045157741957646087080449)
              ·
                refine ⟨3783868306468234565310337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045157741957646087080449 3783868306468234565310337)
                ·
                  refine ⟨2837901229851175923982753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3783868306468234565310337 2837901229851175923982753)
                  ·
                    refine ⟨2128425922388381942987065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2837901229851175923982753 2128425922388381942987065)
                    ·
                      refine ⟨1596319441791286457240299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2128425922388381942987065 1596319441791286457240299)
                      ·
                        rfl

theorem cell23_3108821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_3108821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108821 prefixEnd_3108821 := by exact prefixLift 3108821
  have htrace : WordTrace (prefixWord ++ tailWord_3108821) baseStart_3108821 baseEnd_3108821 := by
    simpa [prefixWord, tailWord_3108821, baseEnd_3108821] using wordTrace_append hprefix tailTrace_3108821
  have hstable : (prefixWord ++ tailWord_3108821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108821).length < 2 ^ (prefixWord ++ tailWord_3108821).sum := by decide
  have hdescent : baseEnd_3108821 < baseStart_3108821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108823 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 4, 5]
def baseStart_3108823 : Nat := 118140960795 + 3108823 * 2 ^ 59
def prefixEnd_3108823 : Nat := 4983230072969 + 3 ^ 40 * 3108823 * 2
def baseEnd_3108823 : Nat := 532106822917531816471763

theorem tailTrace_3108823 : CollatzResearch.WordTrace tailWord_3108823 prefixEnd_3108823 532106822917531816471763 := by
  unfold tailWord_3108823
  simp only [CollatzResearch.WordTrace]
  refine ⟨113388090016272690542843123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75592060010848460361895415 113388090016272690542843123)
  ·
    refine ⟨170082135024409035814264685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113388090016272690542843123 170082135024409035814264685)
    ·
      refine ⟨63780800634153388430349257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170082135024409035814264685 63780800634153388430349257)
      ·
        refine ⟨47835600475615041322761943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63780800634153388430349257 47835600475615041322761943)
        ·
          refine ⟨71753400713422561984142915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47835600475615041322761943 71753400713422561984142915)
          ·
            refine ⟨107630101070133842976214373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71753400713422561984142915 107630101070133842976214373)
            ·
              refine ⟨20180643950650095558040195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107630101070133842976214373 20180643950650095558040195)
              ·
                refine ⟨30270965925975143337060293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20180643950650095558040195 30270965925975143337060293)
                ·
                  refine ⟨5675806111120339375698805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30270965925975143337060293 5675806111120339375698805)
                  ·
                    refine ⟨532106822917531816471763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5675806111120339375698805 532106822917531816471763)
                    ·
                      rfl

theorem cell23_3108823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_3108823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108823 prefixEnd_3108823 := by exact prefixLift 3108823
  have htrace : WordTrace (prefixWord ++ tailWord_3108823) baseStart_3108823 baseEnd_3108823 := by
    simpa [prefixWord, tailWord_3108823, baseEnd_3108823] using wordTrace_append hprefix tailTrace_3108823
  have hstable : (prefixWord ++ tailWord_3108823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108823).length < 2 ^ (prefixWord ++ tailWord_3108823).sum := by decide
  have hdescent : baseEnd_3108823 < baseStart_3108823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108833 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_3108833 : Nat := 118140960795 + 3108833 * 2 ^ 59
def prefixEnd_3108833 : Nat := 4983230072969 + 3 ^ 40 * 3108833 * 2
def baseEnd_3108833 : Nat := 1596325603559140410290243

theorem tailTrace_3108833 : CollatzResearch.WordTrace tailWord_3108833 prefixEnd_3108833 1596325603559140410290243 := by
  unfold tailWord_3108833
  simp only [CollatzResearch.WordTrace]
  refine ⟨113388454746236462250707153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75592303164157641500471435 113388454746236462250707153)
  ·
    refine ⟨85041341059677346688030365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113388454746236462250707153 85041341059677346688030365)
    ·
      refine ⟨31890502897379005008011387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85041341059677346688030365 31890502897379005008011387)
      ·
        refine ⟨47835754346068507512017081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31890502897379005008011387 47835754346068507512017081)
        ·
          refine ⟨35876815759551380634012811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47835754346068507512017081 35876815759551380634012811)
          ·
            refine ⟨53815223639327070951019217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35876815759551380634012811 53815223639327070951019217)
            ·
              refine ⟨40361417729495303213264413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53815223639327070951019217 40361417729495303213264413)
              ·
                refine ⟨15135531648560738704974155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40361417729495303213264413 15135531648560738704974155)
                ·
                  refine ⟨22703297472841108057461233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15135531648560738704974155 22703297472841108057461233)
                  ·
                    refine ⟨17027473104630831043095925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22703297472841108057461233 17027473104630831043095925)
                    ·
                      refine ⟨1596325603559140410290243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17027473104630831043095925 1596325603559140410290243)
                      ·
                        rfl

theorem cell23_3108833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_3108833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108833 prefixEnd_3108833 := by exact prefixLift 3108833
  have htrace : WordTrace (prefixWord ++ tailWord_3108833) baseStart_3108833 baseEnd_3108833 := by
    simpa [prefixWord, tailWord_3108833, baseEnd_3108833] using wordTrace_append hprefix tailTrace_3108833
  have hstable : (prefixWord ++ tailWord_3108833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108833).length < 2 ^ (prefixWord ++ tailWord_3108833).sum := by decide
  have hdescent : baseEnd_3108833 < baseStart_3108833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108860 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_3108860 : Nat := 118140960795 + 3108860 * 2 ^ 59
def prefixEnd_3108860 : Nat := 4983230072969 + 3 ^ 40 * 3108860 * 2
def baseEnd_3108860 : Nat := 1596339467536811804652619

theorem tailTrace_3108860 : CollatzResearch.WordTrace tailWord_3108860 prefixEnd_3108860 1596339467536811804652619 := by
  unfold tailWord_3108860
  simp only [CollatzResearch.WordTrace]
  refine ⟨56694719758569322930970017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75592959678092430574626689 56694719758569322930970017)
  ·
    refine ⟨42521039818926992198227513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56694719758569322930970017 42521039818926992198227513)
    ·
      refine ⟨31890779864195244148670635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42521039818926992198227513 31890779864195244148670635)
      ·
        refine ⟨47836169796292866223005953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31890779864195244148670635 47836169796292866223005953)
        ·
          refine ⟨35877127347219649667254465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47836169796292866223005953 35877127347219649667254465)
          ·
            refine ⟨26907845510414737250440849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35877127347219649667254465 26907845510414737250440849)
            ·
              refine ⟨20180884132811052937830637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26907845510414737250440849 20180884132811052937830637)
              ·
                refine ⟨7567831549804144851686489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20180884132811052937830637 7567831549804144851686489)
                ·
                  refine ⟨5675873662353108638764867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7567831549804144851686489 5675873662353108638764867)
                  ·
                    refine ⟨8513810493529662958147301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5675873662353108638764867 8513810493529662958147301)
                    ·
                      refine ⟨1596339467536811804652619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8513810493529662958147301 1596339467536811804652619)
                      ·
                        rfl

theorem cell23_3108860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_3108860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108860 prefixEnd_3108860 := by exact prefixLift 3108860
  have htrace : WordTrace (prefixWord ++ tailWord_3108860) baseStart_3108860 baseEnd_3108860 := by
    simpa [prefixWord, tailWord_3108860, baseEnd_3108860] using wordTrace_append hprefix tailTrace_3108860
  have hstable : (prefixWord ++ tailWord_3108860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108860).length < 2 ^ (prefixWord ++ tailWord_3108860).sum := by decide
  have hdescent : baseEnd_3108860 < baseStart_3108860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108880 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 3]
def baseStart_3108880 : Nat := 118140960795 + 3108880 * 2 ^ 59
def prefixEnd_3108880 : Nat := 4983230072969 + 3 ^ 40 * 3108880 * 2
def baseEnd_3108880 : Nat := 1596349737149901726402527

theorem tailTrace_3108880 : CollatzResearch.WordTrace tailWord_3108880 prefixEnd_3108880 1596349737149901726402527 := by
  unfold tailWord_3108880
  simp only [CollatzResearch.WordTrace]
  refine ⟨56695084488533094638834047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75593445984710792851778729 56695084488533094638834047)
  ·
    refine ⟨85042626732799641958251071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56695084488533094638834047 85042626732799641958251071)
    ·
      refine ⟨127563940099199462937376607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85042626732799641958251071 127563940099199462937376607)
      ·
        refine ⟨191345910148799194406064911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127563940099199462937376607 191345910148799194406064911)
        ·
          refine ⟨287018865223198791609097367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191345910148799194406064911 287018865223198791609097367)
          ·
            refine ⟨430528297834798187413646051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287018865223198791609097367 430528297834798187413646051)
            ·
              refine ⟨645792446752197281120469077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430528297834798187413646051 645792446752197281120469077)
              ·
                refine ⟨7567880235377311888130497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 645792446752197281120469077 7567880235377311888130497)
                ·
                  refine ⟨5675910176532983916097873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7567880235377311888130497 5675910176532983916097873)
                  ·
                    refine ⟨4256932632399737937073405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675910176532983916097873 4256932632399737937073405)
                    ·
                      refine ⟨1596349737149901726402527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4256932632399737937073405 1596349737149901726402527)
                      ·
                        rfl

theorem cell23_3108880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_3108880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108880 prefixEnd_3108880 := by exact prefixLift 3108880
  have htrace : WordTrace (prefixWord ++ tailWord_3108880) baseStart_3108880 baseEnd_3108880 := by
    simpa [prefixWord, tailWord_3108880, baseEnd_3108880] using wordTrace_append hprefix tailTrace_3108880
  have hstable : (prefixWord ++ tailWord_3108880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108880).length < 2 ^ (prefixWord ++ tailWord_3108880).sum := by decide
  have hdescent : baseEnd_3108880 < baseStart_3108880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108883 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 8]
def baseStart_3108883 : Nat := 118140960795 + 3108883 * 2 ^ 59
def prefixEnd_3108883 : Nat := 4983230072969 + 3 ^ 40 * 3108883 * 2
def baseEnd_3108883 : Nat := 177372364176873912740557

theorem tailTrace_3108883 : CollatzResearch.WordTrace tailWord_3108883 prefixEnd_3108883 177372364176873912740557 := by
  unfold tailWord_3108883
  simp only [CollatzResearch.WordTrace]
  refine ⟨113390278396055320790027303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75593518930703547193351535 113390278396055320790027303)
  ·
    refine ⟨170085417594082981185040955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113390278396055320790027303 170085417594082981185040955)
    ·
      refine ⟨255128126391124471777561433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170085417594082981185040955 255128126391124471777561433)
      ·
        refine ⟨191346094793343353833171075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255128126391124471777561433 191346094793343353833171075)
        ·
          refine ⟨287019142190015030749756613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191346094793343353833171075 287019142190015030749756613)
          ·
            refine ⟨53816089160627818265579365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287019142190015030749756613 53816089160627818265579365)
            ·
              refine ⟨10090516717617715924796131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53816089160627818265579365 10090516717617715924796131)
              ·
                refine ⟨15135775076426573887194197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10090516717617715924796131 15135775076426573887194197)
                ·
                  refine ⟨177372364176873912740557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15135775076426573887194197 177372364176873912740557)
                  ·
                    rfl

theorem cell23_3108883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 8].length) (baseStart_3108883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3108883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3108883 prefixEnd_3108883 := by exact prefixLift 3108883
  have htrace : WordTrace (prefixWord ++ tailWord_3108883) baseStart_3108883 baseEnd_3108883 := by
    simpa [prefixWord, tailWord_3108883, baseEnd_3108883] using wordTrace_append hprefix tailTrace_3108883
  have hstable : (prefixWord ++ tailWord_3108883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108883).length < 2 ^ (prefixWord ++ tailWord_3108883).sum := by decide
  have hdescent : baseEnd_3108883 < baseStart_3108883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
