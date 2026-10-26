import V185TrunkScan23Chunk0127

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_757820 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_757820 : Nat := 118140960795 + 757820 * 2 ^ 59
def prefixEnd_757820 : Nat := 4983230072969 + 3 ^ 40 * 757820 * 2
def baseEnd_757820 : Nat := 129708636530110086488285

theorem tailTrace_757820 : CollatzResearch.WordTrace tailWord_757820 prefixEnd_757820 129708636530110086488285 := by
  unfold tailWord_757820
  simp only [CollatzResearch.WordTrace]
  refine ⟨13819983057277520098515457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18426644076370026798020609 13819983057277520098515457)
  ·
    refine ⟨10364987292958140073886593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13819983057277520098515457 10364987292958140073886593)
    ·
      refine ⟨7773740469718605055414945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10364987292958140073886593 7773740469718605055414945)
      ·
        refine ⟨5830305352288953791561209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7773740469718605055414945 5830305352288953791561209)
        ·
          refine ⟨4372729014216715343670907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5830305352288953791561209 4372729014216715343670907)
          ·
            refine ⟨6559093521325073015506361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372729014216715343670907 6559093521325073015506361)
            ·
              refine ⟨4919320140993804761629771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6559093521325073015506361 4919320140993804761629771)
              ·
                refine ⟨7378980211490707142444657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919320140993804761629771 7378980211490707142444657)
                ·
                  refine ⟨5534235158618030356833493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7378980211490707142444657 5534235158618030356833493)
                  ·
                    refine ⟨129708636530110086488285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5534235158618030356833493 129708636530110086488285)
                    ·
                      rfl

theorem cell23_757820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_757820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757820 prefixEnd_757820 := by exact prefixLift 757820
  have htrace : WordTrace (prefixWord ++ tailWord_757820) baseStart_757820 baseEnd_757820 := by
    simpa [prefixWord, tailWord_757820, baseEnd_757820] using wordTrace_append hprefix tailTrace_757820
  have hstable : (prefixWord ++ tailWord_757820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757820).length < 2 ^ (prefixWord ++ tailWord_757820).sum := by decide
  have hdescent : baseEnd_757820 < baseStart_757820 := by decide
  rcases family_descends (prefixWord ++ tailWord_757820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757880 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 7]
def baseStart_757880 : Nat := 118140960795 + 757880 * 2 ^ 59
def prefixEnd_757880 : Nat := 4983230072969 + 3 ^ 40 * 757880 * 2
def baseEnd_757880 : Nat := 43239635381066669412731

theorem tailTrace_757880 : CollatzResearch.WordTrace tailWord_757880 prefixEnd_757880 43239635381066669412731 := by
  unfold tailWord_757880
  simp only [CollatzResearch.WordTrace]
  refine ⟨13821077247168835222107547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18428102996225113629476729 13821077247168835222107547)
  ·
    refine ⟨20731615870753252833161321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13821077247168835222107547 20731615870753252833161321)
    ·
      refine ⟨15548711903064939624870991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20731615870753252833161321 15548711903064939624870991)
      ·
        refine ⟨23323067854597409437306487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15548711903064939624870991 23323067854597409437306487)
        ·
          refine ⟨34984601781896114155959731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23323067854597409437306487 34984601781896114155959731)
          ·
            refine ⟨52476902672844171233939597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34984601781896114155959731 52476902672844171233939597)
            ·
              refine ⟨19678838502316564212727349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52476902672844171233939597 19678838502316564212727349)
              ·
                refine ⟨1844891109592177894943189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19678838502316564212727349 1844891109592177894943189)
                ·
                  refine ⟨43239635381066669412731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1844891109592177894943189 43239635381066669412731)
                  ·
                    rfl

theorem cell23_757880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 7].length) (baseStart_757880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757880 prefixEnd_757880 := by exact prefixLift 757880
  have htrace : WordTrace (prefixWord ++ tailWord_757880) baseStart_757880 baseEnd_757880 := by
    simpa [prefixWord, tailWord_757880, baseEnd_757880] using wordTrace_append hprefix tailTrace_757880
  have hstable : (prefixWord ++ tailWord_757880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757880).length < 2 ^ (prefixWord ++ tailWord_757880).sum := by decide
  have hdescent : baseEnd_757880 < baseStart_757880 := by decide
  rcases family_descends (prefixWord ++ tailWord_757880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757891 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 2, 2, 2]
def baseStart_757891 : Nat := 118140960795 + 757891 * 2 ^ 59
def prefixEnd_757891 : Nat := 4983230072969 + 3 ^ 40 * 757891 * 2
def baseEnd_757891 : Nat := 389162366716799481677029

theorem tailTrace_757891 : CollatzResearch.WordTrace tailWord_757891 prefixEnd_757891 389162366716799481677029 := by
  unfold tailWord_757891
  simp only [CollatzResearch.WordTrace]
  refine ⟨27642555697297819322865527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18428370464865212881910351 27642555697297819322865527)
  ·
    refine ⟨41463833545946728984298291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27642555697297819322865527 41463833545946728984298291)
    ·
      refine ⟨62195750318920093476447437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41463833545946728984298291 62195750318920093476447437)
      ·
        refine ⟨23323406369595035053667789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62195750318920093476447437 23323406369595035053667789)
        ·
          refine ⟨8746277388598138145125421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23323406369595035053667789 8746277388598138145125421)
          ·
            refine ⟨3279854020724301804422033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8746277388598138145125421 3279854020724301804422033)
            ·
              refine ⟨2459890515543226353316525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3279854020724301804422033 2459890515543226353316525)
              ·
                refine ⟨922458943328709882493697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2459890515543226353316525 922458943328709882493697)
                ·
                  refine ⟨691844207496532411870273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 922458943328709882493697 691844207496532411870273)
                  ·
                    refine ⟨518883155622399308902705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 691844207496532411870273 518883155622399308902705)
                    ·
                      refine ⟨389162366716799481677029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518883155622399308902705 389162366716799481677029)
                      ·
                        rfl

theorem cell23_757891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_757891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757891 prefixEnd_757891 := by exact prefixLift 757891
  have htrace : WordTrace (prefixWord ++ tailWord_757891) baseStart_757891 baseEnd_757891 := by
    simpa [prefixWord, tailWord_757891, baseEnd_757891] using wordTrace_append hprefix tailTrace_757891
  have hstable : (prefixWord ++ tailWord_757891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757891).length < 2 ^ (prefixWord ++ tailWord_757891).sum := by decide
  have hdescent : baseEnd_757891 < baseStart_757891 := by decide
  rcases family_descends (prefixWord ++ tailWord_757891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757967 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 3]
def baseStart_757967 : Nat := 118140960795 + 757967 * 2 ^ 59
def prefixEnd_757967 : Nat := 4983230072969 + 3 ^ 40 * 757967 * 2
def baseEnd_757967 : Nat := 389201391246541184326679

theorem tailTrace_757967 : CollatzResearch.WordTrace tailWord_757967 prefixEnd_757967 389201391246541184326679 := by
  unfold tailWord_757967
  simp only [CollatzResearch.WordTrace]
  refine ⟨27645327645022484302632155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18430218430014989535088103 27645327645022484302632155)
  ·
    refine ⟨41467991467533726453948233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27645327645022484302632155 41467991467533726453948233)
    ·
      refine ⟨31100993600650294840461175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41467991467533726453948233 31100993600650294840461175)
      ·
        refine ⟨46651490400975442260691763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31100993600650294840461175 46651490400975442260691763)
        ·
          refine ⟨69977235601463163391037645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46651490400975442260691763 69977235601463163391037645)
          ·
            refine ⟨26241463350548686271639117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69977235601463163391037645 26241463350548686271639117)
            ·
              refine ⟨9840548756455757351864669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26241463350548686271639117 9840548756455757351864669)
              ·
                refine ⟨3690205783670909006949251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9840548756455757351864669 3690205783670909006949251)
                ·
                  refine ⟨5535308675506363510423877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690205783670909006949251 5535308675506363510423877)
                  ·
                    refine ⟨1037870376657443158204477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535308675506363510423877 1037870376657443158204477)
                    ·
                      refine ⟨389201391246541184326679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1037870376657443158204477 389201391246541184326679)
                      ·
                        rfl

theorem cell23_757967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_757967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757967 prefixEnd_757967 := by exact prefixLift 757967
  have htrace : WordTrace (prefixWord ++ tailWord_757967) baseStart_757967 baseEnd_757967 := by
    simpa [prefixWord, tailWord_757967, baseEnd_757967] using wordTrace_append hprefix tailTrace_757967
  have hstable : (prefixWord ++ tailWord_757967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757967).length < 2 ^ (prefixWord ++ tailWord_757967).sum := by decide
  have hdescent : baseEnd_757967 < baseStart_757967 := by decide
  rcases family_descends (prefixWord ++ tailWord_757967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757981 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_757981 : Nat := 118140960795 + 757981 * 2 ^ 59
def prefixEnd_757981 : Nat := 4983230072969 + 3 ^ 40 * 757981 * 2
def baseEnd_757981 : Nat := 389208579975704129551615

theorem tailTrace_757981 : CollatzResearch.WordTrace tailWord_757981 prefixEnd_757981 389208579975704129551615 := by
  unfold tailWord_757981
  simp only [CollatzResearch.WordTrace]
  refine ⟨27645838266971764693641797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18430558844647843129094531 27645838266971764693641797)
  ·
    refine ⟨5183594675057205880057837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27645838266971764693641797 5183594675057205880057837)
    ·
      refine ⟨1943848003146452205021689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5183594675057205880057837 1943848003146452205021689)
      ·
        refine ⟨1457886002359839153766267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1943848003146452205021689 1457886002359839153766267)
        ·
          refine ⟨2186829003539758730649401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457886002359839153766267 2186829003539758730649401)
          ·
            refine ⟨1640121752654819047987051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186829003539758730649401 1640121752654819047987051)
            ·
              refine ⟨2460182628982228571980577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640121752654819047987051 2460182628982228571980577)
              ·
                refine ⟨1845136971736671428985433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2460182628982228571980577 1845136971736671428985433)
                ·
                  refine ⟨1383852728802503571739075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845136971736671428985433 1383852728802503571739075)
                  ·
                    refine ⟨2075779093203755357608613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1383852728802503571739075 2075779093203755357608613)
                    ·
                      refine ⟨389208579975704129551615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2075779093203755357608613 389208579975704129551615)
                      ·
                        rfl

theorem cell23_757981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_757981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757981 prefixEnd_757981 := by exact prefixLift 757981
  have htrace : WordTrace (prefixWord ++ tailWord_757981) baseStart_757981 baseEnd_757981 := by
    simpa [prefixWord, tailWord_757981, baseEnd_757981] using wordTrace_append hprefix tailTrace_757981
  have hstable : (prefixWord ++ tailWord_757981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757981).length < 2 ^ (prefixWord ++ tailWord_757981).sum := by decide
  have hdescent : baseEnd_757981 < baseStart_757981 := by decide
  rcases family_descends (prefixWord ++ tailWord_757981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757984 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 3]
def baseStart_757984 : Nat := 118140960795 + 757984 * 2 ^ 59
def prefixEnd_757984 : Nat := 4983230072969 + 3 ^ 40 * 757984 * 2
def baseEnd_757984 : Nat := 389210120417667617814101

theorem tailTrace_757984 : CollatzResearch.WordTrace tailWord_757984 prefixEnd_757984 389210120417667617814101 := by
  unfold tailWord_757984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13822973842980448103000503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18430631790640597470667337 13822973842980448103000503)
  ·
    refine ⟨20734460764470672154500755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13822973842980448103000503 20734460764470672154500755)
    ·
      refine ⟨31101691146706008231751133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20734460764470672154500755 31101691146706008231751133)
      ·
        refine ⟨11663134180014753086906675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31101691146706008231751133 11663134180014753086906675)
        ·
          refine ⟨17494701270022129630360013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11663134180014753086906675 17494701270022129630360013)
          ·
            refine ⟨6560512976258298611385005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17494701270022129630360013 6560512976258298611385005)
            ·
              refine ⟨2460192366096861979269377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6560512976258298611385005 2460192366096861979269377)
              ·
                refine ⟨1845144274572646484452033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2460192366096861979269377 1845144274572646484452033)
                ·
                  refine ⟨1383858205929484863339025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845144274572646484452033 1383858205929484863339025)
                  ·
                    refine ⟨1037893654447113647504269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1383858205929484863339025 1037893654447113647504269)
                    ·
                      refine ⟨389210120417667617814101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1037893654447113647504269 389210120417667617814101)
                      ·
                        rfl

theorem cell23_757984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_757984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757984 prefixEnd_757984 := by exact prefixLift 757984
  have htrace : WordTrace (prefixWord ++ tailWord_757984) baseStart_757984 baseEnd_757984 := by
    simpa [prefixWord, tailWord_757984, baseEnd_757984] using wordTrace_append hprefix tailTrace_757984
  have hstable : (prefixWord ++ tailWord_757984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757984).length < 2 ^ (prefixWord ++ tailWord_757984).sum := by decide
  have hdescent : baseEnd_757984 < baseStart_757984 := by decide
  rcases family_descends (prefixWord ++ tailWord_757984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757991 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 3, 4]
def baseStart_757991 : Nat := 118140960795 + 757991 * 2 ^ 59
def prefixEnd_757991 : Nat := 4983230072969 + 3 ^ 40 * 757991 * 2
def baseEnd_757991 : Nat := 129737904927416363475523

theorem tailTrace_757991 : CollatzResearch.WordTrace tailWord_757991 prefixEnd_757991 129737904927416363475523 := by
  unfold tailWord_757991
  simp only [CollatzResearch.WordTrace]
  refine ⟨27646202996935536401505827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18430801997957024267670551 27646202996935536401505827)
  ·
    refine ⟨41469304495403304602258741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27646202996935536401505827 41469304495403304602258741)
    ·
      refine ⟨3887747296444059806461757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41469304495403304602258741 3887747296444059806461757)
      ·
        refine ⟨1457905236166522427423159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3887747296444059806461757 1457905236166522427423159)
        ·
          refine ⟨2186857854249783641134739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457905236166522427423159 2186857854249783641134739)
          ·
            refine ⟨3280286781374675461702109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186857854249783641134739 3280286781374675461702109)
            ·
              refine ⟨1230107543015503298138291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3280286781374675461702109 1230107543015503298138291)
              ·
                refine ⟨1845161314523254947207437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230107543015503298138291 1845161314523254947207437)
                ·
                  refine ⟨691935492946220605202789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1845161314523254947207437 691935492946220605202789)
                  ·
                    refine ⟨129737904927416363475523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691935492946220605202789 129737904927416363475523)
                    ·
                      rfl

theorem cell23_757991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_757991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757991 prefixEnd_757991 := by exact prefixLift 757991
  have htrace : WordTrace (prefixWord ++ tailWord_757991) baseStart_757991 baseEnd_757991 := by
    simpa [prefixWord, tailWord_757991, baseEnd_757991] using wordTrace_append hprefix tailTrace_757991
  have hstable : (prefixWord ++ tailWord_757991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757991).length < 2 ^ (prefixWord ++ tailWord_757991).sum := by decide
  have hdescent : baseEnd_757991 < baseStart_757991 := by decide
  rcases family_descends (prefixWord ++ tailWord_757991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758018 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_758018 : Nat := 118140960795 + 758018 * 2 ^ 59
def prefixEnd_758018 : Nat := 4983230072969 + 3 ^ 40 * 758018 * 2
def baseEnd_758018 : Nat := 389227578759920484788945

theorem tailTrace_758018 : CollatzResearch.WordTrace tailWord_758018 prefixEnd_758018 389227578759920484788945 := by
  unfold tailWord_758018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6911796941959430003184677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18431458511891813341825805 6911796941959430003184677)
  ·
    refine ⟨1295961926617393125597127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6911796941959430003184677 1295961926617393125597127)
    ·
      refine ⟨1943942889926089688395691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1295961926617393125597127 1943942889926089688395691)
      ·
        refine ⟨2915914334889134532593537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943942889926089688395691 2915914334889134532593537)
        ·
          refine ⟨2186935751166850899445153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2915914334889134532593537 2186935751166850899445153)
          ·
            refine ⟨1640201813375138174583865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186935751166850899445153 1640201813375138174583865)
            ·
              refine ⟨1230151360031353630937899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640201813375138174583865 1230151360031353630937899)
              ·
                refine ⟨1845227040047030446406849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230151360031353630937899 1845227040047030446406849)
                ·
                  refine ⟨1383920280035272834805137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845227040047030446406849 1383920280035272834805137)
                  ·
                    refine ⟨1037940210026454626103853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1383920280035272834805137 1037940210026454626103853)
                    ·
                      refine ⟨389227578759920484788945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1037940210026454626103853 389227578759920484788945)
                      ·
                        rfl

theorem cell23_758018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_758018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758018 prefixEnd_758018 := by exact prefixLift 758018
  have htrace : WordTrace (prefixWord ++ tailWord_758018) baseStart_758018 baseEnd_758018 := by
    simpa [prefixWord, tailWord_758018, baseEnd_758018] using wordTrace_append hprefix tailTrace_758018
  have hstable : (prefixWord ++ tailWord_758018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758018).length < 2 ^ (prefixWord ++ tailWord_758018).sum := by decide
  have hdescent : baseEnd_758018 < baseStart_758018 := by decide
  rcases family_descends (prefixWord ++ tailWord_758018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758042 : List Nat := [3, 1, 1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_758042 : Nat := 118140960795 + 758042 * 2 ^ 59
def prefixEnd_758042 : Nat := 4983230072969 + 3 ^ 40 * 758042 * 2
def baseEnd_758042 : Nat := 129746634098542796962945

theorem tailTrace_758042 : CollatzResearch.WordTrace tailWord_758042 prefixEnd_758042 129746634098542796962945 := by
  unfold tailWord_758042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6912015779937693027903095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18432042079833848074408253 6912015779937693027903095)
  ·
    refine ⟨10368023669906539541854643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6912015779937693027903095 10368023669906539541854643)
    ·
      refine ⟨15552035504859809312781965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10368023669906539541854643 15552035504859809312781965)
      ·
        refine ⟨5832013314322428492293237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15552035504859809312781965 5832013314322428492293237)
        ·
          refine ⟨546751248217727671152491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5832013314322428492293237 546751248217727671152491)
          ·
            refine ⟨820126872326591506728737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546751248217727671152491 820126872326591506728737)
            ·
              refine ⟨615095154244943630046553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820126872326591506728737 615095154244943630046553)
              ·
                refine ⟨461321365683707722534915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615095154244943630046553 461321365683707722534915)
                ·
                  refine ⟨691982048525561583802373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461321365683707722534915 691982048525561583802373)
                  ·
                    refine ⟨129746634098542796962945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691982048525561583802373 129746634098542796962945)
                    ·
                      rfl

theorem cell23_758042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_758042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758042 prefixEnd_758042 := by exact prefixLift 758042
  have htrace : WordTrace (prefixWord ++ tailWord_758042) baseStart_758042 baseEnd_758042 := by
    simpa [prefixWord, tailWord_758042, baseEnd_758042] using wordTrace_append hprefix tailTrace_758042
  have hstable : (prefixWord ++ tailWord_758042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758042).length < 2 ^ (prefixWord ++ tailWord_758042).sum := by decide
  have hdescent : baseEnd_758042 < baseStart_758042 := by decide
  rcases family_descends (prefixWord ++ tailWord_758042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758108 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_758108 : Nat := 118140960795 + 758108 * 2 ^ 59
def prefixEnd_758108 : Nat := 4983230072969 + 3 ^ 40 * 758108 * 2
def baseEnd_758108 : Nat := 389273792018825132663531

theorem tailTrace_758108 : CollatzResearch.WordTrace tailWord_758108 prefixEnd_758108 389273792018825132663531 := by
  unfold tailWord_758108
  simp only [CollatzResearch.WordTrace]
  refine ⟨13825235168755832691757489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18433646891674443589009985 13825235168755832691757489)
  ·
    refine ⟨10368926376566874518818117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13825235168755832691757489 10368926376566874518818117)
    ·
      refine ⟨1944173695606288972278397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10368926376566874518818117 1944173695606288972278397)
      ·
        refine ⟨729065135852358364604399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1944173695606288972278397 729065135852358364604399)
        ·
          refine ⟨1093597703778537546906599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729065135852358364604399 1093597703778537546906599)
          ·
            refine ⟨1640396555667806320359899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093597703778537546906599 1640396555667806320359899)
            ·
              refine ⟨2460594833501709480539849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640396555667806320359899 2460594833501709480539849)
              ·
                refine ⟨1845446125126282110404887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2460594833501709480539849 1845446125126282110404887)
                ·
                  refine ⟨2768169187689423165607331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845446125126282110404887 2768169187689423165607331)
                  ·
                    refine ⟨4152253781534134748410997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2768169187689423165607331 4152253781534134748410997)
                    ·
                      refine ⟨389273792018825132663531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4152253781534134748410997 389273792018825132663531)
                      ·
                        rfl

theorem cell23_758108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_758108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758108 prefixEnd_758108 := by exact prefixLift 758108
  have htrace : WordTrace (prefixWord ++ tailWord_758108) baseStart_758108 baseEnd_758108 := by
    simpa [prefixWord, tailWord_758108, baseEnd_758108] using wordTrace_append hprefix tailTrace_758108
  have hstable : (prefixWord ++ tailWord_758108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758108).length < 2 ^ (prefixWord ++ tailWord_758108).sum := by decide
  have hdescent : baseEnd_758108 < baseStart_758108 := by decide
  rcases family_descends (prefixWord ++ tailWord_758108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758127 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_758127 : Nat := 118140960795 + 758127 * 2 ^ 59
def prefixEnd_758127 : Nat := 4983230072969 + 3 ^ 40 * 758127 * 2
def baseEnd_758127 : Nat := 389283548151260558325943

theorem tailTrace_758127 : CollatzResearch.WordTrace tailWord_758127 prefixEnd_758127 389283548151260558325943 := by
  unfold tailWord_758127
  simp only [CollatzResearch.WordTrace]
  refine ⟨27651163324442831628456635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18434108882961887752304423 27651163324442831628456635)
  ·
    refine ⟨41476744986664247442684953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27651163324442831628456635 41476744986664247442684953)
    ·
      refine ⟨31107558739998185582013715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41476744986664247442684953 31107558739998185582013715)
      ·
        refine ⟨46661338109997278373020573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31107558739998185582013715 46661338109997278373020573)
        ·
          refine ⟨17498001791248979389882715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46661338109997278373020573 17498001791248979389882715)
          ·
            refine ⟨26247002686873469084824073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17498001791248979389882715 26247002686873469084824073)
            ·
              refine ⟨19685252015155101813618055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26247002686873469084824073 19685252015155101813618055)
              ·
                refine ⟨29527878022732652720427083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19685252015155101813618055 29527878022732652720427083)
                ·
                  refine ⟨44291817034098979080640625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29527878022732652720427083 44291817034098979080640625)
                  ·
                    refine ⟨33218862775574234310480469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44291817034098979080640625 33218862775574234310480469)
                    ·
                      refine ⟨389283548151260558325943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 33218862775574234310480469 389283548151260558325943)
                      ·
                        rfl

theorem cell23_758127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_758127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758127 prefixEnd_758127 := by exact prefixLift 758127
  have htrace : WordTrace (prefixWord ++ tailWord_758127) baseStart_758127 baseEnd_758127 := by
    simpa [prefixWord, tailWord_758127, baseEnd_758127] using wordTrace_append hprefix tailTrace_758127
  have hstable : (prefixWord ++ tailWord_758127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758127).length < 2 ^ (prefixWord ++ tailWord_758127).sum := by decide
  have hdescent : baseEnd_758127 < baseStart_758127 := by decide
  rcases family_descends (prefixWord ++ tailWord_758127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758148 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_758148 : Nat := 118140960795 + 758148 * 2 ^ 59
def prefixEnd_758148 : Nat := 4983230072969 + 3 ^ 40 * 758148 * 2
def baseEnd_758148 : Nat := 389294331245004976163347

theorem tailTrace_758148 : CollatzResearch.WordTrace tailWord_758148 prefixEnd_758148 389294331245004976163347 := by
  unfold tailWord_758148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13825964628683376107485549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18434619504911168143314065 13825964628683376107485549)
  ·
    refine ⟨5184736735756266040307081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13825964628683376107485549 5184736735756266040307081)
    ·
      refine ⟨3888552551817199530230311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5184736735756266040307081 3888552551817199530230311)
      ·
        refine ⟨5832828827725799295345467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3888552551817199530230311 5832828827725799295345467)
        ·
          refine ⟨8749243241588698943018201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832828827725799295345467 8749243241588698943018201)
          ·
            refine ⟨6561932431191524207263651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8749243241588698943018201 6561932431191524207263651)
            ·
              refine ⟨9842898646787286310895477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6561932431191524207263651 9842898646787286310895477)
              ·
                refine ⟨922771748136308091646451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9842898646787286310895477 922771748136308091646451)
                ·
                  refine ⟨1384157622204462137469677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922771748136308091646451 1384157622204462137469677)
                  ·
                    refine ⟨519059108326673301551129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384157622204462137469677 519059108326673301551129)
                    ·
                      refine ⟨389294331245004976163347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519059108326673301551129 389294331245004976163347)
                      ·
                        rfl

theorem cell23_758148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_758148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758148 prefixEnd_758148 := by exact prefixLift 758148
  have htrace : WordTrace (prefixWord ++ tailWord_758148) baseStart_758148 baseEnd_758148 := by
    simpa [prefixWord, tailWord_758148, baseEnd_758148] using wordTrace_append hprefix tailTrace_758148
  have hstable : (prefixWord ++ tailWord_758148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758148).length < 2 ^ (prefixWord ++ tailWord_758148).sum := by decide
  have hdescent : baseEnd_758148 < baseStart_758148 := by decide
  rcases family_descends (prefixWord ++ tailWord_758148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758166 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_758166 : Nat := 118140960795 + 758166 * 2 ^ 59
def prefixEnd_758166 : Nat := 4983230072969 + 3 ^ 40 * 758166 * 2
def baseEnd_758166 : Nat := 129767857965595301912755

theorem tailTrace_758166 : CollatzResearch.WordTrace tailWord_758166 prefixEnd_758166 129767857965595301912755 := by
  unfold tailWord_758166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728286610706346330570397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18435057180867694192750901 1728286610706346330570397)
  ·
    refine ⟨648107479014879873963899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1728286610706346330570397 648107479014879873963899)
    ·
      refine ⟨972161218522319810945849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 648107479014879873963899 972161218522319810945849)
      ·
        refine ⟨729120913891739858209387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 972161218522319810945849 729120913891739858209387)
        ·
          refine ⟨1093681370837609787314081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729120913891739858209387 1093681370837609787314081)
          ·
            refine ⟨820261028128207340485561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1093681370837609787314081 820261028128207340485561)
            ·
              refine ⟨615195771096155505364171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820261028128207340485561 615195771096155505364171)
              ·
                refine ⟨922793656644233258046257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615195771096155505364171 922793656644233258046257)
                ·
                  refine ⟨692095242483174943534693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 922793656644233258046257 692095242483174943534693)
                  ·
                    refine ⟨129767857965595301912755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 692095242483174943534693 129767857965595301912755)
                    ·
                      rfl

theorem cell23_758166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_758166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758166 prefixEnd_758166 := by exact prefixLift 758166
  have htrace : WordTrace (prefixWord ++ tailWord_758166) baseStart_758166 baseEnd_758166 := by
    simpa [prefixWord, tailWord_758166, baseEnd_758166] using wordTrace_append hprefix tailTrace_758166
  have hstable : (prefixWord ++ tailWord_758166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758166).length < 2 ^ (prefixWord ++ tailWord_758166).sum := by decide
  have hdescent : baseEnd_758166 < baseStart_758166 := by decide
  rcases family_descends (prefixWord ++ tailWord_758166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758178 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_758178 : Nat := 118140960795 + 758178 * 2 ^ 59
def prefixEnd_758178 : Nat := 4983230072969 + 3 ^ 40 * 758178 * 2
def baseEnd_758178 : Nat := 389309735664639858788209

theorem tailTrace_758178 : CollatzResearch.WordTrace tailWord_758178 prefixEnd_758178 389309735664639858788209 := by
  unfold tailWord_758178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6913255861814516834640797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18435348964838711559042125 6913255861814516834640797)
  ·
    refine ⟨2592470948180443812990299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6913255861814516834640797 2592470948180443812990299)
    ·
      refine ⟨3888706422270665719485449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592470948180443812990299 3888706422270665719485449)
      ·
        refine ⟨2916529816702999289614087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3888706422270665719485449 2916529816702999289614087)
        ·
          refine ⟨4374794725054498934421131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916529816702999289614087 4374794725054498934421131)
          ·
            refine ⟨6562192087581748401631697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4374794725054498934421131 6562192087581748401631697)
            ·
              refine ⟨4921644065686311301223773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6562192087581748401631697 4921644065686311301223773)
              ·
                refine ⟨1845616524632366737958915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4921644065686311301223773 1845616524632366737958915)
                ·
                  refine ⟨2768424786948550106938373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845616524632366737958915 2768424786948550106938373)
                  ·
                    refine ⟨519079647552853145050945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2768424786948550106938373 519079647552853145050945)
                    ·
                      refine ⟨389309735664639858788209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519079647552853145050945 389309735664639858788209)
                      ·
                        rfl

theorem cell23_758178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_758178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758178 prefixEnd_758178 := by exact prefixLift 758178
  have htrace : WordTrace (prefixWord ++ tailWord_758178) baseStart_758178 baseEnd_758178 := by
    simpa [prefixWord, tailWord_758178, baseEnd_758178] using wordTrace_append hprefix tailTrace_758178
  have hstable : (prefixWord ++ tailWord_758178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758178).length < 2 ^ (prefixWord ++ tailWord_758178).sum := by decide
  have hdescent : baseEnd_758178 < baseStart_758178 := by decide
  rcases family_descends (prefixWord ++ tailWord_758178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758228 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_758228 : Nat := 118140960795 + 758228 * 2 ^ 59
def prefixEnd_758228 : Nat := 4983230072969 + 3 ^ 40 * 758228 * 2
def baseEnd_758228 : Nat := 389335409697364663162979

theorem tailTrace_758228 : CollatzResearch.WordTrace tailWord_758228 prefixEnd_758228 389335409697364663162979 := by
  unfold tailWord_758228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13827423548538462938941669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18436564731384617251922225 13827423548538462938941669)
  ·
    refine ⟨2592641915350961801051563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13827423548538462938941669 2592641915350961801051563)
    ·
      refine ⟨3888962873026442701577345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592641915350961801051563 3888962873026442701577345)
      ·
        refine ⟨2916722154769832026183009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3888962873026442701577345 2916722154769832026183009)
        ·
          refine ⟨2187541616077374019637257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2916722154769832026183009 2187541616077374019637257)
          ·
            refine ⟨1640656212058030514727943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2187541616077374019637257 1640656212058030514727943)
            ·
              refine ⟨2460984318087045772091915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640656212058030514727943 2460984318087045772091915)
              ·
                refine ⟨3691476477130568658137873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460984318087045772091915 3691476477130568658137873)
                ·
                  refine ⟨2768607357847926493603405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3691476477130568658137873 2768607357847926493603405)
                  ·
                    refine ⟨1038227759192972435101277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2768607357847926493603405 1038227759192972435101277)
                    ·
                      refine ⟨389335409697364663162979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1038227759192972435101277 389335409697364663162979)
                      ·
                        rfl

theorem cell23_758228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_758228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758228 prefixEnd_758228 := by exact prefixLift 758228
  have htrace : WordTrace (prefixWord ++ tailWord_758228) baseStart_758228 baseEnd_758228 := by
    simpa [prefixWord, tailWord_758228, baseEnd_758228] using wordTrace_append hprefix tailTrace_758228
  have hstable : (prefixWord ++ tailWord_758228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758228).length < 2 ^ (prefixWord ++ tailWord_758228).sum := by decide
  have hdescent : baseEnd_758228 < baseStart_758228 := by decide
  rcases family_descends (prefixWord ++ tailWord_758228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758248 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 2, 5]
def baseStart_758248 : Nat := 118140960795 + 758248 * 2 ^ 59
def prefixEnd_758248 : Nat := 4983230072969 + 3 ^ 40 * 758248 * 2
def baseEnd_758248 : Nat := 129781893103484861637629

theorem tailTrace_758248 : CollatzResearch.WordTrace tailWord_758248 prefixEnd_758248 129781893103484861637629 := by
  unfold tailWord_758248
  simp only [CollatzResearch.WordTrace]
  refine ⟨13827788278502234646805699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18437051038002979529074265 13827788278502234646805699)
  ·
    refine ⟨20741682417753351970208549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13827788278502234646805699 20741682417753351970208549)
    ·
      refine ⟨3889065453328753494414103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20741682417753351970208549 3889065453328753494414103)
      ·
        refine ⟨5833598179993130241621155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889065453328753494414103 5833598179993130241621155)
        ·
          refine ⟨8750397269989695362431733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5833598179993130241621155 8750397269989695362431733)
          ·
            refine ⟨820349744061533940227975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8750397269989695362431733 820349744061533940227975)
            ·
              refine ⟨1230524616092300910341963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820349744061533940227975 1230524616092300910341963)
              ·
                refine ⟨1845786924138451365512945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230524616092300910341963 1845786924138451365512945)
                ·
                  refine ⟨1384340193103838524134709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845786924138451365512945 1384340193103838524134709)
                  ·
                    refine ⟨129781893103484861637629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1384340193103838524134709 129781893103484861637629)
                    ·
                      rfl

theorem cell23_758248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_758248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758248 prefixEnd_758248 := by exact prefixLift 758248
  have htrace : WordTrace (prefixWord ++ tailWord_758248) baseStart_758248 baseEnd_758248 := by
    simpa [prefixWord, tailWord_758248, baseEnd_758248] using wordTrace_append hprefix tailTrace_758248
  have hstable : (prefixWord ++ tailWord_758248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758248).length < 2 ^ (prefixWord ++ tailWord_758248).sum := by decide
  have hdescent : baseEnd_758248 < baseStart_758248 := by decide
  rcases family_descends (prefixWord ++ tailWord_758248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758251 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 1, 6, 2]
def baseStart_758251 : Nat := 118140960795 + 758251 * 2 ^ 59
def prefixEnd_758251 : Nat := 4983230072969 + 3 ^ 40 * 758251 * 2
def baseEnd_758251 : Nat := 389347219752418073175373

theorem tailTrace_758251 : CollatzResearch.WordTrace tailWord_758251 prefixEnd_758251 389347219752418073175373 := by
  unfold tailWord_758251
  simp only [CollatzResearch.WordTrace]
  refine ⟨27655685975993600805970607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18437123983995733870647071 27655685975993600805970607)
  ·
    refine ⟨41483528963990401208955911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27655685975993600805970607 41483528963990401208955911)
    ·
      refine ⟨62225293445985601813433867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41483528963990401208955911 62225293445985601813433867)
      ·
        refine ⟨93337940168978402720150801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62225293445985601813433867 93337940168978402720150801)
        ·
          refine ⟨70003455126733802040113101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93337940168978402720150801 70003455126733802040113101)
          ·
            refine ⟨26251295672525175765042413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70003455126733802040113101 26251295672525175765042413)
            ·
              refine ⟨9844235877196940911890905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26251295672525175765042413 9844235877196940911890905)
              ·
                refine ⟨7383176907897705683918179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9844235877196940911890905 7383176907897705683918179)
                ·
                  refine ⟨11074765361846558525877269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7383176907897705683918179 11074765361846558525877269)
                  ·
                    refine ⟨519129626336557430900497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11074765361846558525877269 519129626336557430900497)
                    ·
                      refine ⟨389347219752418073175373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519129626336557430900497 389347219752418073175373)
                      ·
                        rfl

theorem cell23_758251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 6, 2].length) (baseStart_758251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758251 prefixEnd_758251 := by exact prefixLift 758251
  have htrace : WordTrace (prefixWord ++ tailWord_758251) baseStart_758251 baseEnd_758251 := by
    simpa [prefixWord, tailWord_758251, baseEnd_758251] using wordTrace_append hprefix tailTrace_758251
  have hstable : (prefixWord ++ tailWord_758251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758251).length < 2 ^ (prefixWord ++ tailWord_758251).sum := by decide
  have hdescent : baseEnd_758251 < baseStart_758251 := by decide
  rcases family_descends (prefixWord ++ tailWord_758251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758264 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_758264 : Nat := 118140960795 + 758264 * 2 ^ 59
def prefixEnd_758264 : Nat := 4983230072969 + 3 ^ 40 * 758264 * 2
def baseEnd_758264 : Nat := 389353895000926522312813

theorem tailTrace_758264 : CollatzResearch.WordTrace tailWord_758264 prefixEnd_758264 389353895000926522312813 := by
  unfold tailWord_758264
  simp only [CollatzResearch.WordTrace]
  refine ⟨13828080062473252013096923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18437440083297669350795897 13828080062473252013096923)
  ·
    refine ⟨20742120093709878019645385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13828080062473252013096923 20742120093709878019645385)
    ·
      refine ⟨15556590070282408514734039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20742120093709878019645385 15556590070282408514734039)
      ·
        refine ⟨23334885105423612772101059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15556590070282408514734039 23334885105423612772101059)
        ·
          refine ⟨35002327658135419158151589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23334885105423612772101059 35002327658135419158151589)
          ·
            refine ⟨6562936435900391092153423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35002327658135419158151589 6562936435900391092153423)
            ·
              refine ⟨9844404653850586638230135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562936435900391092153423 9844404653850586638230135)
              ·
                refine ⟨14766606980775879957345203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9844404653850586638230135 14766606980775879957345203)
                ·
                  refine ⟨22149910471163819936017805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14766606980775879957345203 22149910471163819936017805)
                  ·
                    refine ⟨8306216426686432476006677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22149910471163819936017805 8306216426686432476006677)
                    ·
                      refine ⟨389353895000926522312813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8306216426686432476006677 389353895000926522312813)
                      ·
                        rfl

theorem cell23_758264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_758264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758264 prefixEnd_758264 := by exact prefixLift 758264
  have htrace : WordTrace (prefixWord ++ tailWord_758264) baseStart_758264 baseEnd_758264 := by
    simpa [prefixWord, tailWord_758264, baseEnd_758264] using wordTrace_append hprefix tailTrace_758264
  have hstable : (prefixWord ++ tailWord_758264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758264).length < 2 ^ (prefixWord ++ tailWord_758264).sum := by decide
  have hdescent : baseEnd_758264 < baseStart_758264 := by decide
  rcases family_descends (prefixWord ++ tailWord_758264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758271 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 3]
def baseStart_758271 : Nat := 118140960795 + 758271 * 2 ^ 59
def prefixEnd_758271 : Nat := 4983230072969 + 3 ^ 40 * 758271 * 2
def baseEnd_758271 : Nat := 389357489365507994925281

theorem tailTrace_758271 : CollatzResearch.WordTrace tailWord_758271 prefixEnd_758271 389357489365507994925281 := by
  unfold tailWord_758271
  simp only [CollatzResearch.WordTrace]
  refine ⟨27656415435921144221698667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18437610290614096147799111 27656415435921144221698667)
  ·
    refine ⟨41484623153881716332548001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27656415435921144221698667 41484623153881716332548001)
    ·
      refine ⟨31113467365411287249411001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41484623153881716332548001 31113467365411287249411001)
      ·
        refine ⟨23335100524058465437058251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31113467365411287249411001 23335100524058465437058251)
        ·
          refine ⟨35002650786087698155587377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23335100524058465437058251 35002650786087698155587377)
          ·
            refine ⟨26251988089565773616690533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35002650786087698155587377 26251988089565773616690533)
            ·
              refine ⟨4922247766793582553129475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26251988089565773616690533 4922247766793582553129475)
              ·
                refine ⟨7383371650190373829694213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4922247766793582553129475 7383371650190373829694213)
                ·
                  refine ⟨1384382184410695093067665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7383371650190373829694213 1384382184410695093067665)
                  ·
                    refine ⟨1038286638308021319800749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1384382184410695093067665 1038286638308021319800749)
                    ·
                      refine ⟨389357489365507994925281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1038286638308021319800749 389357489365507994925281)
                      ·
                        rfl

theorem cell23_758271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_758271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758271 prefixEnd_758271 := by exact prefixLift 758271
  have htrace : WordTrace (prefixWord ++ tailWord_758271) baseStart_758271 baseEnd_758271 := by
    simpa [prefixWord, tailWord_758271, baseEnd_758271] using wordTrace_append hprefix tailTrace_758271
  have hstable : (prefixWord ++ tailWord_758271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758271).length < 2 ^ (prefixWord ++ tailWord_758271).sum := by decide
  have hdescent : baseEnd_758271 < baseStart_758271 := by decide
  rcases family_descends (prefixWord ++ tailWord_758271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758285 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_758285 : Nat := 118140960795 + 758285 * 2 ^ 59
def prefixEnd_758285 : Nat := 4983230072969 + 3 ^ 40 * 758285 * 2
def baseEnd_758285 : Nat := 389364678094670940150217

theorem tailTrace_758285 : CollatzResearch.WordTrace tailWord_758285 prefixEnd_758285 389364678094670940150217 := by
  unfold tailWord_758285
  simp only [CollatzResearch.WordTrace]
  refine ⟨27656926057870424612708309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18437950705246949741805539 27656926057870424612708309)
  ·
    refine ⟨648209204481338076860351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27656926057870424612708309 648209204481338076860351)
    ·
      refine ⟨972313806722007115290527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 648209204481338076860351 972313806722007115290527)
      ·
        refine ⟨1458470710083010672935791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972313806722007115290527 1458470710083010672935791)
        ·
          refine ⟨2187706065124516009403687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458470710083010672935791 2187706065124516009403687)
          ·
            refine ⟨3281559097686774014105531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187706065124516009403687 3281559097686774014105531)
            ·
              refine ⟨4922338646530161021158297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281559097686774014105531 4922338646530161021158297)
              ·
                refine ⟨3691753984897620765868723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4922338646530161021158297 3691753984897620765868723)
                ·
                  refine ⟨5537630977346431148803085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3691753984897620765868723 5537630977346431148803085)
                  ·
                    refine ⟨2076611616504911680801157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5537630977346431148803085 2076611616504911680801157)
                    ·
                      refine ⟨389364678094670940150217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2076611616504911680801157 389364678094670940150217)
                      ·
                        rfl

theorem cell23_758285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_758285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758285 prefixEnd_758285 := by exact prefixLift 758285
  have htrace : WordTrace (prefixWord ++ tailWord_758285) baseStart_758285 baseEnd_758285 := by
    simpa [prefixWord, tailWord_758285, baseEnd_758285] using wordTrace_append hprefix tailTrace_758285
  have hstable : (prefixWord ++ tailWord_758285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758285).length < 2 ^ (prefixWord ++ tailWord_758285).sum := by decide
  have hdescent : baseEnd_758285 < baseStart_758285 := by decide
  rcases family_descends (prefixWord ++ tailWord_758285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758312 : List Nat := [2, 1, 5, 2, 1, 1, 3, 3, 1, 4]
def baseStart_758312 : Nat := 118140960795 + 758312 * 2 ^ 59
def prefixEnd_758312 : Nat := 4983230072969 + 3 ^ 40 * 758312 * 2
def baseEnd_758312 : Nat := 129792847357447444837531

theorem tailTrace_758312 : CollatzResearch.WordTrace tailWord_758312 prefixEnd_758312 129792847357447444837531 := by
  unfold tailWord_758312
  simp only [CollatzResearch.WordTrace]
  refine ⟨13828955414386304111970595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18438607219181738815960793 13828955414386304111970595)
  ·
    refine ⟨20743433121579456167955893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13828955414386304111970595 20743433121579456167955893)
    ·
      refine ⟨1944696855148074015745865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20743433121579456167955893 1944696855148074015745865)
      ·
        refine ⟨1458522641361055511809399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1944696855148074015745865 1458522641361055511809399)
        ·
          refine ⟨2187783962041583267714099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458522641361055511809399 2187783962041583267714099)
          ·
            refine ⟨3281675943062374901571149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187783962041583267714099 3281675943062374901571149)
            ·
              refine ⟨1230628478648390588089181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3281675943062374901571149 1230628478648390588089181)
              ·
                refine ⟨461485679493146470533443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1230628478648390588089181 461485679493146470533443)
                ·
                  refine ⟨692228519239719705800165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461485679493146470533443 692228519239719705800165)
                  ·
                    refine ⟨129792847357447444837531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 692228519239719705800165 129792847357447444837531)
                    ·
                      rfl

theorem cell23_758312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_758312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758312 prefixEnd_758312 := by exact prefixLift 758312
  have htrace : WordTrace (prefixWord ++ tailWord_758312) baseStart_758312 baseEnd_758312 := by
    simpa [prefixWord, tailWord_758312, baseEnd_758312] using wordTrace_append hprefix tailTrace_758312
  have hstable : (prefixWord ++ tailWord_758312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758312).length < 2 ^ (prefixWord ++ tailWord_758312).sum := by decide
  have hdescent : baseEnd_758312 < baseStart_758312 := by decide
  rcases family_descends (prefixWord ++ tailWord_758312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758342 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_758342 : Nat := 118140960795 + 758342 * 2 ^ 59
def prefixEnd_758342 : Nat := 4983230072969 + 3 ^ 40 * 758342 * 2
def baseEnd_758342 : Nat := 43265994054664135237495

theorem tailTrace_758342 : CollatzResearch.WordTrace tailWord_758342 prefixEnd_758342 43265994054664135237495 := by
  unfold tailWord_758342
  simp only [CollatzResearch.WordTrace]
  refine ⟨864343906833247604610415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18439336679109282231688853 864343906833247604610415)
  ·
    refine ⟨1296515860249871406915623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 864343906833247604610415 1296515860249871406915623)
    ·
      refine ⟨1944773790374807110373435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1296515860249871406915623 1944773790374807110373435)
      ·
        refine ⟨2917160685562210665560153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1944773790374807110373435 2917160685562210665560153)
        ·
          refine ⟨2187870514171657999170115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2917160685562210665560153 2187870514171657999170115)
          ·
            refine ⟨3281805771257486998755173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187870514171657999170115 3281805771257486998755173)
            ·
              refine ⟨615338582110778812266595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3281805771257486998755173 615338582110778812266595)
              ·
                refine ⟨923007873166168218399893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615338582110778812266595 923007873166168218399893)
                ·
                  refine ⟨43265994054664135237495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 923007873166168218399893 43265994054664135237495)
                  ·
                    rfl

theorem cell23_758342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_758342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758342 prefixEnd_758342 := by exact prefixLift 758342
  have htrace : WordTrace (prefixWord ++ tailWord_758342) baseStart_758342 baseEnd_758342 := by
    simpa [prefixWord, tailWord_758342, baseEnd_758342] using wordTrace_append hprefix tailTrace_758342
  have hstable : (prefixWord ++ tailWord_758342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758342).length < 2 ^ (prefixWord ++ tailWord_758342).sum := by decide
  have hdescent : baseEnd_758342 < baseStart_758342 := by decide
  rcases family_descends (prefixWord ++ tailWord_758342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758381 : List Nat := [1, 5, 1, 1, 3, 12]
def baseStart_758381 : Nat := 118140960795 + 758381 * 2 ^ 59
def prefixEnd_758381 : Nat := 4983230072969 + 3 ^ 40 * 758381 * 2
def baseEnd_758381 : Nat := 1602526634722232775925

theorem tailTrace_758381 : CollatzResearch.WordTrace tailWord_758381 prefixEnd_758381 1602526634722232775925 := by
  unfold tailWord_758381
  simp only [CollatzResearch.WordTrace]
  refine ⟨27660427465522633008202997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18440284977015088672135331 27660427465522633008202997)
  ·
    refine ⟨2593165074892746844519031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27660427465522633008202997 2593165074892746844519031)
    ·
      refine ⟨3889747612339120266778547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2593165074892746844519031 3889747612339120266778547)
      ·
        refine ⟨5834621418508680400167821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889747612339120266778547 5834621418508680400167821)
        ·
          refine ⟨2187983031940755150062933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5834621418508680400167821 2187983031940755150062933)
          ·
            refine ⟨1602526634722232775925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2187983031940755150062933 1602526634722232775925)
            ·
              rfl

theorem cell23_758381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 12].length) (baseStart_758381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758381 prefixEnd_758381 := by exact prefixLift 758381
  have htrace : WordTrace (prefixWord ++ tailWord_758381) baseStart_758381 baseEnd_758381 := by
    simpa [prefixWord, tailWord_758381, baseEnd_758381] using wordTrace_append hprefix tailTrace_758381
  have hstable : (prefixWord ++ tailWord_758381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758381).length < 2 ^ (prefixWord ++ tailWord_758381).sum := by decide
  have hdescent : baseEnd_758381 < baseStart_758381 := by decide
  rcases family_descends (prefixWord ++ tailWord_758381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758386 : List Nat := [3, 2, 1, 2, 4, 2, 2, 2, 1, 1, 3]
def baseStart_758386 : Nat := 118140960795 + 758386 * 2 ^ 59
def prefixEnd_758386 : Nat := 4983230072969 + 3 ^ 40 * 758386 * 2
def baseEnd_758386 : Nat := 389416539640775044987253

theorem tailTrace_758386 : CollatzResearch.WordTrace tailWord_758386 prefixEnd_758386 389416539640775044987253 := by
  unfold tailWord_758386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915152457626129715533753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18440406553669679241423341 6915152457626129715533753)
  ·
    refine ⟨5186364343219597286650315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6915152457626129715533753 5186364343219597286650315)
    ·
      refine ⟨7779546514829395929975473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5186364343219597286650315 7779546514829395929975473)
      ·
        refine ⟨5834659886122046947481605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7779546514829395929975473 5834659886122046947481605)
        ·
          refine ⟨1093998728647883802652801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5834659886122046947481605 1093998728647883802652801)
          ·
            refine ⟨820499046485912851989601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1093998728647883802652801 820499046485912851989601)
            ·
              refine ⟨615374284864434638992201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820499046485912851989601 615374284864434638992201)
              ·
                refine ⟨461530713648325979244151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615374284864434638992201 461530713648325979244151)
                ·
                  refine ⟨692296070472488968866227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461530713648325979244151 692296070472488968866227)
                  ·
                    refine ⟨1038444105708733453299341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 692296070472488968866227 1038444105708733453299341)
                    ·
                      refine ⟨389416539640775044987253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1038444105708733453299341 389416539640775044987253)
                      ·
                        rfl

theorem cell23_758386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_758386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758386 prefixEnd_758386 := by exact prefixLift 758386
  have htrace : WordTrace (prefixWord ++ tailWord_758386) baseStart_758386 baseEnd_758386 := by
    simpa [prefixWord, tailWord_758386, baseEnd_758386] using wordTrace_append hprefix tailTrace_758386
  have hstable : (prefixWord ++ tailWord_758386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758386).length < 2 ^ (prefixWord ++ tailWord_758386).sum := by decide
  have hdescent : baseEnd_758386 < baseStart_758386 := by decide
  rcases family_descends (prefixWord ++ tailWord_758386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758392 : List Nat := [2, 1, 2, 1, 1, 1, 2, 8, 1, 2, 2]
def baseStart_758392 : Nat := 118140960795 + 758392 * 2 ^ 59
def prefixEnd_758392 : Nat := 4983230072969 + 3 ^ 40 * 758392 * 2
def baseEnd_758392 : Nat := 389419620524702021512225

theorem tailTrace_758392 : CollatzResearch.WordTrace tailWord_758392 prefixEnd_758392 389419620524702021512225 := by
  unfold tailWord_758392
  simp only [CollatzResearch.WordTrace]
  refine ⟨13830414334241390943426715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18440552445655187924568953 13830414334241390943426715)
  ·
    refine ⟨20745621501362086415140073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13830414334241390943426715 20745621501362086415140073)
    ·
      refine ⟨15559216126021564811355055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20745621501362086415140073 15559216126021564811355055)
      ·
        refine ⟨23338824189032347217032583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15559216126021564811355055 23338824189032347217032583)
        ·
          refine ⟨35008236283548520825548875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23338824189032347217032583 35008236283548520825548875)
          ·
            refine ⟨52512354425322781238323313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35008236283548520825548875 52512354425322781238323313)
            ·
              refine ⟨39384265818992085928742485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52512354425322781238323313 39384265818992085928742485)
              ·
                refine ⟨461534365066313506977451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 39384265818992085928742485 461534365066313506977451)
                ·
                  refine ⟨692301547599470260466177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461534365066313506977451 692301547599470260466177)
                  ·
                    refine ⟨519226160699602695349633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 692301547599470260466177 519226160699602695349633)
                    ·
                      refine ⟨389419620524702021512225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519226160699602695349633 389419620524702021512225)
                      ·
                        rfl

theorem cell23_758392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 2, 2].length) (baseStart_758392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758392 prefixEnd_758392 := by exact prefixLift 758392
  have htrace : WordTrace (prefixWord ++ tailWord_758392) baseStart_758392 baseEnd_758392 := by
    simpa [prefixWord, tailWord_758392, baseEnd_758392] using wordTrace_append hprefix tailTrace_758392
  have hstable : (prefixWord ++ tailWord_758392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758392).length < 2 ^ (prefixWord ++ tailWord_758392).sum := by decide
  have hdescent : baseEnd_758392 < baseStart_758392 := by decide
  rcases family_descends (prefixWord ++ tailWord_758392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758426 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4]
def baseStart_758426 : Nat := 118140960795 + 758426 * 2 ^ 59
def prefixEnd_758426 : Nat := 4983230072969 + 3 ^ 40 * 758426 * 2
def baseEnd_758426 : Nat := 389437078866954888487069

theorem tailTrace_758426 : CollatzResearch.WordTrace tailWord_758426 prefixEnd_758426 389437078866954888487069 := by
  unfold tailWord_758426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915517187589901423397783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18441379166906403795727421 6915517187589901423397783)
  ·
    refine ⟨10373275781384852135096675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6915517187589901423397783 10373275781384852135096675)
    ·
      refine ⟨15559913672077278202645013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10373275781384852135096675 15559913672077278202645013)
      ·
        refine ⟨729370953378622415748985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15559913672077278202645013 729370953378622415748985)
        ·
          refine ⟨547028215033966811811739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729370953378622415748985 547028215033966811811739)
          ·
            refine ⟨820542322550950217717609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547028215033966811811739 820542322550950217717609)
            ·
              refine ⟨615406741913212663288207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820542322550950217717609 615406741913212663288207)
              ·
                refine ⟨923110112869818994932311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615406741913212663288207 923110112869818994932311)
                ·
                  refine ⟨1384665169304728492398467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923110112869818994932311 1384665169304728492398467)
                  ·
                    refine ⟨2076997753957092738597701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384665169304728492398467 2076997753957092738597701)
                    ·
                      refine ⟨389437078866954888487069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2076997753957092738597701 389437078866954888487069)
                      ·
                        rfl

theorem cell23_758426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_758426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758426 prefixEnd_758426 := by exact prefixLift 758426
  have htrace : WordTrace (prefixWord ++ tailWord_758426) baseStart_758426 baseEnd_758426 := by
    simpa [prefixWord, tailWord_758426, baseEnd_758426] using wordTrace_append hprefix tailTrace_758426
  have hstable : (prefixWord ++ tailWord_758426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758426).length < 2 ^ (prefixWord ++ tailWord_758426).sum := by decide
  have hdescent : baseEnd_758426 < baseStart_758426 := by decide
  rcases family_descends (prefixWord ++ tailWord_758426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758441 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 2, 6]
def baseStart_758441 : Nat := 118140960795 + 758441 * 2 ^ 59
def prefixEnd_758441 : Nat := 4983230072969 + 3 ^ 40 * 758441 * 2
def baseEnd_758441 : Nat := 129814927025590776599833

theorem tailTrace_758441 : CollatzResearch.WordTrace tailWord_758441 prefixEnd_758441 129814927025590776599833 := by
  unfold tailWord_758441
  simp only [CollatzResearch.WordTrace]
  refine ⟨27662615845305263255387177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18441743896870175503591451 27662615845305263255387177)
  ·
    refine ⟨20746961883978947441540383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27662615845305263255387177 20746961883978947441540383)
    ·
      refine ⟨31120442825968421162310575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20746961883978947441540383 31120442825968421162310575)
      ·
        refine ⟨46680664238952631743465863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31120442825968421162310575 46680664238952631743465863)
        ·
          refine ⟨70020996358428947615198795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46680664238952631743465863 70020996358428947615198795)
          ·
            refine ⟨105031494537643421422798193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70020996358428947615198795 105031494537643421422798193)
            ·
              refine ⟨78773620903232566067098645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105031494537643421422798193 78773620903232566067098645)
              ·
                refine ⟨3692513479839026534395249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78773620903232566067098645 3692513479839026534395249)
                ·
                  refine ⟨2769385109879269900796437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3692513479839026534395249 2769385109879269900796437)
                  ·
                    refine ⟨129814927025590776599833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2769385109879269900796437 129814927025590776599833)
                    ·
                      rfl

theorem cell23_758441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_758441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758441 prefixEnd_758441 := by exact prefixLift 758441
  have htrace : WordTrace (prefixWord ++ tailWord_758441) baseStart_758441 baseEnd_758441 := by
    simpa [prefixWord, tailWord_758441, baseEnd_758441] using wordTrace_append hprefix tailTrace_758441
  have hstable : (prefixWord ++ tailWord_758441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758441).length < 2 ^ (prefixWord ++ tailWord_758441).sum := by decide
  have hdescent : baseEnd_758441 < baseStart_758441 := by decide
  rcases family_descends (prefixWord ++ tailWord_758441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758471 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 9]
def baseStart_758471 : Nat := 118140960795 + 758471 * 2 ^ 59
def prefixEnd_758471 : Nat := 4983230072969 + 3 ^ 40 * 758471 * 2
def baseEnd_758471 : Nat := 43273353944045245824929

theorem tailTrace_758471 : CollatzResearch.WordTrace tailWord_758471 prefixEnd_758471 43273353944045245824929 := by
  unfold tailWord_758471
  simp only [CollatzResearch.WordTrace]
  refine ⟨27663710035196578378979267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18442473356797718919319511 27663710035196578378979267)
  ·
    refine ⟨41495565052794867568468901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27663710035196578378979267 41495565052794867568468901)
    ·
      refine ⟨7780418447399037669087919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41495565052794867568468901 7780418447399037669087919)
      ·
        refine ⟨11670627671098556503631879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7780418447399037669087919 11670627671098556503631879)
        ·
          refine ⟨17505941506647834755447819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11670627671098556503631879 17505941506647834755447819)
          ·
            refine ⟨26258912259971752133171729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17505941506647834755447819 26258912259971752133171729)
            ·
              refine ⟨19694184194978814099878797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26258912259971752133171729 19694184194978814099878797)
              ·
                refine ⟨7385319073117055287454549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19694184194978814099878797 7385319073117055287454549)
                ·
                  refine ⟨43273353944045245824929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7385319073117055287454549 43273353944045245824929)
                  ·
                    rfl

theorem cell23_758471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 9].length) (baseStart_758471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758471 prefixEnd_758471 := by exact prefixLift 758471
  have htrace : WordTrace (prefixWord ++ tailWord_758471) baseStart_758471 baseEnd_758471 := by
    simpa [prefixWord, tailWord_758471, baseEnd_758471] using wordTrace_append hprefix tailTrace_758471
  have hstable : (prefixWord ++ tailWord_758471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758471).length < 2 ^ (prefixWord ++ tailWord_758471).sum := by decide
  have hdescent : baseEnd_758471 < baseStart_758471 := by decide
  rcases family_descends (prefixWord ++ tailWord_758471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758535 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 2, 5]
def baseStart_758535 : Nat := 118140960795 + 758535 * 2 ^ 59
def prefixEnd_758535 : Nat := 4983230072969 + 3 ^ 40 * 758535 * 2
def baseEnd_758535 : Nat := 129831016086098320674689

theorem tailTrace_758535 : CollatzResearch.WordTrace tailWord_758535 prefixEnd_758535 129831016086098320674689 := by
  unfold tailWord_758535
  simp only [CollatzResearch.WordTrace]
  refine ⟨27666044306964717309309059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18444029537976478206206039 27666044306964717309309059)
  ·
    refine ⟨41499066460447075963963589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27666044306964717309309059 41499066460447075963963589)
    ·
      refine ⟨7781074961333826743243173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41499066460447075963963589 7781074961333826743243173)
      ·
        refine ⟨1458951555250092514358095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7781074961333826743243173 1458951555250092514358095)
        ·
          refine ⟨2188427332875138771537143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458951555250092514358095 2188427332875138771537143)
          ·
            refine ⟨3282640999312708157305715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188427332875138771537143 3282640999312708157305715)
            ·
              refine ⟨4923961498969062235958573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282640999312708157305715 4923961498969062235958573)
              ·
                refine ⟨1846485562113398338484465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4923961498969062235958573 1846485562113398338484465)
                ·
                  refine ⟨1384864171585048753863349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1846485562113398338484465 1384864171585048753863349)
                  ·
                    refine ⟨129831016086098320674689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1384864171585048753863349 129831016086098320674689)
                    ·
                      rfl

theorem cell23_758535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_758535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758535 prefixEnd_758535 := by exact prefixLift 758535
  have htrace : WordTrace (prefixWord ++ tailWord_758535) baseStart_758535 baseEnd_758535 := by
    simpa [prefixWord, tailWord_758535, baseEnd_758535] using wordTrace_append hprefix tailTrace_758535
  have hstable : (prefixWord ++ tailWord_758535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758535).length < 2 ^ (prefixWord ++ tailWord_758535).sum := by decide
  have hdescent : baseEnd_758535 < baseStart_758535 := by decide
  rcases family_descends (prefixWord ++ tailWord_758535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758565 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_758565 : Nat := 118140960795 + 758565 * 2 ^ 59
def prefixEnd_758565 : Nat := 4983230072969 + 3 ^ 40 * 758565 * 2
def baseEnd_758565 : Nat := 129836150892643281549643

theorem tailTrace_758565 : CollatzResearch.WordTrace tailWord_758565 prefixEnd_758565 129836150892643281549643 := by
  unfold tailWord_758565
  simp only [CollatzResearch.WordTrace]
  refine ⟨27667138496856032432901149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18444758997904021621934099 27667138496856032432901149)
  ·
    refine ⟨10375176936321012162337931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27667138496856032432901149 10375176936321012162337931)
    ·
      refine ⟨15562765404481518243506897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10375176936321012162337931 15562765404481518243506897)
      ·
        refine ⟨11672074053361138682630173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15562765404481518243506897 11672074053361138682630173)
        ·
          refine ⟨4377027770010427005986315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11672074053361138682630173 4377027770010427005986315)
          ·
            refine ⟨6565541655015640508979473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377027770010427005986315 6565541655015640508979473)
            ·
              refine ⟨4924156241261730381734605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6565541655015640508979473 4924156241261730381734605)
              ·
                refine ⟨1846558590473148893150477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4924156241261730381734605 1846558590473148893150477)
                ·
                  refine ⟨692459471427430834931429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1846558590473148893150477 692459471427430834931429)
                  ·
                    refine ⟨129836150892643281549643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 692459471427430834931429 129836150892643281549643)
                    ·
                      rfl

theorem cell23_758565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_758565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758565 prefixEnd_758565 := by exact prefixLift 758565
  have htrace : WordTrace (prefixWord ++ tailWord_758565) baseStart_758565 baseEnd_758565 := by
    simpa [prefixWord, tailWord_758565, baseEnd_758565] using wordTrace_append hprefix tailTrace_758565
  have hstable : (prefixWord ++ tailWord_758565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758565).length < 2 ^ (prefixWord ++ tailWord_758565).sum := by decide
  have hdescent : baseEnd_758565 < baseStart_758565 := by decide
  rcases family_descends (prefixWord ++ tailWord_758565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758589 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_758589 : Nat := 118140960795 + 758589 * 2 ^ 59
def prefixEnd_758589 : Nat := 4983230072969 + 3 ^ 40 * 758589 * 2
def baseEnd_758589 : Nat := 389520776213637750748819

theorem tailTrace_758589 : CollatzResearch.WordTrace tailWord_758589 prefixEnd_758589 389520776213637750748819 := by
  unfold tailWord_758589
  simp only [CollatzResearch.WordTrace]
  refine ⟨27668013848769084531774821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18445342565846056354516547 27668013848769084531774821)
  ·
    refine ⟨5187752596644203349707779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27668013848769084531774821 5187752596644203349707779)
    ·
      refine ⟨7781628894966305024561669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5187752596644203349707779 7781628894966305024561669)
      ·
        refine ⟨1459055417806182192105313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7781628894966305024561669 1459055417806182192105313)
        ·
          refine ⟨1094291563354636644078985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1459055417806182192105313 1094291563354636644078985)
          ·
            refine ⟨820718672515977483059239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1094291563354636644078985 820718672515977483059239)
            ·
              refine ⟨1231078008773966224588859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820718672515977483059239 1231078008773966224588859)
              ·
                refine ⟨1846617013160949336883289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231078008773966224588859 1846617013160949336883289)
                ·
                  refine ⟨1384962759870712002662467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1846617013160949336883289 1384962759870712002662467)
                  ·
                    refine ⟨2077444139806068003993701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384962759870712002662467 2077444139806068003993701)
                    ·
                      refine ⟨389520776213637750748819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2077444139806068003993701 389520776213637750748819)
                      ·
                        rfl

theorem cell23_758589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_758589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758589 prefixEnd_758589 := by exact prefixLift 758589
  have htrace : WordTrace (prefixWord ++ tailWord_758589) baseStart_758589 baseEnd_758589 := by
    simpa [prefixWord, tailWord_758589, baseEnd_758589] using wordTrace_append hprefix tailTrace_758589
  have hstable : (prefixWord ++ tailWord_758589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758589).length < 2 ^ (prefixWord ++ tailWord_758589).sum := by decide
  have hdescent : baseEnd_758589 < baseStart_758589 := by decide
  rcases family_descends (prefixWord ++ tailWord_758589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758632 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_758632 : Nat := 118140960795 + 758632 * 2 ^ 59
def prefixEnd_758632 : Nat := 4983230072969 + 3 ^ 40 * 758632 * 2
def baseEnd_758632 : Nat := 389542855881781082511121

theorem tailTrace_758632 : CollatzResearch.WordTrace tailWord_758632 prefixEnd_758632 389542855881781082511121 := by
  unfold tailWord_758632
  simp only [CollatzResearch.WordTrace]
  refine ⟨13834791093806651437795075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18446388125075535250393433 13834791093806651437795075)
  ·
    refine ⟨20752186640709977156692613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13834791093806651437795075 20752186640709977156692613)
    ·
      refine ⟨3891034995133120716879865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20752186640709977156692613 3891034995133120716879865)
      ·
        refine ⟨2918276246349840537659899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3891034995133120716879865 2918276246349840537659899)
        ·
          refine ⟨4377414369524760806489849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918276246349840537659899 4377414369524760806489849)
          ·
            refine ⟨3283060777143570604867387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4377414369524760806489849 3283060777143570604867387)
            ·
              refine ⟨4924591165715355907301081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283060777143570604867387 4924591165715355907301081)
              ·
                refine ⟨3693443374286516930475811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4924591165715355907301081 3693443374286516930475811)
                ·
                  refine ⟨5540165061429775395713717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693443374286516930475811 5540165061429775395713717)
                  ·
                    refine ⟨519390474509041443348161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5540165061429775395713717 519390474509041443348161)
                    ·
                      refine ⟨389542855881781082511121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519390474509041443348161 389542855881781082511121)
                      ·
                        rfl

theorem cell23_758632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_758632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758632 prefixEnd_758632 := by exact prefixLift 758632
  have htrace : WordTrace (prefixWord ++ tailWord_758632) baseStart_758632 baseEnd_758632 := by
    simpa [prefixWord, tailWord_758632, baseEnd_758632] using wordTrace_append hprefix tailTrace_758632
  have hstable : (prefixWord ++ tailWord_758632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758632).length < 2 ^ (prefixWord ++ tailWord_758632).sum := by decide
  have hdescent : baseEnd_758632 < baseStart_758632 := by decide
  rcases family_descends (prefixWord ++ tailWord_758632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758655 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 4, 4]
def baseStart_758655 : Nat := 118140960795 + 758655 * 2 ^ 59
def prefixEnd_758655 : Nat := 4983230072969 + 3 ^ 40 * 758655 * 2
def baseEnd_758655 : Nat := 129851555312278164174505

theorem tailTrace_758655 : CollatzResearch.WordTrace tailWord_758655 prefixEnd_758655 129851555312278164174505 := by
  unfold tailWord_758655
  simp only [CollatzResearch.WordTrace]
  refine ⟨27670421066529977803677419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18446947377686651869118279 27670421066529977803677419)
  ·
    refine ⟨41505631599794966705516129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27670421066529977803677419 41505631599794966705516129)
    ·
      refine ⟨31129223699846225029137097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41505631599794966705516129 31129223699846225029137097)
      ·
        refine ⟨23346917774884668771852823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31129223699846225029137097 23346917774884668771852823)
        ·
          refine ⟨35020376662327003157779235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23346917774884668771852823 35020376662327003157779235)
          ·
            refine ⟨52530564993490504736668853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35020376662327003157779235 52530564993490504736668853)
            ·
              refine ⟨4924740468139734819062705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52530564993490504736668853 4924740468139734819062705)
              ·
                refine ⟨3693555351104801114297029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4924740468139734819062705 3693555351104801114297029)
                ·
                  refine ⟨692541628332150208930693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3693555351104801114297029 692541628332150208930693)
                  ·
                    refine ⟨129851555312278164174505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 692541628332150208930693 129851555312278164174505)
                    ·
                      rfl

theorem cell23_758655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 4].length) (baseStart_758655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758655 prefixEnd_758655 := by exact prefixLift 758655
  have htrace : WordTrace (prefixWord ++ tailWord_758655) baseStart_758655 baseEnd_758655 := by
    simpa [prefixWord, tailWord_758655, baseEnd_758655] using wordTrace_append hprefix tailTrace_758655
  have hstable : (prefixWord ++ tailWord_758655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758655).length < 2 ^ (prefixWord ++ tailWord_758655).sum := by decide
  have hdescent : baseEnd_758655 < baseStart_758655 := by decide
  rcases family_descends (prefixWord ++ tailWord_758655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758665 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_758665 : Nat := 118140960795 + 758665 * 2 ^ 59
def prefixEnd_758665 : Nat := 4983230072969 + 3 ^ 40 * 758665 * 2
def baseEnd_758665 : Nat := 389559800743379453398469

theorem tailTrace_758665 : CollatzResearch.WordTrace tailWord_758665 prefixEnd_758665 389559800743379453398469 := by
  unfold tailWord_758665
  simp only [CollatzResearch.WordTrace]
  refine ⟨27670785796493749511541449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18447190530995833007694299 27670785796493749511541449)
  ·
    refine ⟨20753089347370312133656087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27670785796493749511541449 20753089347370312133656087)
    ·
      refine ⟨31129634021055468200484131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20753089347370312133656087 31129634021055468200484131)
      ·
        refine ⟨46694451031583202300726197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31129634021055468200484131 46694451031583202300726197)
        ·
          refine ⟨4377604784210925215693081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46694451031583202300726197 4377604784210925215693081)
          ·
            refine ⟨3283203588158193911769811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4377604784210925215693081 3283203588158193911769811)
            ·
              refine ⟨4924805382237290867654717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283203588158193911769811 4924805382237290867654717)
              ·
                refine ⟨1846802018338984075370519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4924805382237290867654717 1846802018338984075370519)
                ·
                  refine ⟨2770203027508476113055779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846802018338984075370519 2770203027508476113055779)
                  ·
                    refine ⟨4155304541262714169583669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2770203027508476113055779 4155304541262714169583669)
                    ·
                      refine ⟨389559800743379453398469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4155304541262714169583669 389559800743379453398469)
                      ·
                        rfl

theorem cell23_758665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_758665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758665 prefixEnd_758665 := by exact prefixLift 758665
  have htrace : WordTrace (prefixWord ++ tailWord_758665) baseStart_758665 baseEnd_758665 := by
    simpa [prefixWord, tailWord_758665, baseEnd_758665] using wordTrace_append hprefix tailTrace_758665
  have hstable : (prefixWord ++ tailWord_758665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758665).length < 2 ^ (prefixWord ++ tailWord_758665).sum := by decide
  have hdescent : baseEnd_758665 < baseStart_758665 := by decide
  rcases family_descends (prefixWord ++ tailWord_758665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758668 : List Nat := [2, 2, 1, 2, 1, 2, 13]
def baseStart_758668 : Nat := 118140960795 + 758668 * 2 ^ 59
def prefixEnd_758668 : Nat := 4983230072969 + 3 ^ 40 * 758668 * 2
def baseEnd_758668 : Nat := 4809399273893122736555

theorem tailTrace_758668 : CollatzResearch.WordTrace tailWord_758668 prefixEnd_758668 4809399273893122736555 := by
  unfold tailWord_758668
  simp only [CollatzResearch.WordTrace]
  refine ⟨13835447607741440511950329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18447263476988587349267105 13835447607741440511950329)
  ·
    refine ⟨10376585705806080383962747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13835447607741440511950329 10376585705806080383962747)
    ·
      refine ⟨15564878558709120575944121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10376585705806080383962747 15564878558709120575944121)
      ·
        refine ⟨11673658919031840431958091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15564878558709120575944121 11673658919031840431958091)
        ·
          refine ⟨17510488378547760647937137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11673658919031840431958091 17510488378547760647937137)
          ·
            refine ⟨13132866283910820485952853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17510488378547760647937137 13132866283910820485952853)
            ·
              refine ⟨4809399273893122736555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 13132866283910820485952853 4809399273893122736555)
              ·
                rfl

theorem cell23_758668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 13].length) (baseStart_758668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758668 prefixEnd_758668 := by exact prefixLift 758668
  have htrace : WordTrace (prefixWord ++ tailWord_758668) baseStart_758668 baseEnd_758668 := by
    simpa [prefixWord, tailWord_758668, baseEnd_758668] using wordTrace_append hprefix tailTrace_758668
  have hstable : (prefixWord ++ tailWord_758668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758668).length < 2 ^ (prefixWord ++ tailWord_758668).sum := by decide
  have hdescent : baseEnd_758668 < baseStart_758668 := by decide
  rcases family_descends (prefixWord ++ tailWord_758668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758685 : List Nat := [1, 4, 2, 1, 2, 1, 4, 8]
def baseStart_758685 : Nat := 118140960795 + 758685 * 2 ^ 59
def prefixEnd_758685 : Nat := 4983230072969 + 3 ^ 40 * 758685 * 2
def baseEnd_758685 : Nat := 14428521124313680561051

theorem tailTrace_758685 : CollatzResearch.WordTrace tailWord_758685 prefixEnd_758685 14428521124313680561051 := by
  unfold tailWord_758685
  simp only [CollatzResearch.WordTrace]
  refine ⟨27671515256421292927269509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18447676837614195284846339 27671515256421292927269509)
  ·
    refine ⟨5188409110578992423863033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27671515256421292927269509 5188409110578992423863033)
    ·
      refine ⟨3891306832934244317897275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5188409110578992423863033 3891306832934244317897275)
      ·
        refine ⟨5836960249401366476845913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891306832934244317897275 5836960249401366476845913)
        ·
          refine ⟨4377720187051024857634435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5836960249401366476845913 4377720187051024857634435)
          ·
            refine ⟨6566580280576537286451653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377720187051024857634435 6566580280576537286451653)
            ·
              refine ⟨1231233802608100741209685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6566580280576537286451653 1231233802608100741209685)
              ·
                refine ⟨14428521124313680561051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1231233802608100741209685 14428521124313680561051)
                ·
                  rfl

theorem cell23_758685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 8].length) (baseStart_758685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758685 prefixEnd_758685 := by exact prefixLift 758685
  have htrace : WordTrace (prefixWord ++ tailWord_758685) baseStart_758685 baseEnd_758685 := by
    simpa [prefixWord, tailWord_758685, baseEnd_758685] using wordTrace_append hprefix tailTrace_758685
  have hstable : (prefixWord ++ tailWord_758685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758685).length < 2 ^ (prefixWord ++ tailWord_758685).sum := by decide
  have hdescent : baseEnd_758685 < baseStart_758685 := by decide
  rcases family_descends (prefixWord ++ tailWord_758685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758689 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 2, 4]
def baseStart_758689 : Nat := 118140960795 + 758689 * 2 ^ 59
def prefixEnd_758689 : Nat := 4983230072969 + 3 ^ 40 * 758689 * 2
def baseEnd_758689 : Nat := 129857374759695786499453

theorem tailTrace_758689 : CollatzResearch.WordTrace tailWord_758689 prefixEnd_758689 129857374759695786499453 := by
  unfold tailWord_758689
  simp only [CollatzResearch.WordTrace]
  refine ⟨27671661148406801610415121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18447774098937867740276747 27671661148406801610415121)
  ·
    refine ⟨20753745861305101207811341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27671661148406801610415121 20753745861305101207811341)
    ·
      refine ⟨7782654697989412952929253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20753745861305101207811341 7782654697989412952929253)
      ·
        refine ⟨1459247755873014928674235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7782654697989412952929253 1459247755873014928674235)
        ·
          refine ⟨2188871633809522393011353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459247755873014928674235 2188871633809522393011353)
          ·
            refine ⟨1641653725357141794758515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2188871633809522393011353 1641653725357141794758515)
            ·
              refine ⟨2462480588035712692137773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641653725357141794758515 2462480588035712692137773)
              ·
                refine ⟨923430220513392259551665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2462480588035712692137773 923430220513392259551665)
                ·
                  refine ⟨692572665385044194663749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 923430220513392259551665 692572665385044194663749)
                  ·
                    refine ⟨129857374759695786499453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 692572665385044194663749 129857374759695786499453)
                    ·
                      rfl

theorem cell23_758689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_758689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758689 prefixEnd_758689 := by exact prefixLift 758689
  have htrace : WordTrace (prefixWord ++ tailWord_758689) baseStart_758689 baseEnd_758689 := by
    simpa [prefixWord, tailWord_758689, baseEnd_758689] using wordTrace_append hprefix tailTrace_758689
  have hstable : (prefixWord ++ tailWord_758689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758689).length < 2 ^ (prefixWord ++ tailWord_758689).sum := by decide
  have hdescent : baseEnd_758689 < baseStart_758689 := by decide
  rcases family_descends (prefixWord ++ tailWord_758689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758710 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_758710 : Nat := 118140960795 + 758710 * 2 ^ 59
def prefixEnd_758710 : Nat := 4983230072969 + 3 ^ 40 * 758710 * 2
def baseEnd_758710 : Nat := 129860969124277259111921

theorem tailTrace_758710 : CollatzResearch.WordTrace tailWord_758710 prefixEnd_758710 129860969124277259111921 := by
  unfold tailWord_758710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1729526692583170137308099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18448284720887148131286389 1729526692583170137308099)
  ·
    refine ⟨2594290038874755205962149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1729526692583170137308099 2594290038874755205962149)
    ·
      refine ⟨486429382289016601117903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2594290038874755205962149 486429382289016601117903)
      ·
        refine ⟨729644073433524901676855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486429382289016601117903 729644073433524901676855)
        ·
          refine ⟨1094466110150287352515283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729644073433524901676855 1094466110150287352515283)
          ·
            refine ⟨1641699165225431028772925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094466110150287352515283 1641699165225431028772925)
            ·
              refine ⟨615637186959536635789847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1641699165225431028772925 615637186959536635789847)
              ·
                refine ⟨923455780439304953684771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615637186959536635789847 923455780439304953684771)
                ·
                  refine ⟨1385183670658957430527157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923455780439304953684771 1385183670658957430527157)
                  ·
                    refine ⟨129860969124277259111921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1385183670658957430527157 129860969124277259111921)
                    ·
                      rfl

theorem cell23_758710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_758710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758710 prefixEnd_758710 := by exact prefixLift 758710
  have htrace : WordTrace (prefixWord ++ tailWord_758710) baseStart_758710 baseEnd_758710 := by
    simpa [prefixWord, tailWord_758710, baseEnd_758710] using wordTrace_append hprefix tailTrace_758710
  have hstable : (prefixWord ++ tailWord_758710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758710).length < 2 ^ (prefixWord ++ tailWord_758710).sum := by decide
  have hdescent : baseEnd_758710 < baseStart_758710 := by decide
  rcases family_descends (prefixWord ++ tailWord_758710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758712 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_758712 : Nat := 118140960795 + 758712 * 2 ^ 59
def prefixEnd_758712 : Nat := 4983230072969 + 3 ^ 40 * 758712 * 2
def baseEnd_758712 : Nat := 389583934334140769510753

theorem tailTrace_758712 : CollatzResearch.WordTrace tailWord_758712 prefixEnd_758712 389583934334140769510753 := by
  unfold tailWord_758712
  simp only [CollatzResearch.WordTrace]
  refine ⟨13836250013661738269251195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18448333351548984359001593 13836250013661738269251195)
  ·
    refine ⟨20754375020492607403876793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13836250013661738269251195 20754375020492607403876793)
    ·
      refine ⟨15565781265369455552907595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20754375020492607403876793 15565781265369455552907595)
      ·
        refine ⟨23348671898054183329361393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15565781265369455552907595 23348671898054183329361393)
        ·
          refine ⟨17511503923540637497021045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23348671898054183329361393 17511503923540637497021045)
          ·
            refine ⟨1641703492831934765345723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17511503923540637497021045 1641703492831934765345723)
            ·
              refine ⟨2462555239247902148018585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641703492831934765345723 2462555239247902148018585)
              ·
                refine ⟨1846916429435926611013939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462555239247902148018585 1846916429435926611013939)
                ·
                  refine ⟨2770374644153889916520909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846916429435926611013939 2770374644153889916520909)
                  ·
                    refine ⟨1038890491557708718695341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2770374644153889916520909 1038890491557708718695341)
                    ·
                      refine ⟨389583934334140769510753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1038890491557708718695341 389583934334140769510753)
                      ·
                        rfl

theorem cell23_758712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_758712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758712 prefixEnd_758712 := by exact prefixLift 758712
  have htrace : WordTrace (prefixWord ++ tailWord_758712) baseStart_758712 baseEnd_758712 := by
    simpa [prefixWord, tailWord_758712, baseEnd_758712] using wordTrace_append hprefix tailTrace_758712
  have hstable : (prefixWord ++ tailWord_758712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758712).length < 2 ^ (prefixWord ++ tailWord_758712).sum := by decide
  have hdescent : baseEnd_758712 < baseStart_758712 := by decide
  rcases family_descends (prefixWord ++ tailWord_758712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758735 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_758735 : Nat := 118140960795 + 758735 * 2 ^ 59
def prefixEnd_758735 : Nat := 4983230072969 + 3 ^ 40 * 758735 * 2
def baseEnd_758735 : Nat := 389595744389194179523147

theorem tailTrace_758735 : CollatzResearch.WordTrace tailWord_758735 prefixEnd_758735 389595744389194179523147 := by
  unfold tailWord_758735
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673338906240151466589659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18448892604160100977726439 27673338906240151466589659)
  ·
    refine ⟨41510008359360227199884489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27673338906240151466589659 41510008359360227199884489)
    ·
      refine ⟨31132506269520170399913367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41510008359360227199884489 31132506269520170399913367)
      ·
        refine ⟨46698759404280255599870051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31132506269520170399913367 46698759404280255599870051)
        ·
          refine ⟨70048139106420383399805077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46698759404280255599870051 70048139106420383399805077)
          ·
            refine ⟨3283506520613455471865863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70048139106420383399805077 3283506520613455471865863)
            ·
              refine ⟨4925259780920183207798795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283506520613455471865863 4925259780920183207798795)
              ·
                refine ⟨7387889671380274811698193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4925259780920183207798795 7387889671380274811698193)
                ·
                  refine ⟨5540917253535206108773645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7387889671380274811698193 5540917253535206108773645)
                  ·
                    refine ⟨2077843970075702290790117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5540917253535206108773645 2077843970075702290790117)
                    ·
                      refine ⟨389595744389194179523147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2077843970075702290790117 389595744389194179523147)
                      ·
                        rfl

theorem cell23_758735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_758735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758735 prefixEnd_758735 := by exact prefixLift 758735
  have htrace : WordTrace (prefixWord ++ tailWord_758735) baseStart_758735 baseEnd_758735 := by
    simpa [prefixWord, tailWord_758735, baseEnd_758735] using wordTrace_append hprefix tailTrace_758735
  have hstable : (prefixWord ++ tailWord_758735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758735).length < 2 ^ (prefixWord ++ tailWord_758735).sum := by decide
  have hdescent : baseEnd_758735 < baseStart_758735 := by decide
  rcases family_descends (prefixWord ++ tailWord_758735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758745 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 1, 8]
def baseStart_758745 : Nat := 118140960795 + 758745 * 2 ^ 59
def prefixEnd_758745 : Nat := 4983230072969 + 3 ^ 40 * 758745 * 2
def baseEnd_758745 : Nat := 129866959731913046799367

theorem tailTrace_758745 : CollatzResearch.WordTrace tailWord_758745 prefixEnd_758745 129866959731913046799367 := by
  unfold tailWord_758745
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673703636203923174453689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18449135757469282116302459 27673703636203923174453689)
  ·
    refine ⟨20755277727152942380840267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27673703636203923174453689 20755277727152942380840267)
    ·
      refine ⟨31132916590729413571260401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20755277727152942380840267 31132916590729413571260401)
      ·
        refine ⟨23349687443047060178445301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31132916590729413571260401 23349687443047060178445301)
        ·
          refine ⟨2189033197785661891729247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23349687443047060178445301 2189033197785661891729247)
          ·
            refine ⟨3283549796678492837593871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189033197785661891729247 3283549796678492837593871)
            ·
              refine ⟨4925324695017739256390807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283549796678492837593871 4925324695017739256390807)
              ·
                refine ⟨7387987042526608884586211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4925324695017739256390807 7387987042526608884586211)
                ·
                  refine ⟨11081980563789913326879317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7387987042526608884586211 11081980563789913326879317)
                  ·
                    refine ⟨129866959731913046799367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11081980563789913326879317 129866959731913046799367)
                    ·
                      rfl

theorem cell23_758745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_758745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758745 prefixEnd_758745 := by exact prefixLift 758745
  have htrace : WordTrace (prefixWord ++ tailWord_758745) baseStart_758745 baseEnd_758745 := by
    simpa [prefixWord, tailWord_758745, baseEnd_758745] using wordTrace_append hprefix tailTrace_758745
  have hstable : (prefixWord ++ tailWord_758745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758745).length < 2 ^ (prefixWord ++ tailWord_758745).sum := by decide
  have hdescent : baseEnd_758745 < baseStart_758745 := by decide
  rcases family_descends (prefixWord ++ tailWord_758745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758769 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 1, 4, 2]
def baseStart_758769 : Nat := 118140960795 + 758769 * 2 ^ 59
def prefixEnd_758769 : Nat := 4983230072969 + 3 ^ 40 * 758769 * 2
def baseEnd_758769 : Nat := 389613202731447046497991

theorem tailTrace_758769 : CollatzResearch.WordTrace tailWord_758769 prefixEnd_758769 389613202731447046497991 := by
  unfold tailWord_758769
  simp only [CollatzResearch.WordTrace]
  refine ⟨27674578988116975273327361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18449719325411316848884907 27674578988116975273327361)
  ·
    refine ⟨20755934241087731454995521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27674578988116975273327361 20755934241087731454995521)
    ·
      refine ⟨15566950680815798591246641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20755934241087731454995521 15566950680815798591246641)
      ·
        refine ⟨11675213010611848943434981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15566950680815798591246641 11675213010611848943434981)
        ·
          refine ⟨2189102439489721676894059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11675213010611848943434981 2189102439489721676894059)
          ·
            refine ⟨3283653659234582515341089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189102439489721676894059 3283653659234582515341089)
            ·
              refine ⟨2462740244425936886505817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3283653659234582515341089 2462740244425936886505817)
              ·
                refine ⟨1847055183319452664879363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462740244425936886505817 1847055183319452664879363)
                ·
                  refine ⟨2770582774979178997319045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847055183319452664879363 2770582774979178997319045)
                  ·
                    refine ⟨519484270308596061997321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2770582774979178997319045 519484270308596061997321)
                    ·
                      refine ⟨389613202731447046497991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519484270308596061997321 389613202731447046497991)
                      ·
                        rfl

theorem cell23_758769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_758769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758769 prefixEnd_758769 := by exact prefixLift 758769
  have htrace : WordTrace (prefixWord ++ tailWord_758769) baseStart_758769 baseEnd_758769 := by
    simpa [prefixWord, tailWord_758769, baseEnd_758769] using wordTrace_append hprefix tailTrace_758769
  have hstable : (prefixWord ++ tailWord_758769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758769).length < 2 ^ (prefixWord ++ tailWord_758769).sum := by decide
  have hdescent : baseEnd_758769 < baseStart_758769 := by decide
  rcases family_descends (prefixWord ++ tailWord_758769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758792 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 7]
def baseStart_758792 : Nat := 118140960795 + 758792 * 2 ^ 59
def prefixEnd_758792 : Nat := 4983230072969 + 3 ^ 40 * 758792 * 2
def baseEnd_758792 : Nat := 43291668087388939612265

theorem tailTrace_758792 : CollatzResearch.WordTrace tailWord_758792 prefixEnd_758792 43291668087388939612265 := by
  unfold tailWord_758792
  simp only [CollatzResearch.WordTrace]
  refine ⟨13837708933516825100707315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18450278578022433467609753 13837708933516825100707315)
  ·
    refine ⟨20756563400275237651060973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13837708933516825100707315 20756563400275237651060973)
    ·
      refine ⟨7783711275103214119147865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20756563400275237651060973 7783711275103214119147865)
      ·
        refine ⟨5837783456327410589360899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7783711275103214119147865 5837783456327410589360899)
        ·
          refine ⟨8756675184491115884041349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5837783456327410589360899 8756675184491115884041349)
          ·
            refine ⟨1641876597092084228257753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8756675184491115884041349 1641876597092084228257753)
            ·
              refine ⟨1231407447819063171193315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1641876597092084228257753 1231407447819063171193315)
              ·
                refine ⟨1847111171728594756789973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231407447819063171193315 1847111171728594756789973)
                ·
                  refine ⟨43291668087388939612265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1847111171728594756789973 43291668087388939612265)
                  ·
                    rfl

theorem cell23_758792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 7].length) (baseStart_758792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758792 prefixEnd_758792 := by exact prefixLift 758792
  have htrace : WordTrace (prefixWord ++ tailWord_758792) baseStart_758792 baseEnd_758792 := by
    simpa [prefixWord, tailWord_758792, baseEnd_758792] using wordTrace_append hprefix tailTrace_758792
  have hstable : (prefixWord ++ tailWord_758792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758792).length < 2 ^ (prefixWord ++ tailWord_758792).sum := by decide
  have hdescent : baseEnd_758792 < baseStart_758792 := by decide
  rcases family_descends (prefixWord ++ tailWord_758792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758842 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_758842 : Nat := 118140960795 + 758842 * 2 ^ 59
def prefixEnd_758842 : Nat := 4983230072969 + 3 ^ 40 * 758842 * 2
def baseEnd_758842 : Nat := 389650686819225260885155

theorem tailTrace_758842 : CollatzResearch.WordTrace tailWord_758842 prefixEnd_758842 389650686819225260885155 := by
  unfold tailWord_758842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919310379213127185183695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18451494344568339160489853 6919310379213127185183695)
  ·
    refine ⟨10378965568819690777775543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6919310379213127185183695 10378965568819690777775543)
    ·
      refine ⟨15568448353229536166663315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10378965568819690777775543 15568448353229536166663315)
      ·
        refine ⟨23352672529844304249994973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15568448353229536166663315 23352672529844304249994973)
        ·
          refine ⟨8757252198691614093748115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23352672529844304249994973 8757252198691614093748115)
          ·
            refine ⟨13135878298037421140622173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8757252198691614093748115 13135878298037421140622173)
            ·
              refine ⟨4925954361764032927733315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13135878298037421140622173 4925954361764032927733315)
              ·
                refine ⟨7388931542646049391599973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4925954361764032927733315 7388931542646049391599973)
                ·
                  refine ⟨1385424664246134260924995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7388931542646049391599973 1385424664246134260924995)
                  ·
                    refine ⟨2078136996369201391387493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1385424664246134260924995 2078136996369201391387493)
                    ·
                      refine ⟨389650686819225260885155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2078136996369201391387493 389650686819225260885155)
                      ·
                        rfl

theorem cell23_758842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_758842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758842 prefixEnd_758842 := by exact prefixLift 758842
  have htrace : WordTrace (prefixWord ++ tailWord_758842) baseStart_758842 baseEnd_758842 := by
    simpa [prefixWord, tailWord_758842, baseEnd_758842] using wordTrace_append hprefix tailTrace_758842
  have hstable : (prefixWord ++ tailWord_758842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758842).length < 2 ^ (prefixWord ++ tailWord_758842).sum := by decide
  have hdescent : baseEnd_758842 < baseStart_758842 := by decide
  rcases family_descends (prefixWord ++ tailWord_758842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758849 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_758849 : Nat := 118140960795 + 758849 * 2 ^ 59
def prefixEnd_758849 : Nat := 4983230072969 + 3 ^ 40 * 758849 * 2
def baseEnd_758849 : Nat := 389654281183806733497623

theorem tailTrace_758849 : CollatzResearch.WordTrace tailWord_758849 prefixEnd_758849 389654281183806733497623 := by
  unfold tailWord_758849
  simp only [CollatzResearch.WordTrace]
  refine ⟨27677496827827148936239601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18451664551884765957493067 27677496827827148936239601)
  ·
    refine ⟨20758122620870361702179701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27677496827827148936239601 20758122620870361702179701)
    ·
      refine ⟨1946073995706596409579347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20758122620870361702179701 1946073995706596409579347)
      ·
        refine ⟨2919110993559894614369021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1946073995706596409579347 2919110993559894614369021)
        ·
          refine ⟨1094666622584960480388383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2919110993559894614369021 1094666622584960480388383)
          ·
            refine ⟨1641999933877440720582575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094666622584960480388383 1641999933877440720582575)
            ·
              refine ⟨2462999900816161080873863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641999933877440720582575 2462999900816161080873863)
              ·
                refine ⟨3694499851224241621310795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462999900816161080873863 3694499851224241621310795)
                ·
                  refine ⟨5541749776836362431966193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694499851224241621310795 5541749776836362431966193)
                  ·
                    refine ⟨4156312332627271823974645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5541749776836362431966193 4156312332627271823974645)
                    ·
                      refine ⟨389654281183806733497623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4156312332627271823974645 389654281183806733497623)
                      ·
                        rfl

theorem cell23_758849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_758849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758849 prefixEnd_758849 := by exact prefixLift 758849
  have htrace : WordTrace (prefixWord ++ tailWord_758849) baseStart_758849 baseEnd_758849 := by
    simpa [prefixWord, tailWord_758849, baseEnd_758849] using wordTrace_append hprefix tailTrace_758849
  have hstable : (prefixWord ++ tailWord_758849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758849).length < 2 ^ (prefixWord ++ tailWord_758849).sum := by decide
  have hdescent : baseEnd_758849 < baseStart_758849 := by decide
  rcases family_descends (prefixWord ++ tailWord_758849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758879 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 3]
def baseStart_758879 : Nat := 118140960795 + 758879 * 2 ^ 59
def prefixEnd_758879 : Nat := 4983230072969 + 3 ^ 40 * 758879 * 2
def baseEnd_758879 : Nat := 389669685603441616122485

theorem tailTrace_758879 : CollatzResearch.WordTrace tailWord_758879 prefixEnd_758879 389669685603441616122485 := by
  unfold tailWord_758879
  simp only [CollatzResearch.WordTrace]
  refine ⟨27678591017718464059831691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18452394011812309373221127 27678591017718464059831691)
  ·
    refine ⟨41517886526577696089747537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27678591017718464059831691 41517886526577696089747537)
    ·
      refine ⟨31138414894933272067310653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41517886526577696089747537 31138414894933272067310653)
      ·
        refine ⟨11676905585599977025241495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31138414894933272067310653 11676905585599977025241495)
        ·
          refine ⟨17515358378399965537862243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11676905585599977025241495 17515358378399965537862243)
          ·
            refine ⟨26273037567599948306793365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17515358378399965537862243 26273037567599948306793365)
            ·
              refine ⟨1231548635981247576880939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26273037567599948306793365 1231548635981247576880939)
              ·
                refine ⟨1847322953971871365321409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231548635981247576880939 1847322953971871365321409)
                ·
                  refine ⟨1385492215478903523991057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1847322953971871365321409 1385492215478903523991057)
                  ·
                    refine ⟨1039119161609177642993293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1385492215478903523991057 1039119161609177642993293)
                    ·
                      refine ⟨389669685603441616122485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1039119161609177642993293 389669685603441616122485)
                      ·
                        rfl

theorem cell23_758879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_758879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758879 prefixEnd_758879 := by exact prefixLift 758879
  have htrace : WordTrace (prefixWord ++ tailWord_758879) baseStart_758879 baseEnd_758879 := by
    simpa [prefixWord, tailWord_758879, baseEnd_758879] using wordTrace_append hprefix tailTrace_758879
  have hstable : (prefixWord ++ tailWord_758879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758879).length < 2 ^ (prefixWord ++ tailWord_758879).sum := by decide
  have hdescent : baseEnd_758879 < baseStart_758879 := by decide
  rcases family_descends (prefixWord ++ tailWord_758879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758912 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 3, 5]
def baseStart_758912 : Nat := 118140960795 + 758912 * 2 ^ 59
def prefixEnd_758912 : Nat := 4983230072969 + 3 ^ 40 * 758912 * 2
def baseEnd_758912 : Nat := 129895543488346662336611

theorem tailTrace_758912 : CollatzResearch.WordTrace tailWord_758912 prefixEnd_758912 129895543488346662336611 := by
  unfold tailWord_758912
  simp only [CollatzResearch.WordTrace]
  refine ⟨13839897313299455347891495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18453196417732607130521993 13839897313299455347891495)
  ·
    refine ⟨20759845969949183021837243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13839897313299455347891495 20759845969949183021837243)
    ·
      refine ⟨31139768954923774532755865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20759845969949183021837243 31139768954923774532755865)
      ·
        refine ⟨23354826716192830899566899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31139768954923774532755865 23354826716192830899566899)
        ·
          refine ⟨35032240074289246349350349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23354826716192830899566899 35032240074289246349350349)
          ·
            refine ⟨13137090027858467381006381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35032240074289246349350349 13137090027858467381006381)
            ·
              refine ⟨4926408760446925267877393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13137090027858467381006381 4926408760446925267877393)
              ·
                refine ⟨3694806570335193950908045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4926408760446925267877393 3694806570335193950908045)
                ·
                  refine ⟨1385552463875697731590517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3694806570335193950908045 1385552463875697731590517)
                  ·
                    refine ⟨129895543488346662336611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1385552463875697731590517 129895543488346662336611)
                    ·
                      rfl

theorem cell23_758912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_758912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758912 prefixEnd_758912 := by exact prefixLift 758912
  have htrace : WordTrace (prefixWord ++ tailWord_758912) baseStart_758912 baseEnd_758912 := by
    simpa [prefixWord, tailWord_758912, baseEnd_758912] using wordTrace_append hprefix tailTrace_758912
  have hstable : (prefixWord ++ tailWord_758912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758912).length < 2 ^ (prefixWord ++ tailWord_758912).sum := by decide
  have hdescent : baseEnd_758912 < baseStart_758912 := by decide
  rcases family_descends (prefixWord ++ tailWord_758912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758919 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_758919 : Nat := 118140960795 + 758919 * 2 ^ 59
def prefixEnd_758919 : Nat := 4983230072969 + 3 ^ 40 * 758919 * 2
def baseEnd_758919 : Nat := 389690224829621459622301

theorem tailTrace_758919 : CollatzResearch.WordTrace tailWord_758919 prefixEnd_758919 389690224829621459622301 := by
  unfold tailWord_758919
  simp only [CollatzResearch.WordTrace]
  refine ⟨27680049937573550891287811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18453366625049033927525207 27680049937573550891287811)
  ·
    refine ⟨41520074906360326336931717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27680049937573550891287811 41520074906360326336931717)
    ·
      refine ⟨7785014044942561188174697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41520074906360326336931717 7785014044942561188174697)
      ·
        refine ⟨5838760533706920891131023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7785014044942561188174697 5838760533706920891131023)
        ·
          refine ⟨8758140800560381336696535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5838760533706920891131023 8758140800560381336696535)
          ·
            refine ⟨13137211200840572005044803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8758140800560381336696535 13137211200840572005044803)
            ·
              refine ⟨19705816801260858007567205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13137211200840572005044803 19705816801260858007567205)
              ·
                refine ⟨3694840650236410876418851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19705816801260858007567205 3694840650236410876418851)
                ·
                  refine ⟨5542260975354616314628277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694840650236410876418851 5542260975354616314628277)
                  ·
                    refine ⟨519586966439495279496401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5542260975354616314628277 519586966439495279496401)
                    ·
                      refine ⟨389690224829621459622301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519586966439495279496401 389690224829621459622301)
                      ·
                        rfl

theorem cell23_758919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_758919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758919 prefixEnd_758919 := by exact prefixLift 758919
  have htrace : WordTrace (prefixWord ++ tailWord_758919) baseStart_758919 baseEnd_758919 := by
    simpa [prefixWord, tailWord_758919, baseEnd_758919] using wordTrace_append hprefix tailTrace_758919
  have hstable : (prefixWord ++ tailWord_758919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758919).length < 2 ^ (prefixWord ++ tailWord_758919).sum := by decide
  have hdescent : baseEnd_758919 < baseStart_758919 := by decide
  rcases family_descends (prefixWord ++ tailWord_758919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758922 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_758922 : Nat := 118140960795 + 758922 * 2 ^ 59
def prefixEnd_758922 : Nat := 4983230072969 + 3 ^ 40 * 758922 * 2
def baseEnd_758922 : Nat := 389691765271584947884787

theorem tailTrace_758922 : CollatzResearch.WordTrace tailWord_758922 prefixEnd_758922 389691765271584947884787 := by
  unfold tailWord_758922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920039839140670600911755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18453439571041788269098013 6920039839140670600911755)
  ·
    refine ⟨10380059758711005901367633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6920039839140670600911755 10380059758711005901367633)
    ·
      refine ⟨7785044819033254426025725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10380059758711005901367633 7785044819033254426025725)
      ·
        refine ⟨2919391807137470409759647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7785044819033254426025725 2919391807137470409759647)
        ·
          refine ⟨4379087710706205614639471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2919391807137470409759647 4379087710706205614639471)
          ·
            refine ⟨6568631566059308421959207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4379087710706205614639471 6568631566059308421959207)
            ·
              refine ⟨9852947349088962632938811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6568631566059308421959207 9852947349088962632938811)
              ·
                refine ⟨14779421023633443949408217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9852947349088962632938811 14779421023633443949408217)
                ·
                  refine ⟨11084565767725082962056163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14779421023633443949408217 11084565767725082962056163)
                  ·
                    refine ⟨16626848651587624443084245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11084565767725082962056163 16626848651587624443084245)
                    ·
                      refine ⟨389691765271584947884787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16626848651587624443084245 389691765271584947884787)
                      ·
                        rfl

theorem cell23_758922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_758922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758922 prefixEnd_758922 := by exact prefixLift 758922
  have htrace : WordTrace (prefixWord ++ tailWord_758922) baseStart_758922 baseEnd_758922 := by
    simpa [prefixWord, tailWord_758922, baseEnd_758922] using wordTrace_append hprefix tailTrace_758922
  have hstable : (prefixWord ++ tailWord_758922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758922).length < 2 ^ (prefixWord ++ tailWord_758922).sum := by decide
  have hdescent : baseEnd_758922 < baseStart_758922 := by decide
  rcases family_descends (prefixWord ++ tailWord_758922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758926 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_758926 : Nat := 118140960795 + 758926 * 2 ^ 59
def prefixEnd_758926 : Nat := 4983230072969 + 3 ^ 40 * 758926 * 2
def baseEnd_758926 : Nat := 389693819194202932234769

theorem tailTrace_758926 : CollatzResearch.WordTrace tailWord_758926 prefixEnd_758926 389693819194202932234769 := by
  unfold tailWord_758926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3460038156068523885849079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18453536832365460724528421 3460038156068523885849079)
  ·
    refine ⟨5190057234102785828773619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3460038156068523885849079 5190057234102785828773619)
    ·
      refine ⟨7785085851154178743160429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5190057234102785828773619 7785085851154178743160429)
      ·
        refine ⟨2919407194182817028685161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7785085851154178743160429 2919407194182817028685161)
        ·
          refine ⟨2189555395637112771513871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2919407194182817028685161 2189555395637112771513871)
          ·
            refine ⟨3284333093455669157270807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189555395637112771513871 3284333093455669157270807)
            ·
              refine ⟨4926499640183503735906211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284333093455669157270807 4926499640183503735906211)
              ·
                refine ⟨7389749460275255603859317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926499640183503735906211 7389749460275255603859317)
                ·
                  refine ⟨692789011900805212861811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7389749460275255603859317 692789011900805212861811)
                  ·
                    refine ⟨1039183517851207819292717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 692789011900805212861811 1039183517851207819292717)
                    ·
                      refine ⟨389693819194202932234769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1039183517851207819292717 389693819194202932234769)
                      ·
                        rfl

theorem cell23_758926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_758926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758926 prefixEnd_758926 := by exact prefixLift 758926
  have htrace : WordTrace (prefixWord ++ tailWord_758926) baseStart_758926 baseEnd_758926 := by
    simpa [prefixWord, tailWord_758926, baseEnd_758926] using wordTrace_append hprefix tailTrace_758926
  have hstable : (prefixWord ++ tailWord_758926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758926).length < 2 ^ (prefixWord ++ tailWord_758926).sum := by decide
  have hdescent : baseEnd_758926 < baseStart_758926 := by decide
  rcases family_descends (prefixWord ++ tailWord_758926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758936 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 1, 5, 2]
def baseStart_758936 : Nat := 118140960795 + 758936 * 2 ^ 59
def prefixEnd_758936 : Nat := 4983230072969 + 3 ^ 40 * 758936 * 2
def baseEnd_758936 : Nat := 389698954000747893109723

theorem tailTrace_758936 : CollatzResearch.WordTrace tailWord_758936 prefixEnd_758936 389698954000747893109723 := by
  unfold tailWord_758936
  simp only [CollatzResearch.WordTrace]
  refine ⟨13840334989255981397328331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18453779985674641863104441 13840334989255981397328331)
  ·
    refine ⟨20760502483883972095992497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13840334989255981397328331 20760502483883972095992497)
    ·
      refine ⟨15570376862912979071994373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20760502483883972095992497 15570376862912979071994373)
      ·
        refine ⟨2919445661796183575998945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15570376862912979071994373 2919445661796183575998945)
        ·
          refine ⟨2189584246347137681999209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2919445661796183575998945 2189584246347137681999209)
          ·
            refine ⟨1642188184760353261499407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2189584246347137681999209 1642188184760353261499407)
            ·
              refine ⟨2463282277140529892249111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642188184760353261499407 2463282277140529892249111)
              ·
                refine ⟨3694923415710794838373667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463282277140529892249111 3694923415710794838373667)
                ·
                  refine ⟨5542385123566192257560501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694923415710794838373667 5542385123566192257560501)
                  ·
                    refine ⟨519598605334330524146297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5542385123566192257560501 519598605334330524146297)
                    ·
                      refine ⟨389698954000747893109723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519598605334330524146297 389698954000747893109723)
                      ·
                        rfl

theorem cell23_758936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_758936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758936 prefixEnd_758936 := by exact prefixLift 758936
  have htrace : WordTrace (prefixWord ++ tailWord_758936) baseStart_758936 baseEnd_758936 := by
    simpa [prefixWord, tailWord_758936, baseEnd_758936] using wordTrace_append hprefix tailTrace_758936
  have hstable : (prefixWord ++ tailWord_758936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758936).length < 2 ^ (prefixWord ++ tailWord_758936).sum := by decide
  have hdescent : baseEnd_758936 < baseStart_758936 := by decide
  rcases family_descends (prefixWord ++ tailWord_758936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758969 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_758969 : Nat := 118140960795 + 758969 * 2 ^ 59
def prefixEnd_758969 : Nat := 4983230072969 + 3 ^ 40 * 758969 * 2
def baseEnd_758969 : Nat := 389715898862346263997071

theorem tailTrace_758969 : CollatzResearch.WordTrace tailWord_758969 prefixEnd_758969 389715898862346263997071 := by
  unfold tailWord_758969
  simp only [CollatzResearch.WordTrace]
  refine ⟨27681873587392409430607961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18454582391594939620405307 27681873587392409430607961)
  ·
    refine ⟨20761405190544307072955971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27681873587392409430607961 20761405190544307072955971)
    ·
      refine ⟨31142107785816460609433957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20761405190544307072955971 31142107785816460609433957)
      ·
        refine ⟨5839145209840586364268867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31142107785816460609433957 5839145209840586364268867)
        ·
          refine ⟨8758717814760879546403301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5839145209840586364268867 8758717814760879546403301)
          ·
            refine ⟨1642259590267664914950619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8758717814760879546403301 1642259590267664914950619)
            ·
              refine ⟨2463389385401497372425929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642259590267664914950619 2463389385401497372425929)
              ·
                refine ⟨1847542039051123029319447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2463389385401497372425929 1847542039051123029319447)
                ·
                  refine ⟨2771313058576684543979171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847542039051123029319447 2771313058576684543979171)
                  ·
                    refine ⟨4156969587865026815968757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2771313058576684543979171 4156969587865026815968757)
                    ·
                      refine ⟨389715898862346263997071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4156969587865026815968757 389715898862346263997071)
                      ·
                        rfl

theorem cell23_758969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_758969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758969 prefixEnd_758969 := by exact prefixLift 758969
  have htrace : WordTrace (prefixWord ++ tailWord_758969) baseStart_758969 baseEnd_758969 := by
    simpa [prefixWord, tailWord_758969, baseEnd_758969] using wordTrace_append hprefix tailTrace_758969
  have hstable : (prefixWord ++ tailWord_758969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758969).length < 2 ^ (prefixWord ++ tailWord_758969).sum := by decide
  have hdescent : baseEnd_758969 < baseStart_758969 := by decide
  rcases family_descends (prefixWord ++ tailWord_758969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758976 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 1, 6]
def baseStart_758976 : Nat := 118140960795 + 758976 * 2 ^ 59
def prefixEnd_758976 : Nat := 4983230072969 + 3 ^ 40 * 758976 * 2
def baseEnd_758976 : Nat := 129906497742309245536513

theorem tailTrace_758976 : CollatzResearch.WordTrace tailWord_758976 prefixEnd_758976 129906497742309245536513 := by
  unfold tailWord_758976
  simp only [CollatzResearch.WordTrace]
  refine ⟨13841064449183524813056391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18454752598911366417408521 13841064449183524813056391)
  ·
    refine ⟨20761596673775287219584587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13841064449183524813056391 20761596673775287219584587)
    ·
      refine ⟨31142395010662930829376881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20761596673775287219584587 31142395010662930829376881)
      ·
        refine ⟨23356796257997198122032661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31142395010662930829376881 23356796257997198122032661)
        ·
          refine ⟨1094849824593618661970281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23356796257997198122032661 1094849824593618661970281)
          ·
            refine ⟨821137368445213996477711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1094849824593618661970281 821137368445213996477711)
            ·
              refine ⟨1231706052667820994716567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821137368445213996477711 1231706052667820994716567)
              ·
                refine ⟨1847559079001731492074851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231706052667820994716567 1847559079001731492074851)
                ·
                  refine ⟨2771338618502597238112277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847559079001731492074851 2771338618502597238112277)
                  ·
                    refine ⟨129906497742309245536513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2771338618502597238112277 129906497742309245536513)
                    ·
                      rfl

theorem cell23_758976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 6].length) (baseStart_758976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758976 prefixEnd_758976 := by exact prefixLift 758976
  have htrace : WordTrace (prefixWord ++ tailWord_758976) baseStart_758976 baseEnd_758976 := by
    simpa [prefixWord, tailWord_758976, baseEnd_758976] using wordTrace_append hprefix tailTrace_758976
  have hstable : (prefixWord ++ tailWord_758976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758976).length < 2 ^ (prefixWord ++ tailWord_758976).sum := by decide
  have hdescent : baseEnd_758976 < baseStart_758976 := by decide
  rcases family_descends (prefixWord ++ tailWord_758976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758986 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_758986 : Nat := 118140960795 + 758986 * 2 ^ 59
def prefixEnd_758986 : Nat := 4983230072969 + 3 ^ 40 * 758986 * 2
def baseEnd_758986 : Nat := 389724628033472697484493

theorem tailTrace_758986 : CollatzResearch.WordTrace tailWord_758986 prefixEnd_758986 389724628033472697484493 := by
  unfold tailWord_758986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920623407082705333494203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18454995752220547555984541 6920623407082705333494203)
  ·
    refine ⟨10380935110624058000241305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6920623407082705333494203 10380935110624058000241305)
    ·
      refine ⟨7785701332968043500180979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10380935110624058000241305 7785701332968043500180979)
      ·
        refine ⟨11678551999452065250271469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785701332968043500180979 11678551999452065250271469)
        ·
          refine ⟨4379456999794524468851801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11678551999452065250271469 4379456999794524468851801)
          ·
            refine ⟨3284592749845893351638851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4379456999794524468851801 3284592749845893351638851)
            ·
              refine ⟨4926889124768840027458277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284592749845893351638851 4926889124768840027458277)
              ·
                refine ⟨923791710894157505148427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4926889124768840027458277 923791710894157505148427)
                ·
                  refine ⟨1385687566341236257722641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923791710894157505148427 1385687566341236257722641)
                  ·
                    refine ⟨1039265674755927193291981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1385687566341236257722641 1039265674755927193291981)
                    ·
                      refine ⟨389724628033472697484493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1039265674755927193291981 389724628033472697484493)
                      ·
                        rfl

theorem cell23_758986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_758986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758986 prefixEnd_758986 := by exact prefixLift 758986
  have htrace : WordTrace (prefixWord ++ tailWord_758986) baseStart_758986 baseEnd_758986 := by
    simpa [prefixWord, tailWord_758986, baseEnd_758986] using wordTrace_append hprefix tailTrace_758986
  have hstable : (prefixWord ++ tailWord_758986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758986).length < 2 ^ (prefixWord ++ tailWord_758986).sum := by decide
  have hdescent : baseEnd_758986 < baseStart_758986 := by decide
  rcases family_descends (prefixWord ++ tailWord_758986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758999 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_758999 : Nat := 118140960795 + 758999 * 2 ^ 59
def prefixEnd_758999 : Nat := 4983230072969 + 3 ^ 40 * 758999 * 2
def baseEnd_758999 : Nat := 389731303281981146621933

theorem tailTrace_758999 : CollatzResearch.WordTrace tailWord_758999 prefixEnd_758999 389731303281981146621933 := by
  unfold tailWord_758999
  simp only [CollatzResearch.WordTrace]
  refine ⟨27682967777283724554200051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18455311851522483036133367 27682967777283724554200051)
  ·
    refine ⟨41524451665925586831300077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27682967777283724554200051 41524451665925586831300077)
    ·
      refine ⟨15571669374722095061737529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41524451665925586831300077 15571669374722095061737529)
      ·
        refine ⟨11678752031041571296303147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15571669374722095061737529 11678752031041571296303147)
        ·
          refine ⟨17518128046562356944454721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11678752031041571296303147 17518128046562356944454721)
          ·
            refine ⟨13138596034921767708341041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17518128046562356944454721 13138596034921767708341041)
            ·
              refine ⟨9853947026191325781255781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13138596034921767708341041 9853947026191325781255781)
              ·
                refine ⟨1847615067410873583985459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9853947026191325781255781 1847615067410873583985459)
                ·
                  refine ⟨2771422601116310375978189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847615067410873583985459 2771422601116310375978189)
                  ·
                    refine ⟨1039283475418616390991821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2771422601116310375978189 1039283475418616390991821)
                    ·
                      refine ⟨389731303281981146621933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1039283475418616390991821 389731303281981146621933)
                      ·
                        rfl

theorem cell23_758999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_758999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_758999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_758999 prefixEnd_758999 := by exact prefixLift 758999
  have htrace : WordTrace (prefixWord ++ tailWord_758999) baseStart_758999 baseEnd_758999 := by
    simpa [prefixWord, tailWord_758999, baseEnd_758999] using wordTrace_append hprefix tailTrace_758999
  have hstable : (prefixWord ++ tailWord_758999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758999).length < 2 ^ (prefixWord ++ tailWord_758999).sum := by decide
  have hdescent : baseEnd_758999 < baseStart_758999 := by decide
  rcases family_descends (prefixWord ++ tailWord_758999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759002 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_759002 : Nat := 118140960795 + 759002 * 2 ^ 59
def prefixEnd_759002 : Nat := 4983230072969 + 3 ^ 40 * 759002 * 2
def baseEnd_759002 : Nat := 129910947907981544961473

theorem tailTrace_759002 : CollatzResearch.WordTrace tailWord_759002 prefixEnd_759002 129910947907981544961473 := by
  unfold tailWord_759002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920769299068214016639815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18455384797515237377706173 6920769299068214016639815)
  ·
    refine ⟨10381153948602321024959723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6920769299068214016639815 10381153948602321024959723)
    ·
      refine ⟨15571730922903481537439585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10381153948602321024959723 15571730922903481537439585)
      ·
        refine ⟨11678798192177611153079689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15571730922903481537439585 11678798192177611153079689)
        ·
          refine ⟨8759098644133208364809767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11678798192177611153079689 8759098644133208364809767)
          ·
            refine ⟨13138647966199812547214651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8759098644133208364809767 13138647966199812547214651)
            ·
              refine ⟨19707971949299718820821977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13138647966199812547214651 19707971949299718820821977)
              ·
                refine ⟨14780978961974789115616483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19707971949299718820821977 14780978961974789115616483)
                ·
                  refine ⟨22171468442962183673424725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14780978961974789115616483 22171468442962183673424725)
                  ·
                    refine ⟨129910947907981544961473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 22171468442962183673424725 129910947907981544961473)
                    ·
                      rfl

theorem cell23_759002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_759002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759002 prefixEnd_759002 := by exact prefixLift 759002
  have htrace : WordTrace (prefixWord ++ tailWord_759002) baseStart_759002 baseEnd_759002 := by
    simpa [prefixWord, tailWord_759002, baseEnd_759002] using wordTrace_append hprefix tailTrace_759002
  have hstable : (prefixWord ++ tailWord_759002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759002).length < 2 ^ (prefixWord ++ tailWord_759002).sum := by decide
  have hdescent : baseEnd_759002 < baseStart_759002 := by decide
  rcases family_descends (prefixWord ++ tailWord_759002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759016 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_759016 : Nat := 118140960795 + 759016 * 2 ^ 59
def prefixEnd_759016 : Nat := 4983230072969 + 3 ^ 40 * 759016 * 2
def baseEnd_759016 : Nat := 389740032453107580109355

theorem tailTrace_759016 : CollatzResearch.WordTrace tailWord_759016 prefixEnd_759016 389740032453107580109355 := by
  unfold tailWord_759016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13841793909111068228784451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18455725212148090971712601 13841793909111068228784451)
  ·
    refine ⟨20762690863666602343176677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13841793909111068228784451 20762690863666602343176677)
    ·
      refine ⟨3893004536937487939345627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20762690863666602343176677 3893004536937487939345627)
      ·
        refine ⟨5839506805406231909018441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893004536937487939345627 5839506805406231909018441)
        ·
          refine ⟨4379630104054673931763831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5839506805406231909018441 4379630104054673931763831)
          ·
            refine ⟨6569445156082010897645747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4379630104054673931763831 6569445156082010897645747)
            ·
              refine ⟨9854167734123016346468621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6569445156082010897645747 9854167734123016346468621)
              ·
                refine ⟨3695312900296131129925733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9854167734123016346468621 3695312900296131129925733)
                ·
                  refine ⟨692871168805524586861075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3695312900296131129925733 692871168805524586861075)
                  ·
                    refine ⟨1039306753208286880291613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 692871168805524586861075 1039306753208286880291613)
                    ·
                      refine ⟨389740032453107580109355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1039306753208286880291613 389740032453107580109355)
                      ·
                        rfl

theorem cell23_759016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_759016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759016 prefixEnd_759016 := by exact prefixLift 759016
  have htrace : WordTrace (prefixWord ++ tailWord_759016) baseStart_759016 baseEnd_759016 := by
    simpa [prefixWord, tailWord_759016, baseEnd_759016] using wordTrace_append hprefix tailTrace_759016
  have hstable : (prefixWord ++ tailWord_759016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759016).length < 2 ^ (prefixWord ++ tailWord_759016).sum := by decide
  have hdescent : baseEnd_759016 < baseStart_759016 := by decide
  rcases family_descends (prefixWord ++ tailWord_759016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759043 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 1, 3, 2]
def baseStart_759043 : Nat := 118140960795 + 759043 * 2 ^ 59
def prefixEnd_759043 : Nat := 4983230072969 + 3 ^ 40 * 759043 * 2
def baseEnd_759043 : Nat := 389753896430778974471731

theorem tailTrace_759043 : CollatzResearch.WordTrace tailWord_759043 prefixEnd_759043 389753896430778974471731 := by
  unfold tailWord_759043
  simp only [CollatzResearch.WordTrace]
  refine ⟨27684572589124320068801783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18456381726082880045867855 27684572589124320068801783)
  ·
    refine ⟨41526858883686480103202675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27684572589124320068801783 41526858883686480103202675)
    ·
      refine ⟨62290288325529720154804013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41526858883686480103202675 62290288325529720154804013)
      ·
        refine ⟨23358858122073645058051505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62290288325529720154804013 23358858122073645058051505)
        ·
          refine ⟨17519143591555233793538629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23358858122073645058051505 17519143591555233793538629)
          ·
            refine ⟨3284839423416606336288493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17519143591555233793538629 3284839423416606336288493)
            ·
              refine ⟨1231814783781227376108185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3284839423416606336288493 1231814783781227376108185)
              ·
                refine ⟨923861087835920532081139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231814783781227376108185 923861087835920532081139)
                ·
                  refine ⟨1385791631753880798121709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923861087835920532081139 1385791631753880798121709)
                  ·
                    refine ⟨519671861907705299295641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385791631753880798121709 519671861907705299295641)
                    ·
                      refine ⟨389753896430778974471731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519671861907705299295641 389753896430778974471731)
                      ·
                        rfl

theorem cell23_759043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_759043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759043 prefixEnd_759043 := by exact prefixLift 759043
  have htrace : WordTrace (prefixWord ++ tailWord_759043) baseStart_759043 baseEnd_759043 := by
    simpa [prefixWord, tailWord_759043, baseEnd_759043] using wordTrace_append hprefix tailTrace_759043
  have hstable : (prefixWord ++ tailWord_759043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759043).length < 2 ^ (prefixWord ++ tailWord_759043).sum := by decide
  have hdescent : baseEnd_759043 < baseStart_759043 := by decide
  rcases family_descends (prefixWord ++ tailWord_759043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759090 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_759090 : Nat := 118140960795 + 759090 * 2 ^ 59
def prefixEnd_759090 : Nat := 4983230072969 + 3 ^ 40 * 759090 * 2
def baseEnd_759090 : Nat := 389778030021540290584015

theorem tailTrace_759090 : CollatzResearch.WordTrace tailWord_759090 prefixEnd_759090 389778030021540290584015 := by
  unfold tailWord_759090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921571704988511773940681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18457524546636031397175149 6921571704988511773940681)
  ·
    refine ⟨5191178778741383830455511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6921571704988511773940681 5191178778741383830455511)
    ·
      refine ⟨7786768168112075745683267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5191178778741383830455511 7786768168112075745683267)
      ·
        refine ⟨11680152252168113618524901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7786768168112075745683267 11680152252168113618524901)
        ·
          refine ⟨2190028547281521303473419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11680152252168113618524901 2190028547281521303473419)
          ·
            refine ⟨3285042820922281955210129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190028547281521303473419 3285042820922281955210129)
            ·
              refine ⟨2463782115691711466407597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285042820922281955210129 2463782115691711466407597)
              ·
                refine ⟨923918293384391799902849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2463782115691711466407597 923918293384391799902849)
                ·
                  refine ⟨692938720038293849927137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 923918293384391799902849 692938720038293849927137)
                  ·
                    refine ⟨519704040028720387445353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 692938720038293849927137 519704040028720387445353)
                    ·
                      refine ⟨389778030021540290584015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519704040028720387445353 389778030021540290584015)
                      ·
                        rfl

theorem cell23_759090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_759090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759090 prefixEnd_759090 := by exact prefixLift 759090
  have htrace : WordTrace (prefixWord ++ tailWord_759090) baseStart_759090 baseEnd_759090 := by
    simpa [prefixWord, tailWord_759090, baseEnd_759090] using wordTrace_append hprefix tailTrace_759090
  have hstable : (prefixWord ++ tailWord_759090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759090).length < 2 ^ (prefixWord ++ tailWord_759090).sum := by decide
  have hdescent : baseEnd_759090 < baseStart_759090 := by decide
  rcases family_descends (prefixWord ++ tailWord_759090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759159 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_759159 : Nat := 118140960795 + 759159 * 2 ^ 59
def prefixEnd_759159 : Nat := 4983230072969 + 3 ^ 40 * 759159 * 2
def baseEnd_759159 : Nat := 389813460186700520621197

theorem tailTrace_759159 : CollatzResearch.WordTrace tailWord_759159 prefixEnd_759159 389813460186700520621197 := by
  unfold tailWord_759159
  simp only [CollatzResearch.WordTrace]
  refine ⟨27688803456704071880024531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18459202304469381253349687 27688803456704071880024531)
  ·
    refine ⟨41533205185056107820036797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27688803456704071880024531 41533205185056107820036797)
    ·
      refine ⟨15574951944396040432513799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41533205185056107820036797 15574951944396040432513799)
      ·
        refine ⟨23362427916594060648770699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15574951944396040432513799 23362427916594060648770699)
        ·
          refine ⟨35043641874891090973156049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23362427916594060648770699 35043641874891090973156049)
          ·
            refine ⟨26282731406168318229867037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35043641874891090973156049 26282731406168318229867037)
            ·
              refine ⟨9856024277313119336200139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26282731406168318229867037 9856024277313119336200139)
              ·
                refine ⟨14784036415969679004300209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9856024277313119336200139 14784036415969679004300209)
                ·
                  refine ⟨11088027311977259253225157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14784036415969679004300209 11088027311977259253225157)
                  ·
                    refine ⟨2079005120995736109979717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11088027311977259253225157 2079005120995736109979717)
                    ·
                      refine ⟨389813460186700520621197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2079005120995736109979717 389813460186700520621197)
                      ·
                        rfl

theorem cell23_759159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_759159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759159 prefixEnd_759159 := by exact prefixLift 759159
  have htrace : WordTrace (prefixWord ++ tailWord_759159) baseStart_759159 baseEnd_759159 := by
    simpa [prefixWord, tailWord_759159, baseEnd_759159] using wordTrace_append hprefix tailTrace_759159
  have hstable : (prefixWord ++ tailWord_759159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759159).length < 2 ^ (prefixWord ++ tailWord_759159).sum := by decide
  have hdescent : baseEnd_759159 < baseStart_759159 := by decide
  rcases family_descends (prefixWord ++ tailWord_759159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759189 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_759189 : Nat := 118140960795 + 759189 * 2 ^ 59
def prefixEnd_759189 : Nat := 4983230072969 + 3 ^ 40 * 759189 * 2
def baseEnd_759189 : Nat := 389828864606335403246059

theorem tailTrace_759189 : CollatzResearch.WordTrace tailWord_759189 prefixEnd_759189 389828864606335403246059 := by
  unfold tailWord_759189
  simp only [CollatzResearch.WordTrace]
  refine ⟨27689897646595387003616621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18459931764396924669077747 27689897646595387003616621)
  ·
    refine ⟨10383711617473270126356233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27689897646595387003616621 10383711617473270126356233)
    ·
      refine ⟨7787783713104952594767175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10383711617473270126356233 7787783713104952594767175)
      ·
        refine ⟨11681675569657428892150763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7787783713104952594767175 11681675569657428892150763)
        ·
          refine ⟨17522513354486143338226145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11681675569657428892150763 17522513354486143338226145)
          ·
            refine ⟨13141885015864607503669609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17522513354486143338226145 13141885015864607503669609)
            ·
              refine ⟨9856413761898455627752207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13141885015864607503669609 9856413761898455627752207)
              ·
                refine ⟨14784620642847683441628311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9856413761898455627752207 14784620642847683441628311)
                ·
                  refine ⟨22176930964271525162442467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14784620642847683441628311 22176930964271525162442467)
                  ·
                    refine ⟨33265396446407287743663701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22176930964271525162442467 33265396446407287743663701)
                    ·
                      refine ⟨389828864606335403246059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 33265396446407287743663701 389828864606335403246059)
                      ·
                        rfl

theorem cell23_759189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_759189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759189 prefixEnd_759189 := by exact prefixLift 759189
  have htrace : WordTrace (prefixWord ++ tailWord_759189) baseStart_759189 baseEnd_759189 := by
    simpa [prefixWord, tailWord_759189, baseEnd_759189] using wordTrace_append hprefix tailTrace_759189
  have hstable : (prefixWord ++ tailWord_759189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759189).length < 2 ^ (prefixWord ++ tailWord_759189).sum := by decide
  have hdescent : baseEnd_759189 < baseStart_759189 := by decide
  rcases family_descends (prefixWord ++ tailWord_759189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759216 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 1, 5]
def baseStart_759216 : Nat := 118140960795 + 759216 * 2 ^ 59
def prefixEnd_759216 : Nat := 4983230072969 + 3 ^ 40 * 759216 * 2
def baseEnd_759216 : Nat := 129947576194668932536145

theorem tailTrace_759216 : CollatzResearch.WordTrace tailWord_759216 prefixEnd_759216 129947576194668932536145 := by
  unfold tailWord_759216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845441208748785307424751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18460588278331713743233001 13845441208748785307424751)
  ·
    refine ⟨20768161813123177961137127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13845441208748785307424751 20768161813123177961137127)
    ·
      refine ⟨31152242719684766941705691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20768161813123177961137127 31152242719684766941705691)
      ·
        refine ⟨46728364079527150412558537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31152242719684766941705691 46728364079527150412558537)
        ·
          refine ⟨35046273059645362809418903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46728364079527150412558537 35046273059645362809418903)
          ·
            refine ⟨52569409589468044214128355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35046273059645362809418903 52569409589468044214128355)
            ·
              refine ⟨78854114384202066321192533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52569409589468044214128355 78854114384202066321192533)
              ·
                refine ⟨924071652939867964701475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 78854114384202066321192533 924071652939867964701475)
                ·
                  refine ⟨1386107479409801947052213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924071652939867964701475 1386107479409801947052213)
                  ·
                    refine ⟨129947576194668932536145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1386107479409801947052213 129947576194668932536145)
                    ·
                      rfl

theorem cell23_759216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 5].length) (baseStart_759216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759216 prefixEnd_759216 := by exact prefixLift 759216
  have htrace : WordTrace (prefixWord ++ tailWord_759216) baseStart_759216 baseEnd_759216 := by
    simpa [prefixWord, tailWord_759216, baseEnd_759216] using wordTrace_append hprefix tailTrace_759216
  have hstable : (prefixWord ++ tailWord_759216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759216).length < 2 ^ (prefixWord ++ tailWord_759216).sum := by decide
  have hdescent : baseEnd_759216 < baseStart_759216 := by decide
  rcases family_descends (prefixWord ++ tailWord_759216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759247 : List Nat := [1, 1, 2, 1, 1, 4, 6, 2, 1, 1, 3]
def baseStart_759247 : Nat := 118140960795 + 759247 * 2 ^ 59
def prefixEnd_759247 : Nat := 4983230072969 + 3 ^ 40 * 759247 * 2
def baseEnd_759247 : Nat := 389858646484296176320793

theorem tailTrace_759247 : CollatzResearch.WordTrace tailWord_759247 prefixEnd_759247 389858646484296176320793 := by
  unfold tailWord_759247
  simp only [CollatzResearch.WordTrace]
  refine ⟨27692013080385262909227995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18461342053590175272818663 27692013080385262909227995)
  ·
    refine ⟨41538019620577894363841993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27692013080385262909227995 41538019620577894363841993)
    ·
      refine ⟨31153514715433420772881495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41538019620577894363841993 31153514715433420772881495)
      ·
        refine ⟨46730272073150131159322243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31153514715433420772881495 46730272073150131159322243)
        ·
          refine ⟨70095408109725196738983365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46730272073150131159322243 70095408109725196738983365)
          ·
            refine ⟨13142889020573474388559381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70095408109725196738983365 13142889020573474388559381)
            ·
              refine ⟨616072922839381611963721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13142889020573474388559381 616072922839381611963721)
              ·
                refine ⟨462054692129536208972791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616072922839381611963721 462054692129536208972791)
                ·
                  refine ⟨693082038194304313459187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462054692129536208972791 693082038194304313459187)
                  ·
                    refine ⟨1039623057291456470188781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 693082038194304313459187 1039623057291456470188781)
                    ·
                      refine ⟨389858646484296176320793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1039623057291456470188781 389858646484296176320793)
                      ·
                        rfl

theorem cell23_759247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 1, 3].length) (baseStart_759247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759247 prefixEnd_759247 := by exact prefixLift 759247
  have htrace : WordTrace (prefixWord ++ tailWord_759247) baseStart_759247 baseEnd_759247 := by
    simpa [prefixWord, tailWord_759247, baseEnd_759247] using wordTrace_append hprefix tailTrace_759247
  have hstable : (prefixWord ++ tailWord_759247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759247).length < 2 ^ (prefixWord ++ tailWord_759247).sum := by decide
  have hdescent : baseEnd_759247 < baseStart_759247 := by decide
  rcases family_descends (prefixWord ++ tailWord_759247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759256 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_759256 : Nat := 118140960795 + 759256 * 2 ^ 59
def prefixEnd_759256 : Nat := 4983230072969 + 3 ^ 40 * 759256 * 2
def baseEnd_759256 : Nat := 389863267810186641108251

theorem tailTrace_759256 : CollatzResearch.WordTrace tailWord_759256 prefixEnd_759256 389863267810186641108251 := by
  unfold tailWord_759256
  simp only [CollatzResearch.WordTrace]
  refine ⟨13846170668676328723152811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18461560891568438297537081 13846170668676328723152811)
  ·
    refine ⟨20769256003014493084729217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13846170668676328723152811 20769256003014493084729217)
    ·
      refine ⟨15576942002260869813546913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20769256003014493084729217 15576942002260869813546913)
      ·
        refine ⟨11682706501695652360160185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15576942002260869813546913 11682706501695652360160185)
        ·
          refine ⟨8762029876271739270120139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11682706501695652360160185 8762029876271739270120139)
          ·
            refine ⟨13143044814407608905180209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762029876271739270120139 13143044814407608905180209)
            ·
              refine ⟨9857283610805706678885157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13143044814407608905180209 9857283610805706678885157)
              ·
                refine ⟨1848240677026070002290967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9857283610805706678885157 1848240677026070002290967)
                ·
                  refine ⟨2772361015539105003436451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848240677026070002290967 2772361015539105003436451)
                  ·
                    refine ⟨4158541523308657505154677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2772361015539105003436451 4158541523308657505154677)
                    ·
                      refine ⟨389863267810186641108251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4158541523308657505154677 389863267810186641108251)
                      ·
                        rfl

theorem cell23_759256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_759256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759256 prefixEnd_759256 := by exact prefixLift 759256
  have htrace : WordTrace (prefixWord ++ tailWord_759256) baseStart_759256 baseEnd_759256 := by
    simpa [prefixWord, tailWord_759256, baseEnd_759256] using wordTrace_append hprefix tailTrace_759256
  have hstable : (prefixWord ++ tailWord_759256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759256).length < 2 ^ (prefixWord ++ tailWord_759256).sum := by decide
  have hdescent : baseEnd_759256 < baseStart_759256 := by decide
  rcases family_descends (prefixWord ++ tailWord_759256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759263 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 2, 4]
def baseStart_759263 : Nat := 118140960795 + 759263 * 2 ^ 59
def prefixEnd_759263 : Nat := 4983230072969 + 3 ^ 40 * 759263 * 2
def baseEnd_759263 : Nat := 129955620724922704573573

theorem tailTrace_759263 : CollatzResearch.WordTrace tailWord_759263 prefixEnd_759263 129955620724922704573573 := by
  unfold tailWord_759263
  simp only [CollatzResearch.WordTrace]
  refine ⟨27692596648327297641810443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18461731098884865094540295 27692596648327297641810443)
  ·
    refine ⟨41538894972490946462715665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27692596648327297641810443 41538894972490946462715665)
    ·
      refine ⟨31154171229368209847036749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41538894972490946462715665 31154171229368209847036749)
      ·
        refine ⟨11682814211013078692638781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31154171229368209847036749 11682814211013078692638781)
        ·
          refine ⟨4381055329129904509739543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11682814211013078692638781 4381055329129904509739543)
          ·
            refine ⟨6571582993694856764609315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381055329129904509739543 6571582993694856764609315)
            ·
              refine ⟨9857374490542285146913973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6571582993694856764609315 9857374490542285146913973)
              ·
                refine ⟨924128858488339232523185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9857374490542285146913973 924128858488339232523185)
                ·
                  refine ⟨693096643866254424392389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 924128858488339232523185 693096643866254424392389)
                  ·
                    refine ⟨129955620724922704573573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 693096643866254424392389 129955620724922704573573)
                    ·
                      rfl

theorem cell23_759263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 4].length) (baseStart_759263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759263 prefixEnd_759263 := by exact prefixLift 759263
  have htrace : WordTrace (prefixWord ++ tailWord_759263) baseStart_759263 baseEnd_759263 := by
    simpa [prefixWord, tailWord_759263, baseEnd_759263] using wordTrace_append hprefix tailTrace_759263
  have hstable : (prefixWord ++ tailWord_759263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759263).length < 2 ^ (prefixWord ++ tailWord_759263).sum := by decide
  have hdescent : baseEnd_759263 < baseStart_759263 := by decide
  rcases family_descends (prefixWord ++ tailWord_759263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759274 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_759274 : Nat := 118140960795 + 759274 * 2 ^ 59
def prefixEnd_759274 : Nat := 4983230072969 + 3 ^ 40 * 759274 * 2
def baseEnd_759274 : Nat := 389872510461967570683169

theorem tailTrace_759274 : CollatzResearch.WordTrace tailWord_759274 prefixEnd_759274 389872510461967570683169 := by
  unfold tailWord_759274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923249462821861630115219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18461998567524964346973917 6923249462821861630115219)
  ·
    refine ⟨10384874194232792445172829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6923249462821861630115219 10384874194232792445172829)
    ·
      refine ⟨3894327822837297166939811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10384874194232792445172829 3894327822837297166939811)
      ·
        refine ⟨5841491734255945750409717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894327822837297166939811 5841491734255945750409717)
        ·
          refine ⟨547639850086494914100911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5841491734255945750409717 547639850086494914100911)
          ·
            refine ⟨821459775129742371151367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547639850086494914100911 821459775129742371151367)
            ·
              refine ⟨1232189662694613556727051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821459775129742371151367 1232189662694613556727051)
              ·
                refine ⟨1848284494041920335090577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232189662694613556727051 1848284494041920335090577)
                ·
                  refine ⟨1386213370531440251317933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1848284494041920335090577 1386213370531440251317933)
                  ·
                    refine ⟨519830013949290094244225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386213370531440251317933 519830013949290094244225)
                    ·
                      refine ⟨389872510461967570683169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519830013949290094244225 389872510461967570683169)
                      ·
                        rfl

theorem cell23_759274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_759274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759274 prefixEnd_759274 := by exact prefixLift 759274
  have htrace : WordTrace (prefixWord ++ tailWord_759274) baseStart_759274 baseEnd_759274 := by
    simpa [prefixWord, tailWord_759274, baseEnd_759274] using wordTrace_append hprefix tailTrace_759274
  have hstable : (prefixWord ++ tailWord_759274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759274).length < 2 ^ (prefixWord ++ tailWord_759274).sum := by decide
  have hdescent : baseEnd_759274 < baseStart_759274 := by decide
  rcases family_descends (prefixWord ++ tailWord_759274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759297 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 2, 4]
def baseStart_759297 : Nat := 118140960795 + 759297 * 2 ^ 59
def prefixEnd_759297 : Nat := 4983230072969 + 3 ^ 40 * 759297 * 2
def baseEnd_759297 : Nat := 129961440172340326898521

theorem tailTrace_759297 : CollatzResearch.WordTrace tailWord_759297 prefixEnd_759297 129961440172340326898521 := by
  unfold tailWord_759297
  simp only [CollatzResearch.WordTrace]
  refine ⟨27693836730204121448548145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18462557820136080965698763 27693836730204121448548145)
  ·
    refine ⟨20770377547653091086411109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27693836730204121448548145 20770377547653091086411109)
    ·
      refine ⟨3894445790184954578702083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20770377547653091086411109 3894445790184954578702083)
      ·
        refine ⟨5841668685277431868053125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894445790184954578702083 5841668685277431868053125)
        ·
          refine ⟨1095312878489518475259961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5841668685277431868053125 1095312878489518475259961)
          ·
            refine ⟨821484658867138856444971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095312878489518475259961 821484658867138856444971)
            ·
              refine ⟨1232226988300708284667457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821484658867138856444971 1232226988300708284667457)
              ·
                refine ⟨924170241225531213500593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232226988300708284667457 924170241225531213500593)
                ·
                  refine ⟨693127680919148410125445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 924170241225531213500593 693127680919148410125445)
                  ·
                    refine ⟨129961440172340326898521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 693127680919148410125445 129961440172340326898521)
                    ·
                      rfl

theorem cell23_759297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_759297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759297 prefixEnd_759297 := by exact prefixLift 759297
  have htrace : WordTrace (prefixWord ++ tailWord_759297) baseStart_759297 baseEnd_759297 := by
    simpa [prefixWord, tailWord_759297, baseEnd_759297] using wordTrace_append hprefix tailTrace_759297
  have hstable : (prefixWord ++ tailWord_759297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759297).length < 2 ^ (prefixWord ++ tailWord_759297).sum := by decide
  have hdescent : baseEnd_759297 < baseStart_759297 := by decide
  rcases family_descends (prefixWord ++ tailWord_759297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759330 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_759330 : Nat := 118140960795 + 759330 * 2 ^ 59
def prefixEnd_759330 : Nat := 4983230072969 + 3 ^ 40 * 759330 * 2
def baseEnd_759330 : Nat := 389901265378619351582911

theorem tailTrace_759330 : CollatzResearch.WordTrace tailWord_759330 prefixEnd_759330 389901265378619351582911 := by
  unfold tailWord_759330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923760084771142021124861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18463360226056378722999629 6923760084771142021124861)
  ·
    refine ⟨2596410031789178257921823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6923760084771142021124861 2596410031789178257921823)
    ·
      refine ⟨3894615047683767386882735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2596410031789178257921823 3894615047683767386882735)
      ·
        refine ⟨5841922571525651080324103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894615047683767386882735 5841922571525651080324103)
        ·
          refine ⟨8762883857288476620486155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841922571525651080324103 8762883857288476620486155)
          ·
            refine ⟨13144325785932714930729233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762883857288476620486155 13144325785932714930729233)
            ·
              refine ⟨9858244339449536198046925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13144325785932714930729233 9858244339449536198046925)
              ·
                refine ⟨3696841627293576074267597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9858244339449536198046925 3696841627293576074267597)
                ·
                  refine ⟨1386315610235091027850349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3696841627293576074267597 1386315610235091027850349)
                  ·
                    refine ⟨519868353838159135443881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386315610235091027850349 519868353838159135443881)
                    ·
                      refine ⟨389901265378619351582911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519868353838159135443881 389901265378619351582911)
                      ·
                        rfl

theorem cell23_759330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_759330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759330 prefixEnd_759330 := by exact prefixLift 759330
  have htrace : WordTrace (prefixWord ++ tailWord_759330) baseStart_759330 baseEnd_759330 := by
    simpa [prefixWord, tailWord_759330, baseEnd_759330] using wordTrace_append hprefix tailTrace_759330
  have hstable : (prefixWord ++ tailWord_759330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759330).length < 2 ^ (prefixWord ++ tailWord_759330).sum := by decide
  have hdescent : baseEnd_759330 < baseStart_759330 := by decide
  rcases family_descends (prefixWord ++ tailWord_759330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759377 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 2, 2, 2]
def baseStart_759377 : Nat := 118140960795 + 759377 * 2 ^ 59
def prefixEnd_759377 : Nat := 4983230072969 + 3 ^ 40 * 759377 * 2
def baseEnd_759377 : Nat := 389925398969380667695195

theorem tailTrace_759377 : CollatzResearch.WordTrace tailWord_759377 prefixEnd_759377 389925398969380667695195 := by
  unfold tailWord_759377
  simp only [CollatzResearch.WordTrace]
  refine ⟨27696754569914295111460385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18464503046609530074306923 27696754569914295111460385)
  ·
    refine ⟨20772565927435721333595289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27696754569914295111460385 20772565927435721333595289)
    ·
      refine ⟨15579424445576791000196467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20772565927435721333595289 15579424445576791000196467)
      ·
        refine ⟨23369136668365186500294701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15579424445576791000196467 23369136668365186500294701)
        ·
          refine ⟨8763426250636944937610513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23369136668365186500294701 8763426250636944937610513)
          ·
            refine ⟨6572569687977708703207885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8763426250636944937610513 6572569687977708703207885)
            ·
              refine ⟨2464713632991640763702957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6572569687977708703207885 2464713632991640763702957)
              ·
                refine ⟨924267612371865286388609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2464713632991640763702957 924267612371865286388609)
                ·
                  refine ⟨693200709278898964791457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 924267612371865286388609 693200709278898964791457)
                  ·
                    refine ⟨519900531959174223593593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 693200709278898964791457 519900531959174223593593)
                    ·
                      refine ⟨389925398969380667695195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 519900531959174223593593 389925398969380667695195)
                      ·
                        rfl

theorem cell23_759377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_759377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759377 prefixEnd_759377 := by exact prefixLift 759377
  have htrace : WordTrace (prefixWord ++ tailWord_759377) baseStart_759377 baseEnd_759377 := by
    simpa [prefixWord, tailWord_759377, baseEnd_759377] using wordTrace_append hprefix tailTrace_759377
  have hstable : (prefixWord ++ tailWord_759377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759377).length < 2 ^ (prefixWord ++ tailWord_759377).sum := by decide
  have hdescent : baseEnd_759377 < baseStart_759377 := by decide
  rcases family_descends (prefixWord ++ tailWord_759377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759386 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_759386 : Nat := 118140960795 + 759386 * 2 ^ 59
def prefixEnd_759386 : Nat := 4983230072969 + 3 ^ 40 * 759386 * 2
def baseEnd_759386 : Nat := 389930020295271132482653

theorem tailTrace_759386 : CollatzResearch.WordTrace tailWord_759386 prefixEnd_759386 389930020295271132482653 := by
  unfold tailWord_759386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6924270706720422412134503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18464721884587793099025341 6924270706720422412134503)
  ·
    refine ⟨10386406060080633618201755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6924270706720422412134503 10386406060080633618201755)
    ·
      refine ⟨15579609090120950427302633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10386406060080633618201755 15579609090120950427302633)
      ·
        refine ⟨11684706817590712820476975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15579609090120950427302633 11684706817590712820476975)
        ·
          refine ⟨17527060226386069230715463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11684706817590712820476975 17527060226386069230715463)
          ·
            refine ⟨26290590339579103846073195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17527060226386069230715463 26290590339579103846073195)
            ·
              refine ⟨39435885509368655769109793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26290590339579103846073195 39435885509368655769109793)
              ·
                refine ⟨29576914132026491826832345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39435885509368655769109793 29576914132026491826832345)
                ·
                  refine ⟨22182685599019868870124259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29576914132026491826832345 22182685599019868870124259)
                  ·
                    refine ⟨33274028398529803305186389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22182685599019868870124259 33274028398529803305186389)
                    ·
                      refine ⟨389930020295271132482653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 33274028398529803305186389 389930020295271132482653)
                      ·
                        rfl

theorem cell23_759386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_759386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759386 prefixEnd_759386 := by exact prefixLift 759386
  have htrace : WordTrace (prefixWord ++ tailWord_759386) baseStart_759386 baseEnd_759386 := by
    simpa [prefixWord, tailWord_759386, baseEnd_759386] using wordTrace_append hprefix tailTrace_759386
  have hstable : (prefixWord ++ tailWord_759386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759386).length < 2 ^ (prefixWord ++ tailWord_759386).sum := by decide
  have hdescent : baseEnd_759386 < baseStart_759386 := by decide
  rcases family_descends (prefixWord ++ tailWord_759386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759416 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_759416 : Nat := 118140960795 + 759416 * 2 ^ 59
def prefixEnd_759416 : Nat := 4983230072969 + 3 ^ 40 * 759416 * 2
def baseEnd_759416 : Nat := 389945424714906015107515

theorem tailTrace_759416 : CollatzResearch.WordTrace tailWord_759416 prefixEnd_759416 389945424714906015107515 := by
  unfold tailWord_759416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13849088508386502386065051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18465451344515336514753401 13849088508386502386065051)
  ·
    refine ⟨20773632762579753579097577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13849088508386502386065051 20773632762579753579097577)
    ·
      refine ⟨15580224571934815184323183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20773632762579753579097577 15580224571934815184323183)
      ·
        refine ⟨23370336857902222776484775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15580224571934815184323183 23370336857902222776484775)
        ·
          refine ⟨35055505286853334164727163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23370336857902222776484775 35055505286853334164727163)
          ·
            refine ⟨52583257930280001247090745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35055505286853334164727163 52583257930280001247090745)
            ·
              refine ⟨39437443447710000935318059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52583257930280001247090745 39437443447710000935318059)
              ·
                refine ⟨59156165171565001402977089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39437443447710000935318059 59156165171565001402977089)
                ·
                  refine ⟨44367123878673751052232817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59156165171565001402977089 44367123878673751052232817)
                  ·
                    refine ⟨33275342909005313289174613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44367123878673751052232817 33275342909005313289174613)
                    ·
                      refine ⟨389945424714906015107515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 33275342909005313289174613 389945424714906015107515)
                      ·
                        rfl

theorem cell23_759416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_759416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759416 prefixEnd_759416 := by exact prefixLift 759416
  have htrace : WordTrace (prefixWord ++ tailWord_759416) baseStart_759416 baseEnd_759416 := by
    simpa [prefixWord, tailWord_759416, baseEnd_759416] using wordTrace_append hprefix tailTrace_759416
  have hstable : (prefixWord ++ tailWord_759416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759416).length < 2 ^ (prefixWord ++ tailWord_759416).sum := by decide
  have hdescent : baseEnd_759416 < baseStart_759416 := by decide
  rcases family_descends (prefixWord ++ tailWord_759416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759433 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_759433 : Nat := 118140960795 + 759433 * 2 ^ 59
def prefixEnd_759433 : Nat := 4983230072969 + 3 ^ 40 * 759433 * 2
def baseEnd_759433 : Nat := 389954153886032448594937

theorem tailTrace_759433 : CollatzResearch.WordTrace tailWord_759433 prefixEnd_759433 389954153886032448594937 := by
  unfold tailWord_759433
  simp only [CollatzResearch.WordTrace]
  refine ⟨27698797057711416675498953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18465864705140944450332635 27698797057711416675498953)
  ·
    refine ⟨20774097793283562506624215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27698797057711416675498953 20774097793283562506624215)
    ·
      refine ⟨31161146689925343759936323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20774097793283562506624215 31161146689925343759936323)
      ·
        refine ⟨46741720034888015639904485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31161146689925343759936323 46741720034888015639904485)
        ·
          refine ⟨8764072506541502932482091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46741720034888015639904485 8764072506541502932482091)
          ·
            refine ⟨13146108759812254398723137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8764072506541502932482091 13146108759812254398723137)
            ·
              refine ⟨9859581569859190799042353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13146108759812254398723137 9859581569859190799042353)
              ·
                refine ⟨7394686177394393099281765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9859581569859190799042353 7394686177394393099281765)
                ·
                  refine ⟨1386503658261448706115331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7394686177394393099281765 1386503658261448706115331)
                  ·
                    refine ⟨2079755487392173059172997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1386503658261448706115331 2079755487392173059172997)
                    ·
                      refine ⟨389954153886032448594937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2079755487392173059172997 389954153886032448594937)
                      ·
                        rfl

theorem cell23_759433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_759433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759433 prefixEnd_759433 := by exact prefixLift 759433
  have htrace : WordTrace (prefixWord ++ tailWord_759433) baseStart_759433 baseEnd_759433 := by
    simpa [prefixWord, tailWord_759433, baseEnd_759433] using wordTrace_append hprefix tailTrace_759433
  have hstable : (prefixWord ++ tailWord_759433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759433).length < 2 ^ (prefixWord ++ tailWord_759433).sum := by decide
  have hdescent : baseEnd_759433 < baseStart_759433 := by decide
  rcases family_descends (prefixWord ++ tailWord_759433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759503 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 3, 5]
def baseStart_759503 : Nat := 118140960795 + 759503 * 2 ^ 59
def prefixEnd_759503 : Nat := 4983230072969 + 3 ^ 40 * 759503 * 2
def baseEnd_759503 : Nat := 129996699177282391573205

theorem tailTrace_759503 : CollatzResearch.WordTrace tailWord_759503 prefixEnd_759503 129996699177282391573205 := by
  unfold tailWord_759503
  simp only [CollatzResearch.WordTrace]
  refine ⟨27701350167457818630547163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18467566778305212420364775 27701350167457818630547163)
  ·
    refine ⟨41552025251186727945820745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27701350167457818630547163 41552025251186727945820745)
    ·
      refine ⟨31164018938390045959365559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41552025251186727945820745 31164018938390045959365559)
      ·
        refine ⟨46746028407585068939048339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31164018938390045959365559 46746028407585068939048339)
        ·
          refine ⟨70119042611377603408572509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46746028407585068939048339 70119042611377603408572509)
          ·
            refine ⟨26294640979266601278214691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70119042611377603408572509 26294640979266601278214691)
            ·
              refine ⟨39441961468899901917322037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26294640979266601278214691 39441961468899901917322037)
              ·
                refine ⟨3697683887709365804748941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39441961468899901917322037 3697683887709365804748941)
                ·
                  refine ⟨1386631457891012176780853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3697683887709365804748941 1386631457891012176780853)
                  ·
                    refine ⟨129996699177282391573205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1386631457891012176780853 129996699177282391573205)
                    ·
                      rfl

theorem cell23_759503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_759503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759503 prefixEnd_759503 := by exact prefixLift 759503
  have htrace : WordTrace (prefixWord ++ tailWord_759503) baseStart_759503 baseEnd_759503 := by
    simpa [prefixWord, tailWord_759503, baseEnd_759503] using wordTrace_append hprefix tailTrace_759503
  have hstable : (prefixWord ++ tailWord_759503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759503).length < 2 ^ (prefixWord ++ tailWord_759503).sum := by decide
  have hdescent : baseEnd_759503 < baseStart_759503 := by decide
  rcases family_descends (prefixWord ++ tailWord_759503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759520 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 1, 5]
def baseStart_759520 : Nat := 118140960795 + 759520 * 2 ^ 59
def prefixEnd_759520 : Nat := 4983230072969 + 3 ^ 40 * 759520 * 2
def baseEnd_759520 : Nat := 129999608900991202735679

theorem tailTrace_759520 : CollatzResearch.WordTrace tailWord_759520 prefixEnd_759520 129999608900991202735679 := by
  unfold tailWord_759520
  simp only [CollatzResearch.WordTrace]
  refine ⟨13850985104198115266958007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18467980138930820355944009 13850985104198115266958007)
  ·
    refine ⟨20776477656297172900437011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13850985104198115266958007 20776477656297172900437011)
    ·
      refine ⟨31164716484445759350655517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20776477656297172900437011 31164716484445759350655517)
      ·
        refine ⟨11686768681667159756495819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31164716484445759350655517 11686768681667159756495819)
        ·
          refine ⟨17530153022500739634743729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11686768681667159756495819 17530153022500739634743729)
          ·
            refine ⟨13147614766875554726057797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17530153022500739634743729 13147614766875554726057797)
            ·
              refine ⟨2465177768789166511135837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13147614766875554726057797 2465177768789166511135837)
              ·
                refine ⟨924441663295937441675939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2465177768789166511135837 924441663295937441675939)
                ·
                  refine ⟨1386662494943906162513909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924441663295937441675939 1386662494943906162513909)
                  ·
                    refine ⟨129999608900991202735679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1386662494943906162513909 129999608900991202735679)
                    ·
                      rfl

theorem cell23_759520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 5].length) (baseStart_759520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759520 prefixEnd_759520 := by exact prefixLift 759520
  have htrace : WordTrace (prefixWord ++ tailWord_759520) baseStart_759520 baseEnd_759520 := by
    simpa [prefixWord, tailWord_759520, baseEnd_759520] using wordTrace_append hprefix tailTrace_759520
  have hstable : (prefixWord ++ tailWord_759520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759520).length < 2 ^ (prefixWord ++ tailWord_759520).sum := by decide
  have hdescent : baseEnd_759520 < baseStart_759520 := by decide
  rcases family_descends (prefixWord ++ tailWord_759520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759563 : List Nat := [1, 1, 1, 1, 5, 1, 4, 9]
def baseStart_759563 : Nat := 118140960795 + 759563 * 2 ^ 59
def prefixEnd_759563 : Nat := 4983230072969 + 3 ^ 40 * 759563 * 2
def baseEnd_759563 : Nat := 14445218754485812591457

theorem tailTrace_759563 : CollatzResearch.WordTrace tailWord_759563 prefixEnd_759563 14445218754485812591457 := by
  unfold tailWord_759563
  simp only [CollatzResearch.WordTrace]
  refine ⟨27703538547240448877731343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18469025698160299251820895 27703538547240448877731343)
  ·
    refine ⟨41555307820860673316597015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27703538547240448877731343 41555307820860673316597015)
    ·
      refine ⟨62332961731291009974895523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41555307820860673316597015 62332961731291009974895523)
      ·
        refine ⟨93499442596936514962343285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62332961731291009974895523 93499442596936514962343285)
        ·
          refine ⟨8765572743462798277719683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93499442596936514962343285 8765572743462798277719683)
          ·
            refine ⟨13148359115194197416579525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765572743462798277719683 13148359115194197416579525)
            ·
              refine ⟨2465317334098912015608661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13148359115194197416579525 2465317334098912015608661)
              ·
                refine ⟨14445218754485812591457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2465317334098912015608661 14445218754485812591457)
                ·
                  rfl

theorem cell23_759563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 9].length) (baseStart_759563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759563 prefixEnd_759563 := by exact prefixLift 759563
  have htrace : WordTrace (prefixWord ++ tailWord_759563) baseStart_759563 baseEnd_759563 := by
    simpa [prefixWord, tailWord_759563, baseEnd_759563] using wordTrace_append hprefix tailTrace_759563
  have hstable : (prefixWord ++ tailWord_759563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759563).length < 2 ^ (prefixWord ++ tailWord_759563).sum := by decide
  have hdescent : baseEnd_759563 < baseStart_759563 := by decide
  rcases family_descends (prefixWord ++ tailWord_759563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759604 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_759604 : Nat := 118140960795 + 759604 * 2 ^ 59
def prefixEnd_759604 : Nat := 4983230072969 + 3 ^ 40 * 759604 * 2
def baseEnd_759604 : Nat := 390041959077951279556651

theorem tailTrace_759604 : CollatzResearch.WordTrace tailWord_759604 prefixEnd_759604 390041959077951279556651 := by
  unfold tailWord_759604
  simp only [CollatzResearch.WordTrace]
  refine ⟨13852516970045956439986933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18470022626727941919982577 13852516970045956439986933)
  ·
    refine ⟨1298673465941808416248775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13852516970045956439986933 1298673465941808416248775)
    ·
      refine ⟨1948010198912712624373163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298673465941808416248775 1948010198912712624373163)
      ·
        refine ⟨2922015298369068936559745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948010198912712624373163 2922015298369068936559745)
        ·
          refine ⟨2191511473776801702419809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922015298369068936559745 2191511473776801702419809)
          ·
            refine ⟨1643633605332601276814857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2191511473776801702419809 1643633605332601276814857)
            ·
              refine ⟨1232725203999450957611143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1643633605332601276814857 1232725203999450957611143)
              ·
                refine ⟨1849087805999176436416715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232725203999450957611143 1849087805999176436416715)
                ·
                  refine ⟨2773631708998764654625073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849087805999176436416715 2773631708998764654625073)
                  ·
                    refine ⟨2080223781749073490968805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2773631708998764654625073 2080223781749073490968805)
                    ·
                      refine ⟨390041959077951279556651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2080223781749073490968805 390041959077951279556651)
                      ·
                        rfl

theorem cell23_759604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_759604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759604 prefixEnd_759604 := by exact prefixLift 759604
  have htrace : WordTrace (prefixWord ++ tailWord_759604) baseStart_759604 baseEnd_759604 := by
    simpa [prefixWord, tailWord_759604, baseEnd_759604] using wordTrace_append hprefix tailTrace_759604
  have hstable : (prefixWord ++ tailWord_759604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759604).length < 2 ^ (prefixWord ++ tailWord_759604).sum := by decide
  have hdescent : baseEnd_759604 < baseStart_759604 := by decide
  rcases family_descends (prefixWord ++ tailWord_759604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759628 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 1, 2, 3]
def baseStart_759628 : Nat := 118140960795 + 759628 * 2 ^ 59
def prefixEnd_759628 : Nat := 4983230072969 + 3 ^ 40 * 759628 * 2
def baseEnd_759628 : Nat := 390054282613659185656541

theorem tailTrace_759628 : CollatzResearch.WordTrace tailWord_759628 prefixEnd_759628 390054282613659185656541 := by
  unfold tailWord_759628
  simp only [CollatzResearch.WordTrace]
  refine ⟨13852954646002482489423769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18470606194669976652565025 13852954646002482489423769)
  ·
    refine ⟨10389715984501861867067827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13852954646002482489423769 10389715984501861867067827)
    ·
      refine ⟨15584573976752792800601741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10389715984501861867067827 15584573976752792800601741)
      ·
        refine ⟨5844215241282297300225653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15584573976752792800601741 5844215241282297300225653)
        ·
          refine ⟨547895178870215371896155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5844215241282297300225653 547895178870215371896155)
          ·
            refine ⟨821842768305323057844233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547895178870215371896155 821842768305323057844233)
            ·
              refine ⟨616382076228992293383175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821842768305323057844233 616382076228992293383175)
              ·
                refine ⟨924573114343488440074763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616382076228992293383175 924573114343488440074763)
                ·
                  refine ⟨1386859671515232660112145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924573114343488440074763 1386859671515232660112145)
                  ·
                    refine ⟨1040144753636424495084109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1386859671515232660112145 1040144753636424495084109)
                    ·
                      refine ⟨390054282613659185656541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1040144753636424495084109 390054282613659185656541)
                      ·
                        rfl

theorem cell23_759628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_759628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759628 prefixEnd_759628 := by exact prefixLift 759628
  have htrace : WordTrace (prefixWord ++ tailWord_759628) baseStart_759628 baseEnd_759628 := by
    simpa [prefixWord, tailWord_759628, baseEnd_759628] using wordTrace_append hprefix tailTrace_759628
  have hstable : (prefixWord ++ tailWord_759628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759628).length < 2 ^ (prefixWord ++ tailWord_759628).sum := by decide
  have hdescent : baseEnd_759628 < baseStart_759628 := by decide
  rcases family_descends (prefixWord ++ tailWord_759628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759658 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_759658 : Nat := 118140960795 + 759658 * 2 ^ 59
def prefixEnd_759658 : Nat := 4983230072969 + 3 ^ 40 * 759658 * 2
def baseEnd_759658 : Nat := 390069687033294068281403

theorem tailTrace_759658 : CollatzResearch.WordTrace tailWord_759658 prefixEnd_759658 390069687033294068281403 := by
  unfold tailWord_759658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6926750870474070025609907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18471335654597520068293085 6926750870474070025609907)
  ·
    refine ⟨10390126305711105038414861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6926750870474070025609907 10390126305711105038414861)
    ·
      refine ⟨3896297364641664389405573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10390126305711105038414861 3896297364641664389405573)
      ·
        refine ⟨730555755870312073013545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3896297364641664389405573 730555755870312073013545)
        ·
          refine ⟨547916816902734054760159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730555755870312073013545 547916816902734054760159)
          ·
            refine ⟨821875225354101082140239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547916816902734054760159 821875225354101082140239)
            ·
              refine ⟨1232812838031151623210359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821875225354101082140239 1232812838031151623210359)
              ·
                refine ⟨1849219257046727434815539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232812838031151623210359 1849219257046727434815539)
                ·
                  refine ⟨2773828885570091152223309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849219257046727434815539 2773828885570091152223309)
                  ·
                    refine ⟨1040185832088784182083741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773828885570091152223309 1040185832088784182083741)
                    ·
                      refine ⟨390069687033294068281403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1040185832088784182083741 390069687033294068281403)
                      ·
                        rfl

theorem cell23_759658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_759658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759658 prefixEnd_759658 := by exact prefixLift 759658
  have htrace : WordTrace (prefixWord ++ tailWord_759658) baseStart_759658 baseEnd_759658 := by
    simpa [prefixWord, tailWord_759658, baseEnd_759658] using wordTrace_append hprefix tailTrace_759658
  have hstable : (prefixWord ++ tailWord_759658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759658).length < 2 ^ (prefixWord ++ tailWord_759658).sum := by decide
  have hdescent : baseEnd_759658 < baseStart_759658 := by decide
  rcases family_descends (prefixWord ++ tailWord_759658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759730 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_759730 : Nat := 118140960795 + 759730 * 2 ^ 59
def prefixEnd_759730 : Nat := 4983230072969 + 3 ^ 40 * 759730 * 2
def baseEnd_759730 : Nat := 130035552546805928860357

theorem tailTrace_759730 : CollatzResearch.WordTrace tailWord_759730 prefixEnd_759730 130035552546805928860357 := by
  unfold tailWord_759730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6927407384408859099765161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18473086358423624266040429 6927407384408859099765161)
  ·
    refine ⟨5195555538306644324823871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6927407384408859099765161 5195555538306644324823871)
    ·
      refine ⟨7793333307459966487235807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5195555538306644324823871 7793333307459966487235807)
      ·
        refine ⟨11689999961189949730853711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7793333307459966487235807 11689999961189949730853711)
        ·
          refine ⟨17534999941784924596280567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11689999961189949730853711 17534999941784924596280567)
          ·
            refine ⟨26302499912677386894420851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17534999941784924596280567 26302499912677386894420851)
            ·
              refine ⟨39453749869016080341631277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26302499912677386894420851 39453749869016080341631277)
              ·
                refine ⟨14795156200881030128111729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39453749869016080341631277 14795156200881030128111729)
                ·
                  refine ⟨11096367150660772596083797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14795156200881030128111729 11096367150660772596083797)
                  ·
                    refine ⟨130035552546805928860357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11096367150660772596083797 130035552546805928860357)
                    ·
                      rfl

theorem cell23_759730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_759730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759730 prefixEnd_759730 := by exact prefixLift 759730
  have htrace : WordTrace (prefixWord ++ tailWord_759730) baseStart_759730 baseEnd_759730 := by
    simpa [prefixWord, tailWord_759730, baseEnd_759730] using wordTrace_append hprefix tailTrace_759730
  have hstable : (prefixWord ++ tailWord_759730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759730).length < 2 ^ (prefixWord ++ tailWord_759730).sum := by decide
  have hdescent : baseEnd_759730 < baseStart_759730 := by decide
  rcases family_descends (prefixWord ++ tailWord_759730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759760 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 8]
def baseStart_759760 : Nat := 118140960795 + 759760 * 2 ^ 59
def prefixEnd_759760 : Nat := 4983230072969 + 3 ^ 40 * 759760 * 2
def baseEnd_759760 : Nat := 43346895784450296578437

theorem tailTrace_759760 : CollatzResearch.WordTrace tailWord_759760 prefixEnd_759760 43346895784450296578437 := by
  unfold tailWord_759760
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855361863763375761326367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18473815818351167681768489 13855361863763375761326367)
  ·
    refine ⟨20783042795645063641989551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13855361863763375761326367 20783042795645063641989551)
    ·
      refine ⟨31174564193467595462984327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20783042795645063641989551 31174564193467595462984327)
      ·
        refine ⟨46761846290201393194476491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31174564193467595462984327 46761846290201393194476491)
        ·
          refine ⟨70142769435302089791714737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46761846290201393194476491 70142769435302089791714737)
          ·
            refine ⟨52607077076476567343786053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70142769435302089791714737 52607077076476567343786053)
            ·
              refine ⟨9863826951839356376959885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52607077076476567343786053 9863826951839356376959885)
              ·
                refine ⟨3698935106939758641359957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9863826951839356376959885 3698935106939758641359957)
                ·
                  refine ⟨43346895784450296578437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3698935106939758641359957 43346895784450296578437)
                  ·
                    rfl

theorem cell23_759760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 8].length) (baseStart_759760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759760 prefixEnd_759760 := by exact prefixLift 759760
  have htrace : WordTrace (prefixWord ++ tailWord_759760) baseStart_759760 baseEnd_759760 := by
    simpa [prefixWord, tailWord_759760, baseEnd_759760] using wordTrace_append hprefix tailTrace_759760
  have hstable : (prefixWord ++ tailWord_759760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759760).length < 2 ^ (prefixWord ++ tailWord_759760).sum := by decide
  have hdescent : baseEnd_759760 < baseStart_759760 := by decide
  rcases family_descends (prefixWord ++ tailWord_759760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759764 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_759764 : Nat := 118140960795 + 759764 * 2 ^ 59
def prefixEnd_759764 : Nat := 4983230072969 + 3 ^ 40 * 759764 * 2
def baseEnd_759764 : Nat := 130041371994223551185305

theorem tailTrace_759764 : CollatzResearch.WordTrace tailWord_759764 prefixEnd_759764 130041371994223551185305 := by
  unfold tailWord_759764
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855434809756130102899173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18473913079674840137198897 13855434809756130102899173)
  ·
    refine ⟨2597894026829274394293595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13855434809756130102899173 2597894026829274394293595)
    ·
      refine ⟨3896841040243911591440393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2597894026829274394293595 3896841040243911591440393)
      ·
        refine ⟨2922630780182933693580295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3896841040243911591440393 2922630780182933693580295)
        ·
          refine ⟨4383946170274400540370443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922630780182933693580295 4383946170274400540370443)
          ·
            refine ⟨6575919255411600810555665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383946170274400540370443 6575919255411600810555665)
            ·
              refine ⟨4931939441558700607916749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6575919255411600810555665 4931939441558700607916749)
              ·
                refine ⟨1849477290584512727968781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4931939441558700607916749 1849477290584512727968781)
                ·
                  refine ⟨693553983969192272988293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1849477290584512727968781 693553983969192272988293)
                  ·
                    refine ⟨130041371994223551185305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 693553983969192272988293 130041371994223551185305)
                    ·
                      rfl

theorem cell23_759764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_759764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759764 prefixEnd_759764 := by exact prefixLift 759764
  have htrace : WordTrace (prefixWord ++ tailWord_759764) baseStart_759764 baseEnd_759764 := by
    simpa [prefixWord, tailWord_759764, baseEnd_759764] using wordTrace_append hprefix tailTrace_759764
  have hstable : (prefixWord ++ tailWord_759764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759764).length < 2 ^ (prefixWord ++ tailWord_759764).sum := by decide
  have hdescent : baseEnd_759764 < baseStart_759764 := by decide
  rcases family_descends (prefixWord ++ tailWord_759764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759777 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 6]
def baseStart_759777 : Nat := 118140960795 + 759777 * 2 ^ 59
def prefixEnd_759777 : Nat := 4983230072969 + 3 ^ 40 * 759777 * 2
def baseEnd_759777 : Nat := 43347865692353233632595

theorem tailTrace_759777 : CollatzResearch.WordTrace tailWord_759777 prefixEnd_759777 43347865692353233632595 := by
  unfold tailWord_759777
  simp only [CollatzResearch.WordTrace]
  refine ⟨27711343768465163426021585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18474229178976775617347723 27711343768465163426021585)
  ·
    refine ⟨20783507826348872569516189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27711343768465163426021585 20783507826348872569516189)
    ·
      refine ⟨7793815434880827213568571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20783507826348872569516189 7793815434880827213568571)
      ·
        refine ⟨11690723152321240820352857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7793815434880827213568571 11690723152321240820352857)
        ·
          refine ⟨8768042364240930615264643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11690723152321240820352857 8768042364240930615264643)
          ·
            refine ⟨13152063546361395922896965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768042364240930615264643 13152063546361395922896965)
            ·
              refine ⟨2466011914942761735543181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13152063546361395922896965 2466011914942761735543181)
              ·
                refine ⟨924754468103535650828693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2466011914942761735543181 924754468103535650828693)
                ·
                  refine ⟨43347865692353233632595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 924754468103535650828693 43347865692353233632595)
                  ·
                    rfl

theorem cell23_759777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 6].length) (baseStart_759777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759777 prefixEnd_759777 := by exact prefixLift 759777
  have htrace : WordTrace (prefixWord ++ tailWord_759777) baseStart_759777 baseEnd_759777 := by
    simpa [prefixWord, tailWord_759777, baseEnd_759777] using wordTrace_append hprefix tailTrace_759777
  have hstable : (prefixWord ++ tailWord_759777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759777).length < 2 ^ (prefixWord ++ tailWord_759777).sum := by decide
  have hdescent : baseEnd_759777 < baseStart_759777 := by decide
  rcases family_descends (prefixWord ++ tailWord_759777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759804 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_759804 : Nat := 118140960795 + 759804 * 2 ^ 59
def prefixEnd_759804 : Nat := 4983230072969 + 3 ^ 40 * 759804 * 2
def baseEnd_759804 : Nat := 390144655208850497055731

theorem tailTrace_759804 : CollatzResearch.WordTrace tailWord_759804 prefixEnd_759804 390144655208850497055731 := by
  unfold tailWord_759804
  simp only [CollatzResearch.WordTrace]
  refine ⟨13856164269683673518627233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18474885692911564691502977 13856164269683673518627233)
  ·
    refine ⟨10392123202262755138970425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13856164269683673518627233 10392123202262755138970425)
    ·
      refine ⟨7794092401697066354227819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10392123202262755138970425 7794092401697066354227819)
      ·
        refine ⟨11691138602545599531341729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7794092401697066354227819 11691138602545599531341729)
        ·
          refine ⟨8768353951909199648506297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11691138602545599531341729 8768353951909199648506297)
          ·
            refine ⟨6576265463931899736379723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8768353951909199648506297 6576265463931899736379723)
            ·
              refine ⟨9864398195897849604569585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576265463931899736379723 9864398195897849604569585)
              ·
                refine ⟨7398298646923387203427189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9864398195897849604569585 7398298646923387203427189)
                ·
                  refine ⟨693590498149067550321299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7398298646923387203427189 693590498149067550321299)
                  ·
                    refine ⟨1040385747223601325481949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 693590498149067550321299 1040385747223601325481949)
                    ·
                      refine ⟨390144655208850497055731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1040385747223601325481949 390144655208850497055731)
                      ·
                        rfl

theorem cell23_759804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_759804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759804 prefixEnd_759804 := by exact prefixLift 759804
  have htrace : WordTrace (prefixWord ++ tailWord_759804) baseStart_759804 baseEnd_759804 := by
    simpa [prefixWord, tailWord_759804, baseEnd_759804] using wordTrace_append hprefix tailTrace_759804
  have hstable : (prefixWord ++ tailWord_759804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759804).length < 2 ^ (prefixWord ++ tailWord_759804).sum := by decide
  have hdescent : baseEnd_759804 < baseStart_759804 := by decide
  rcases family_descends (prefixWord ++ tailWord_759804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759827 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 4]
def baseStart_759827 : Nat := 118140960795 + 759827 * 2 ^ 59
def prefixEnd_759827 : Nat := 4983230072969 + 3 ^ 40 * 759827 * 2
def baseEnd_759827 : Nat := 390156465263903907068125

theorem tailTrace_759827 : CollatzResearch.WordTrace tailWord_759827 prefixEnd_759827 390156465263903907068125 := by
  unfold tailWord_759827
  simp only [CollatzResearch.WordTrace]
  refine ⟨27713167418284021965341735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18475444945522681310227823 27713167418284021965341735)
  ·
    refine ⟨41569751127426032948012603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27713167418284021965341735 41569751127426032948012603)
    ·
      refine ⟨62354626691139049422018905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41569751127426032948012603 62354626691139049422018905)
      ·
        refine ⟨46765970018354287066514179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62354626691139049422018905 46765970018354287066514179)
        ·
          refine ⟨70148955027531430599771269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46765970018354287066514179 70148955027531430599771269)
          ·
            refine ⟨13152929067662143237457113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70148955027531430599771269 13152929067662143237457113)
            ·
              refine ⟨9864696800746607428092835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13152929067662143237457113 9864696800746607428092835)
              ·
                refine ⟨14797045201119911142139253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9864696800746607428092835 14797045201119911142139253)
                ·
                  refine ⟨1387222987604991669575555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14797045201119911142139253 1387222987604991669575555)
                  ·
                    refine ⟨2080834481407487504363333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1387222987604991669575555 2080834481407487504363333)
                    ·
                      refine ⟨390156465263903907068125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2080834481407487504363333 390156465263903907068125)
                      ·
                        rfl

theorem cell23_759827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_759827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759827 prefixEnd_759827 := by exact prefixLift 759827
  have htrace : WordTrace (prefixWord ++ tailWord_759827) baseStart_759827 baseEnd_759827 := by
    simpa [prefixWord, tailWord_759827, baseEnd_759827] using wordTrace_append hprefix tailTrace_759827
  have hstable : (prefixWord ++ tailWord_759827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759827).length < 2 ^ (prefixWord ++ tailWord_759827).sum := by decide
  have hdescent : baseEnd_759827 < baseStart_759827 := by decide
  rcases family_descends (prefixWord ++ tailWord_759827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759841 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 1, 5]
def baseStart_759841 : Nat := 118140960795 + 759841 * 2 ^ 59
def prefixEnd_759841 : Nat := 4983230072969 + 3 ^ 40 * 759841 * 2
def baseEnd_759841 : Nat := 130054551331022284097687

theorem tailTrace_759841 : CollatzResearch.WordTrace tailWord_759841 prefixEnd_759841 130054551331022284097687 := by
  unfold tailWord_759841
  simp only [CollatzResearch.WordTrace]
  refine ⟨27713678040233302356351377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18475785360155534904234251 27713678040233302356351377)
  ·
    refine ⟨20785258530174976767263533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27713678040233302356351377 20785258530174976767263533)
    ·
      refine ⟨7794471948815616287723825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20785258530174976767263533 7794471948815616287723825)
      ·
        refine ⟨5845853961611712215792869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7794471948815616287723825 5845853961611712215792869)
        ·
          refine ⟨1096097617802196040461163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5845853961611712215792869 1096097617802196040461163)
          ·
            refine ⟨1644146426703294060691745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096097617802196040461163 1644146426703294060691745)
            ·
              refine ⟨1233109820027470545518809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644146426703294060691745 1233109820027470545518809)
              ·
                refine ⟨924832365020602909139107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1233109820027470545518809 924832365020602909139107)
                ·
                  refine ⟨1387248547530904363708661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924832365020602909139107 1387248547530904363708661)
                  ·
                    refine ⟨130054551331022284097687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1387248547530904363708661 130054551331022284097687)
                    ·
                      rfl

theorem cell23_759841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_759841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759841 prefixEnd_759841 := by exact prefixLift 759841
  have htrace : WordTrace (prefixWord ++ tailWord_759841) baseStart_759841 baseEnd_759841 := by
    simpa [prefixWord, tailWord_759841, baseEnd_759841] using wordTrace_append hprefix tailTrace_759841
  have hstable : (prefixWord ++ tailWord_759841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759841).length < 2 ^ (prefixWord ++ tailWord_759841).sum := by decide
  have hdescent : baseEnd_759841 < baseStart_759841 := by decide
  rcases family_descends (prefixWord ++ tailWord_759841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759861 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_759861 : Nat := 118140960795 + 759861 * 2 ^ 59
def prefixEnd_759861 : Nat := 4983230072969 + 3 ^ 40 * 759861 * 2
def baseEnd_759861 : Nat := 390173923606156774042969

theorem tailTrace_759861 : CollatzResearch.WordTrace tailWord_759861 prefixEnd_759861 390173923606156774042969 := by
  unfold tailWord_759861
  simp only [CollatzResearch.WordTrace]
  refine ⟨27714407500160845772079437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18476271666773897181386291 27714407500160845772079437)
  ·
    refine ⟨10392902812560317164529789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27714407500160845772079437 10392902812560317164529789)
    ·
      refine ⟨3897338554710118936698671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10392902812560317164529789 3897338554710118936698671)
      ·
        refine ⟨5846007832065178405048007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3897338554710118936698671 5846007832065178405048007)
        ·
          refine ⟨8769011748097767607572011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5846007832065178405048007 8769011748097767607572011)
          ·
            refine ⟨13153517622146651411358017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8769011748097767607572011 13153517622146651411358017)
            ·
              refine ⟨9865138216609988558518513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13153517622146651411358017 9865138216609988558518513)
              ·
                refine ⟨7398853662457491418888885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9865138216609988558518513 7398853662457491418888885)
                ·
                  refine ⟨693642530855389820520833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7398853662457491418888885 693642530855389820520833)
                  ·
                    refine ⟨520231898141542365390625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 693642530855389820520833 520231898141542365390625)
                    ·
                      refine ⟨390173923606156774042969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520231898141542365390625 390173923606156774042969)
                      ·
                        rfl

theorem cell23_759861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_759861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759861 prefixEnd_759861 := by exact prefixLift 759861
  have htrace : WordTrace (prefixWord ++ tailWord_759861) baseStart_759861 baseEnd_759861 := by
    simpa [prefixWord, tailWord_759861, baseEnd_759861] using wordTrace_append hprefix tailTrace_759861
  have hstable : (prefixWord ++ tailWord_759861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759861).length < 2 ^ (prefixWord ++ tailWord_759861).sum := by decide
  have hdescent : baseEnd_759861 < baseStart_759861 := by decide
  rcases family_descends (prefixWord ++ tailWord_759861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759907 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 5]
def baseStart_759907 : Nat := 118140960795 + 759907 * 2 ^ 59
def prefixEnd_759907 : Nat := 4983230072969 + 3 ^ 40 * 759907 * 2
def baseEnd_759907 : Nat := 390197543716263594067757

theorem tailTrace_759907 : CollatzResearch.WordTrace tailWord_759907 prefixEnd_759907 390197543716263594067757 := by
  unfold tailWord_759907
  simp only [CollatzResearch.WordTrace]
  refine ⟨27716085257994195628253975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18477390171996130418835983 27716085257994195628253975)
  ·
    refine ⟨41574127886991293442380963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27716085257994195628253975 41574127886991293442380963)
    ·
      refine ⟨62361191830486940163571445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41574127886991293442380963 62361191830486940163571445)
      ·
        refine ⟨5846361734108150640334823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62361191830486940163571445 5846361734108150640334823)
        ·
          refine ⟨8769542601162225960502235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5846361734108150640334823 8769542601162225960502235)
          ·
            refine ⟨13154313901743338940753353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8769542601162225960502235 13154313901743338940753353)
            ·
              refine ⟨9865735426307504205565015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13154313901743338940753353 9865735426307504205565015)
              ·
                refine ⟨14798603139461256308347523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9865735426307504205565015 14798603139461256308347523)
                ·
                  refine ⟨22197904709191884462521285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14798603139461256308347523 22197904709191884462521285)
                  ·
                    refine ⟨4162107132973478336722741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22197904709191884462521285 4162107132973478336722741)
                    ·
                      refine ⟨390197543716263594067757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4162107132973478336722741 390197543716263594067757)
                      ·
                        rfl

theorem cell23_759907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_759907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759907 prefixEnd_759907 := by exact prefixLift 759907
  have htrace : WordTrace (prefixWord ++ tailWord_759907) baseStart_759907 baseEnd_759907 := by
    simpa [prefixWord, tailWord_759907, baseEnd_759907] using wordTrace_append hprefix tailTrace_759907
  have hstable : (prefixWord ++ tailWord_759907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759907).length < 2 ^ (prefixWord ++ tailWord_759907).sum := by decide
  have hdescent : baseEnd_759907 < baseStart_759907 := by decide
  rcases family_descends (prefixWord ++ tailWord_759907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759944 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 1, 8]
def baseStart_759944 : Nat := 118140960795 + 759944 * 2 ^ 59
def prefixEnd_759944 : Nat := 4983230072969 + 3 ^ 40 * 759944 * 2
def baseEnd_759944 : Nat := 130072180833493316435029

theorem tailTrace_759944 : CollatzResearch.WordTrace tailWord_759944 prefixEnd_759944 130072180833493316435029 := by
  unfold tailWord_759944
  simp only [CollatzResearch.WordTrace]
  refine ⟨13858717379430075473675443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18478289839240100631567257 13858717379430075473675443)
  ·
    refine ⟨20788076069145113210513165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13858717379430075473675443 20788076069145113210513165)
    ·
      refine ⟨7795528525929417453942437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20788076069145113210513165 7795528525929417453942437)
      ·
        refine ⟨1461661598611765772614207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7795528525929417453942437 1461661598611765772614207)
        ·
          refine ⟨2192492397917648658921311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461661598611765772614207 2192492397917648658921311)
          ·
            refine ⟨3288738596876472988381967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192492397917648658921311 3288738596876472988381967)
            ·
              refine ⟨4933107895314709482572951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288738596876472988381967 4933107895314709482572951)
              ·
                refine ⟨7399661842972064223859427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4933107895314709482572951 7399661842972064223859427)
                ·
                  refine ⟨11099492764458096335789141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7399661842972064223859427 11099492764458096335789141)
                  ·
                    refine ⟨130072180833493316435029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11099492764458096335789141 130072180833493316435029)
                    ·
                      rfl

theorem cell23_759944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_759944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759944 prefixEnd_759944 := by exact prefixLift 759944
  have htrace : WordTrace (prefixWord ++ tailWord_759944) baseStart_759944 baseEnd_759944 := by
    simpa [prefixWord, tailWord_759944, baseEnd_759944] using wordTrace_append hprefix tailTrace_759944
  have hstable : (prefixWord ++ tailWord_759944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759944).length < 2 ^ (prefixWord ++ tailWord_759944).sum := by decide
  have hdescent : baseEnd_759944 < baseStart_759944 := by decide
  rcases family_descends (prefixWord ++ tailWord_759944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759964 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_759964 : Nat := 118140960795 + 759964 * 2 ^ 59
def prefixEnd_759964 : Nat := 4983230072969 + 3 ^ 40 * 759964 * 2
def baseEnd_759964 : Nat := 390226812113569871054995

theorem tailTrace_759964 : CollatzResearch.WordTrace tailWord_759964 prefixEnd_759964 390226812113569871054995 := by
  unfold tailWord_759964
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859082109393847181539473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18478776145858462908719297 13859082109393847181539473)
  ·
    refine ⟨10394311582045385386154605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13859082109393847181539473 10394311582045385386154605)
    ·
      refine ⟨3897866843267019519807977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10394311582045385386154605 3897866843267019519807977)
      ·
        refine ⟨2923400132450264639855983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3897866843267019519807977 2923400132450264639855983)
        ·
          refine ⟨4385100198675396959783975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923400132450264639855983 4385100198675396959783975)
          ·
            refine ⟨6577650298013095439675963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4385100198675396959783975 6577650298013095439675963)
            ·
              refine ⟨9866475447019643159513945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6577650298013095439675963 9866475447019643159513945)
              ·
                refine ⟨7399856585264732369635459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9866475447019643159513945 7399856585264732369635459)
                ·
                  refine ⟨11099784877897098554453189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7399856585264732369635459 11099784877897098554453189)
                  ·
                    refine ⟨2081209664605705978959973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11099784877897098554453189 2081209664605705978959973)
                    ·
                      refine ⟨390226812113569871054995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2081209664605705978959973 390226812113569871054995)
                      ·
                        rfl

theorem cell23_759964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_759964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759964 prefixEnd_759964 := by exact prefixLift 759964
  have htrace : WordTrace (prefixWord ++ tailWord_759964) baseStart_759964 baseEnd_759964 := by
    simpa [prefixWord, tailWord_759964, baseEnd_759964] using wordTrace_append hprefix tailTrace_759964
  have hstable : (prefixWord ++ tailWord_759964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759964).length < 2 ^ (prefixWord ++ tailWord_759964).sum := by decide
  have hdescent : baseEnd_759964 < baseStart_759964 := by decide
  rcases family_descends (prefixWord ++ tailWord_759964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759972 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_759972 : Nat := 118140960795 + 759972 * 2 ^ 59
def prefixEnd_759972 : Nat := 4983230072969 + 3 ^ 40 * 759972 * 2
def baseEnd_759972 : Nat := 390230919958805839754959

theorem tailTrace_759972 : CollatzResearch.WordTrace tailWord_759972 prefixEnd_759972 390230919958805839754959 := by
  unfold tailWord_759972
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859228001379355864685085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18478970668505807819580113 13859228001379355864685085)
  ·
    refine ⟨5197210500517258449256907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13859228001379355864685085 5197210500517258449256907)
    ·
      refine ⟨7795815750775887673885361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5197210500517258449256907 7795815750775887673885361)
      ·
        refine ⟨5846861813081915755414021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7795815750775887673885361 5846861813081915755414021)
        ·
          refine ⟨1096286589952859204140129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5846861813081915755414021 1096286589952859204140129)
          ·
            refine ⟨822214942464644403105097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1096286589952859204140129 822214942464644403105097)
            ·
              refine ⟨616661206848483302328823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822214942464644403105097 616661206848483302328823)
              ·
                refine ⟨924991810272724953493235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616661206848483302328823 924991810272724953493235)
                ·
                  refine ⟨1387487715409087430239853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924991810272724953493235 1387487715409087430239853)
                  ·
                    refine ⟨520307893278407786339945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1387487715409087430239853 520307893278407786339945)
                    ·
                      refine ⟨390230919958805839754959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520307893278407786339945 390230919958805839754959)
                      ·
                        rfl

theorem cell23_759972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_759972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759972 prefixEnd_759972 := by exact prefixLift 759972
  have htrace : WordTrace (prefixWord ++ tailWord_759972) baseStart_759972 baseEnd_759972 := by
    simpa [prefixWord, tailWord_759972, baseEnd_759972] using wordTrace_append hprefix tailTrace_759972
  have hstable : (prefixWord ++ tailWord_759972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759972).length < 2 ^ (prefixWord ++ tailWord_759972).sum := by decide
  have hdescent : baseEnd_759972 < baseStart_759972 := by decide
  rcases family_descends (prefixWord ++ tailWord_759972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759977 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_759977 : Nat := 118140960795 + 759977 * 2 ^ 59
def prefixEnd_759977 : Nat := 4983230072969 + 3 ^ 40 * 759977 * 2
def baseEnd_759977 : Nat := 390233487362078320192435

theorem tailTrace_759977 : CollatzResearch.WordTrace tailWord_759977 prefixEnd_759977 390233487362078320192435 := by
  unfold tailWord_759977
  simp only [CollatzResearch.WordTrace]
  refine ⟨27718638367740597583302185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18479092245160398388868123 27718638367740597583302185)
  ·
    refine ⟨20788978775805448187476639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27718638367740597583302185 20788978775805448187476639)
    ·
      refine ⟨31183468163708172281214959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20788978775805448187476639 31183468163708172281214959)
      ·
        refine ⟨46775202245562258421822439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31183468163708172281214959 46775202245562258421822439)
        ·
          refine ⟨70162803368343387632733659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46775202245562258421822439 70162803368343387632733659)
          ·
            refine ⟨105244205052515081449100489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70162803368343387632733659 105244205052515081449100489)
            ·
              refine ⟨78933153789386311086825367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105244205052515081449100489 78933153789386311086825367)
              ·
                refine ⟨118399730684079466630238051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78933153789386311086825367 118399730684079466630238051)
                ·
                  refine ⟨177599596026119199945357077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118399730684079466630238051 177599596026119199945357077)
                  ·
                    refine ⟨8324981063724337497438613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 177599596026119199945357077 8324981063724337497438613)
                    ·
                      refine ⟨390233487362078320192435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8324981063724337497438613 390233487362078320192435)
                      ·
                        rfl

theorem cell23_759977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_759977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759977 prefixEnd_759977 := by exact prefixLift 759977
  have htrace : WordTrace (prefixWord ++ tailWord_759977) baseStart_759977 baseEnd_759977 := by
    simpa [prefixWord, tailWord_759977, baseEnd_759977] using wordTrace_append hprefix tailTrace_759977
  have hstable : (prefixWord ++ tailWord_759977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759977).length < 2 ^ (prefixWord ++ tailWord_759977).sum := by decide
  have hdescent : baseEnd_759977 < baseStart_759977 := by decide
  rcases family_descends (prefixWord ++ tailWord_759977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759981 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_759981 : Nat := 118140960795 + 759981 * 2 ^ 59
def prefixEnd_759981 : Nat := 4983230072969 + 3 ^ 40 * 759981 * 2
def baseEnd_759981 : Nat := 390235541284696304542417

theorem tailTrace_759981 : CollatzResearch.WordTrace tailWord_759981 prefixEnd_759981 390235541284696304542417 := by
  unfold tailWord_759981
  simp only [CollatzResearch.WordTrace]
  refine ⟨27718784259726106266447797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18479189506484070844298531 27718784259726106266447797)
  ·
    refine ⟨2598636024349322462479481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27718784259726106266447797 2598636024349322462479481)
    ·
      refine ⟨1948977018261991846859611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2598636024349322462479481 1948977018261991846859611)
      ·
        refine ⟨2923465527392987770289417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948977018261991846859611 2923465527392987770289417)
        ·
          refine ⟨2192599145544740827717063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2923465527392987770289417 2192599145544740827717063)
          ·
            refine ⟨3288898718317111241575595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192599145544740827717063 3288898718317111241575595)
            ·
              refine ⟨4933348077475666862363393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288898718317111241575595 4933348077475666862363393)
              ·
                refine ⟨3700011058106750146772545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4933348077475666862363393 3700011058106750146772545)
                ·
                  refine ⟨2775008293580062610079409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3700011058106750146772545 2775008293580062610079409)
                  ·
                    refine ⟨2081256220185046957559557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2775008293580062610079409 2081256220185046957559557)
                    ·
                      refine ⟨390235541284696304542417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2081256220185046957559557 390235541284696304542417)
                      ·
                        rfl

theorem cell23_759981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_759981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759981 prefixEnd_759981 := by exact prefixLift 759981
  have htrace : WordTrace (prefixWord ++ tailWord_759981) baseStart_759981 baseEnd_759981 := by
    simpa [prefixWord, tailWord_759981, baseEnd_759981] using wordTrace_append hprefix tailTrace_759981
  have hstable : (prefixWord ++ tailWord_759981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759981).length < 2 ^ (prefixWord ++ tailWord_759981).sum := by decide
  have hdescent : baseEnd_759981 < baseStart_759981 := by decide
  rcases family_descends (prefixWord ++ tailWord_759981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759985 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 4, 2, 2]
def baseStart_759985 : Nat := 118140960795 + 759985 * 2 ^ 59
def prefixEnd_759985 : Nat := 4983230072969 + 3 ^ 40 * 759985 * 2
def baseEnd_759985 : Nat := 390237595207314288892399

theorem tailTrace_759985 : CollatzResearch.WordTrace tailWord_759985 prefixEnd_759985 390237595207314288892399 := by
  unfold tailWord_759985
  simp only [CollatzResearch.WordTrace]
  refine ⟨27718930151711614949593409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18479286767807743299728939 27718930151711614949593409)
  ·
    refine ⟨20789197613783711212195057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27718930151711614949593409 20789197613783711212195057)
    ·
      refine ⟨15591898210337783409146293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20789197613783711212195057 15591898210337783409146293)
      ·
        refine ⟨1461740457219167194607465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15591898210337783409146293 1461740457219167194607465)
        ·
          refine ⟨1096305342914375395955599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1461740457219167194607465 1096305342914375395955599)
          ·
            refine ⟨1644458014371563093933399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096305342914375395955599 1644458014371563093933399)
            ·
              refine ⟨2466687021557344640900099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644458014371563093933399 2466687021557344640900099)
              ·
                refine ⟨3700030532336016961350149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466687021557344640900099 3700030532336016961350149)
                ·
                  refine ⟨693755724813003180253153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3700030532336016961350149 693755724813003180253153)
                  ·
                    refine ⟨520316793609752385189865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 693755724813003180253153 520316793609752385189865)
                    ·
                      refine ⟨390237595207314288892399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520316793609752385189865 390237595207314288892399)
                      ·
                        rfl

theorem cell23_759985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_759985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759985 prefixEnd_759985 := by exact prefixLift 759985
  have htrace : WordTrace (prefixWord ++ tailWord_759985) baseStart_759985 baseEnd_759985 := by
    simpa [prefixWord, tailWord_759985, baseEnd_759985] using wordTrace_append hprefix tailTrace_759985
  have hstable : (prefixWord ++ tailWord_759985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759985).length < 2 ^ (prefixWord ++ tailWord_759985).sum := by decide
  have hdescent : baseEnd_759985 < baseStart_759985 := by decide
  rcases family_descends (prefixWord ++ tailWord_759985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759991 : List Nat := [1, 1, 3, 1, 4, 2, 2, 4, 5]
def baseStart_759991 : Nat := 118140960795 + 759991 * 2 ^ 59
def prefixEnd_759991 : Nat := 4983230072969 + 3 ^ 40 * 759991 * 2
def baseEnd_759991 : Nat := 43360075121249029490819

theorem tailTrace_759991 : CollatzResearch.WordTrace tailWord_759991 prefixEnd_759991 43360075121249029490819 := by
  unfold tailWord_759991
  simp only [CollatzResearch.WordTrace]
  refine ⟨27719148989689877974311827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18479432659793251982874551 27719148989689877974311827)
  ·
    refine ⟨41578723484534816961467741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27719148989689877974311827 41578723484534816961467741)
    ·
      refine ⟨15592021306700556360550403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41578723484534816961467741 15592021306700556360550403)
      ·
        refine ⟨23388031960050834540825605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15592021306700556360550403 23388031960050834540825605)
        ·
          refine ⟨4385255992509531476404801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23388031960050834540825605 4385255992509531476404801)
          ·
            refine ⟨3288941994382148607303601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4385255992509531476404801 3288941994382148607303601)
            ·
              refine ⟨2466706495786611455477701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3288941994382148607303601 2466706495786611455477701)
              ·
                refine ⟨462507467959989647902069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2466706495786611455477701 462507467959989647902069)
                ·
                  refine ⟨43360075121249029490819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 462507467959989647902069 43360075121249029490819)
                  ·
                    rfl

theorem cell23_759991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 5].length) (baseStart_759991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_759991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_759991 prefixEnd_759991 := by exact prefixLift 759991
  have htrace : WordTrace (prefixWord ++ tailWord_759991) baseStart_759991 baseEnd_759991 := by
    simpa [prefixWord, tailWord_759991, baseEnd_759991] using wordTrace_append hprefix tailTrace_759991
  have hstable : (prefixWord ++ tailWord_759991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759991).length < 2 ^ (prefixWord ++ tailWord_759991).sum := by decide
  have hdescent : baseEnd_759991 < baseStart_759991 := by decide
  rcases family_descends (prefixWord ++ tailWord_759991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760002 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_760002 : Nat := 118140960795 + 760002 * 2 ^ 59
def prefixEnd_760002 : Nat := 4983230072969 + 3 ^ 40 * 760002 * 2
def baseEnd_760002 : Nat := 390246324378440722379821

theorem tailTrace_760002 : CollatzResearch.WordTrace tailWord_760002 prefixEnd_760002 390246324378440722379821 := by
  unfold tailWord_760002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929887548162506713240565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18479700128433351235308173 6929887548162506713240565)
  ·
    refine ⟨649676957640235004366303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6929887548162506713240565 649676957640235004366303)
    ·
      refine ⟨974515436460352506549455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 649676957640235004366303 974515436460352506549455)
      ·
        refine ⟨1461773154690528759824183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974515436460352506549455 1461773154690528759824183)
        ·
          refine ⟨2192659732035793139736275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461773154690528759824183 2192659732035793139736275)
          ·
            refine ⟨3288989598053689709604413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192659732035793139736275 3288989598053689709604413)
            ·
              refine ⟨1233371099270133641101655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3288989598053689709604413 1233371099270133641101655)
              ·
                refine ⟨1850056648905200461652483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233371099270133641101655 1850056648905200461652483)
                ·
                  refine ⟨2775084973357800692478725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850056648905200461652483 2775084973357800692478725)
                  ·
                    refine ⟨520328432504587629839761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2775084973357800692478725 520328432504587629839761)
                    ·
                      refine ⟨390246324378440722379821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520328432504587629839761 390246324378440722379821)
                      ·
                        rfl

theorem cell23_760002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_760002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760002 prefixEnd_760002 := by exact prefixLift 760002
  have htrace : WordTrace (prefixWord ++ tailWord_760002) baseStart_760002 baseEnd_760002 := by
    simpa [prefixWord, tailWord_760002, baseEnd_760002] using wordTrace_append hprefix tailTrace_760002
  have hstable : (prefixWord ++ tailWord_760002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760002).length < 2 ^ (prefixWord ++ tailWord_760002).sum := by decide
  have hdescent : baseEnd_760002 < baseStart_760002 := by decide
  rcases family_descends (prefixWord ++ tailWord_760002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760078 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_760078 : Nat := 118140960795 + 760078 * 2 ^ 59
def prefixEnd_760078 : Nat := 4983230072969 + 3 ^ 40 * 760078 * 2
def baseEnd_760078 : Nat := 390285348908182425029471

theorem tailTrace_760078 : CollatzResearch.WordTrace tailWord_760078 prefixEnd_760078 390285348908182425029471 := by
  unfold tailWord_760078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3465290267546836479091111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18481548093583127888485925 3465290267546836479091111)
  ·
    refine ⟨5197935401320254718636667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3465290267546836479091111 5197935401320254718636667)
    ·
      refine ⟨7796903101980382077955001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5197935401320254718636667 7796903101980382077955001)
      ·
        refine ⟨5847677326485286558466251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7796903101980382077955001 5847677326485286558466251)
        ·
          refine ⟨8771515989727929837699377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5847677326485286558466251 8771515989727929837699377)
          ·
            refine ⟨6578636992295947378274533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8771515989727929837699377 6578636992295947378274533)
            ·
              refine ⟨1233494436055490133426475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6578636992295947378274533 1233494436055490133426475)
              ·
                refine ⟨1850241654083235200139713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233494436055490133426475 1850241654083235200139713)
                ·
                  refine ⟨1387681240562426400104785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1850241654083235200139713 1387681240562426400104785)
                  ·
                    refine ⟨1040760930421819800078589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1387681240562426400104785 1040760930421819800078589)
                    ·
                      refine ⟨390285348908182425029471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1040760930421819800078589 390285348908182425029471)
                      ·
                        rfl

theorem cell23_760078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_760078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760078 prefixEnd_760078 := by exact prefixLift 760078
  have htrace : WordTrace (prefixWord ++ tailWord_760078) baseStart_760078 baseEnd_760078 := by
    simpa [prefixWord, tailWord_760078, baseEnd_760078] using wordTrace_append hprefix tailTrace_760078
  have hstable : (prefixWord ++ tailWord_760078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760078).length < 2 ^ (prefixWord ++ tailWord_760078).sum := by decide
  have hdescent : baseEnd_760078 < baseStart_760078 := by decide
  rcases family_descends (prefixWord ++ tailWord_760078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760098 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 6]
def baseStart_760098 : Nat := 118140960795 + 760098 * 2 ^ 59
def prefixEnd_760098 : Nat := 4983230072969 + 3 ^ 40 * 760098 * 2
def baseEnd_760098 : Nat := 43366179835696927419931

theorem tailTrace_760098 : CollatzResearch.WordTrace tailWord_760098 prefixEnd_760098 43366179835696927419931 := by
  unfold tailWord_760098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6930762900075558812114237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18482034400201490165637965 6930762900075558812114237)
  ·
    refine ⟨2599036087528334554542839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6930762900075558812114237 2599036087528334554542839)
    ·
      refine ⟨3898554131292501831814259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2599036087528334554542839 3898554131292501831814259)
      ·
        refine ⟨5847831196938752747721389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3898554131292501831814259 5847831196938752747721389)
        ·
          refine ⟨2192936698852032280395521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5847831196938752747721389 2192936698852032280395521)
          ·
            refine ⟨1644702524139024210296641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2192936698852032280395521 1644702524139024210296641)
            ·
              refine ⟨1233526893104268157722481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644702524139024210296641 1233526893104268157722481)
              ·
                refine ⟨925145169828201118291861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1233526893104268157722481 925145169828201118291861)
                ·
                  refine ⟨43366179835696927419931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 925145169828201118291861 43366179835696927419931)
                  ·
                    rfl

theorem cell23_760098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_760098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760098 prefixEnd_760098 := by exact prefixLift 760098
  have htrace : WordTrace (prefixWord ++ tailWord_760098) baseStart_760098 baseEnd_760098 := by
    simpa [prefixWord, tailWord_760098, baseEnd_760098] using wordTrace_append hprefix tailTrace_760098
  have hstable : (prefixWord ++ tailWord_760098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760098).length < 2 ^ (prefixWord ++ tailWord_760098).sum := by decide
  have hdescent : baseEnd_760098 < baseStart_760098 := by decide
  rcases family_descends (prefixWord ++ tailWord_760098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760131 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 4]
def baseStart_760131 : Nat := 118140960795 + 760131 * 2 ^ 59
def prefixEnd_760131 : Nat := 4983230072969 + 3 ^ 40 * 760131 * 2
def baseEnd_760131 : Nat := 390312563382870717666727

theorem tailTrace_760131 : CollatzResearch.WordTrace tailWord_760131 prefixEnd_760131 390312563382870717666727 := by
  unfold tailWord_760131
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724255209182681884408247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18482836806121787922938831 27724255209182681884408247)
  ·
    refine ⟨41586382813774022826612371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27724255209182681884408247 41586382813774022826612371)
    ·
      refine ⟨62379574220661034239918557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41586382813774022826612371 62379574220661034239918557)
      ·
        refine ⟨23392340332747887839969459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62379574220661034239918557 23392340332747887839969459)
        ·
          refine ⟨35088510499121831759954189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23392340332747887839969459 35088510499121831759954189)
          ·
            refine ⟨13158191437170686909982821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35088510499121831759954189 13158191437170686909982821)
            ·
              refine ⟨2467160894469503795621779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13158191437170686909982821 2467160894469503795621779)
              ·
                refine ⟨3700741341704255693432669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467160894469503795621779 3700741341704255693432669)
                ·
                  refine ⟨1387778003139095885037251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3700741341704255693432669 1387778003139095885037251)
                  ·
                    refine ⟨2081667004708643827555877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1387778003139095885037251 2081667004708643827555877)
                    ·
                      refine ⟨390312563382870717666727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2081667004708643827555877 390312563382870717666727)
                      ·
                        rfl

theorem cell23_760131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_760131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760131 prefixEnd_760131 := by exact prefixLift 760131
  have htrace : WordTrace (prefixWord ++ tailWord_760131) baseStart_760131 baseEnd_760131 := by
    simpa [prefixWord, tailWord_760131, baseEnd_760131] using wordTrace_append hprefix tailTrace_760131
  have hstable : (prefixWord ++ tailWord_760131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760131).length < 2 ^ (prefixWord ++ tailWord_760131).sum := by decide
  have hdescent : baseEnd_760131 < baseStart_760131 := by decide
  rcases family_descends (prefixWord ++ tailWord_760131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760145 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 1, 5]
def baseStart_760145 : Nat := 118140960795 + 760145 * 2 ^ 59
def prefixEnd_760145 : Nat := 4983230072969 + 3 ^ 40 * 760145 * 2
def baseEnd_760145 : Nat := 130106584037344554297221

theorem tailTrace_760145 : CollatzResearch.WordTrace tailWord_760145 prefixEnd_760145 130106584037344554297221 := by
  unfold tailWord_760145
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724765831131962275417889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18483177220754641516945259 27724765831131962275417889)
  ·
    refine ⟨20793574373348971706563417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27724765831131962275417889 20793574373348971706563417)
    ·
      refine ⟨15595180780011728779922563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20793574373348971706563417 15595180780011728779922563)
      ·
        refine ⟨23392771170017593169883845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15595180780011728779922563 23392771170017593169883845)
        ·
          refine ⟨4386144594378298719353221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23392771170017593169883845 4386144594378298719353221)
          ·
            refine ⟨822402111445931009878729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4386144594378298719353221 822402111445931009878729)
            ·
              refine ⟨616801583584448257409047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822402111445931009878729 616801583584448257409047)
              ·
                refine ⟨925202375376672386113571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616801583584448257409047 925202375376672386113571)
                ·
                  refine ⟨1387803563065008579170357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925202375376672386113571 1387803563065008579170357)
                  ·
                    refine ⟨130106584037344554297221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1387803563065008579170357 130106584037344554297221)
                    ·
                      rfl

theorem cell23_760145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_760145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760145 prefixEnd_760145 := by exact prefixLift 760145
  have htrace : WordTrace (prefixWord ++ tailWord_760145) baseStart_760145 baseEnd_760145 := by
    simpa [prefixWord, tailWord_760145, baseEnd_760145] using wordTrace_append hprefix tailTrace_760145
  have hstable : (prefixWord ++ tailWord_760145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760145).length < 2 ^ (prefixWord ++ tailWord_760145).sum := by decide
  have hdescent : baseEnd_760145 < baseStart_760145 := by decide
  rcases family_descends (prefixWord ++ tailWord_760145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760151 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_760151 : Nat := 118140960795 + 760151 * 2 ^ 59
def prefixEnd_760151 : Nat := 4983230072969 + 3 ^ 40 * 760151 * 2
def baseEnd_760151 : Nat := 390322832995960639416635

theorem tailTrace_760151 : CollatzResearch.WordTrace tailWord_760151 prefixEnd_760151 390322832995960639416635 := by
  unfold tailWord_760151
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724984669110225300136307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18483323112740150200090871 27724984669110225300136307)
  ·
    refine ⟨41587477003665337950204461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27724984669110225300136307 41587477003665337950204461)
    ·
      refine ⟨15595303876374501731326673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41587477003665337950204461 15595303876374501731326673)
      ·
        refine ⟨11696477907280876298495005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15595303876374501731326673 11696477907280876298495005)
        ·
          refine ⟨4386179215230328611935627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11696477907280876298495005 4386179215230328611935627)
          ·
            refine ⟨6579268822845492917903441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386179215230328611935627 6579268822845492917903441)
            ·
              refine ⟨4934451617134119688427581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6579268822845492917903441 4934451617134119688427581)
              ·
                refine ⟨1850419356425294883160343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4934451617134119688427581 1850419356425294883160343)
                ·
                  refine ⟨2775629034637942324740515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850419356425294883160343 2775629034637942324740515)
                  ·
                    refine ⟨4163443551956913487110773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2775629034637942324740515 4163443551956913487110773)
                    ·
                      refine ⟨390322832995960639416635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4163443551956913487110773 390322832995960639416635)
                      ·
                        rfl

theorem cell23_760151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_760151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760151 prefixEnd_760151 := by exact prefixLift 760151
  have htrace : WordTrace (prefixWord ++ tailWord_760151) baseStart_760151 baseEnd_760151 := by
    simpa [prefixWord, tailWord_760151, baseEnd_760151] using wordTrace_append hprefix tailTrace_760151
  have hstable : (prefixWord ++ tailWord_760151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760151).length < 2 ^ (prefixWord ++ tailWord_760151).sum := by decide
  have hdescent : baseEnd_760151 < baseStart_760151 := by decide
  rcases family_descends (prefixWord ++ tailWord_760151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760165 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 3, 2, 2]
def baseStart_760165 : Nat := 118140960795 + 760165 * 2 ^ 59
def prefixEnd_760165 : Nat := 4983230072969 + 3 ^ 40 * 760165 * 2
def baseEnd_760165 : Nat := 390330021725123584641571

theorem tailTrace_760165 : CollatzResearch.WordTrace tailWord_760165 prefixEnd_760165 390330021725123584641571 := by
  unfold tailWord_760165
  simp only [CollatzResearch.WordTrace]
  refine ⟨27725495291059505691145949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18483663527373003794097299 27725495291059505691145949)
  ·
    refine ⟨10397060734147314634179731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27725495291059505691145949 10397060734147314634179731)
    ·
      refine ⟨15595591101220971951269597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10397060734147314634179731 15595591101220971951269597)
      ·
        refine ⟨5848346662957864481726099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15595591101220971951269597 5848346662957864481726099)
        ·
          refine ⟨8772519994436796722589149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848346662957864481726099 8772519994436796722589149)
          ·
            refine ⟨3289694997913798770970931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8772519994436796722589149 3289694997913798770970931)
            ·
              refine ⟨4934542496870698156456397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289694997913798770970931 4934542496870698156456397)
              ·
                refine ⟨1850453436326511808671149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4934542496870698156456397 1850453436326511808671149)
                ·
                  refine ⟨693920038622441928251681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1850453436326511808671149 693920038622441928251681)
                  ·
                    refine ⟨520440028966831446188761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 693920038622441928251681 520440028966831446188761)
                    ·
                      refine ⟨390330021725123584641571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520440028966831446188761 390330021725123584641571)
                      ·
                        rfl

theorem cell23_760165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_760165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760165 prefixEnd_760165 := by exact prefixLift 760165
  have htrace : WordTrace (prefixWord ++ tailWord_760165) baseStart_760165 baseEnd_760165 := by
    simpa [prefixWord, tailWord_760165, baseEnd_760165] using wordTrace_append hprefix tailTrace_760165
  have hstable : (prefixWord ++ tailWord_760165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760165).length < 2 ^ (prefixWord ++ tailWord_760165).sum := by decide
  have hdescent : baseEnd_760165 < baseStart_760165 := by decide
  rcases family_descends (prefixWord ++ tailWord_760165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760168 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_760168 : Nat := 118140960795 + 760168 * 2 ^ 59
def prefixEnd_760168 : Nat := 4983230072969 + 3 ^ 40 * 760168 * 2
def baseEnd_760168 : Nat := 390331562167087072904057

theorem tailTrace_760168 : CollatzResearch.WordTrace tailWord_760168 prefixEnd_760168 390331562167087072904057 := by
  unfold tailWord_760168
  simp only [CollatzResearch.WordTrace]
  refine ⟨13862802355024318601752579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18483736473365758135670105 13862802355024318601752579)
  ·
    refine ⟨20794203532536477902628869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13862802355024318601752579 20794203532536477902628869)
    ·
      refine ⟨3898913162350589606742913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20794203532536477902628869 3898913162350589606742913)
      ·
        refine ⟨2924184871762942205057185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3898913162350589606742913 2924184871762942205057185)
        ·
          refine ⟨2193138653822206653792889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2924184871762942205057185 2193138653822206653792889)
          ·
            refine ⟨1644853990366654990344667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2193138653822206653792889 1644853990366654990344667)
            ·
              refine ⟨2467280985549982485517001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644853990366654990344667 2467280985549982485517001)
              ·
                refine ⟨1850460739162486864137751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467280985549982485517001 1850460739162486864137751)
                ·
                  refine ⟨2775691108743730296206627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850460739162486864137751 2775691108743730296206627)
                  ·
                    refine ⟨4163536663115595444309941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2775691108743730296206627 4163536663115595444309941)
                    ·
                      refine ⟨390331562167087072904057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4163536663115595444309941 390331562167087072904057)
                      ·
                        rfl

theorem cell23_760168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_760168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760168 prefixEnd_760168 := by exact prefixLift 760168
  have htrace : WordTrace (prefixWord ++ tailWord_760168) baseStart_760168 baseEnd_760168 := by
    simpa [prefixWord, tailWord_760168, baseEnd_760168] using wordTrace_append hprefix tailTrace_760168
  have hstable : (prefixWord ++ tailWord_760168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760168).length < 2 ^ (prefixWord ++ tailWord_760168).sum := by decide
  have hdescent : baseEnd_760168 < baseStart_760168 := by decide
  rcases family_descends (prefixWord ++ tailWord_760168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760178 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_760178 : Nat := 118140960795 + 760178 * 2 ^ 59
def prefixEnd_760178 : Nat := 4983230072969 + 3 ^ 40 * 760178 * 2
def baseEnd_760178 : Nat := 390336696973632033779011

theorem tailTrace_760178 : CollatzResearch.WordTrace tailWord_760178 prefixEnd_760178 390336696973632033779011 := by
  unfold tailWord_760178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6931492360003102227842297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18483979626674939274246125 6931492360003102227842297)
  ·
    refine ⟨5198619270002326670881723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6931492360003102227842297 5198619270002326670881723)
    ·
      refine ⟨7797928905003490006322585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5198619270002326670881723 7797928905003490006322585)
      ·
        refine ⟨5848446678752617504741939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7797928905003490006322585 5848446678752617504741939)
        ·
          refine ⟨8772670018128926257112909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848446678752617504741939 8772670018128926257112909)
          ·
            refine ⟨3289751256798347346417341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8772670018128926257112909 3289751256798347346417341)
            ·
              refine ⟨1233656721299380254906503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3289751256798347346417341 1233656721299380254906503)
              ·
                refine ⟨1850485081949070382359755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233656721299380254906503 1850485081949070382359755)
                ·
                  refine ⟨2775727622923605573539633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850485081949070382359755 2775727622923605573539633)
                  ·
                    refine ⟨2081795717192704180154725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2775727622923605573539633 2081795717192704180154725)
                    ·
                      refine ⟨390336696973632033779011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2081795717192704180154725 390336696973632033779011)
                      ·
                        rfl

theorem cell23_760178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_760178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760178 prefixEnd_760178 := by exact prefixLift 760178
  have htrace : WordTrace (prefixWord ++ tailWord_760178) baseStart_760178 baseEnd_760178 := by
    simpa [prefixWord, tailWord_760178, baseEnd_760178] using wordTrace_append hprefix tailTrace_760178
  have hstable : (prefixWord ++ tailWord_760178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760178).length < 2 ^ (prefixWord ++ tailWord_760178).sum := by decide
  have hdescent : baseEnd_760178 < baseStart_760178 := by decide
  rcases family_descends (prefixWord ++ tailWord_760178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760216 : List Nat := [2, 1, 2, 5, 1, 2, 3, 2, 1, 2, 2]
def baseStart_760216 : Nat := 118140960795 + 760216 * 2 ^ 59
def prefixEnd_760216 : Nat := 4983230072969 + 3 ^ 40 * 760216 * 2
def baseEnd_760216 : Nat := 390356209238502885103837

theorem tailTrace_760216 : CollatzResearch.WordTrace tailWord_760216 prefixEnd_760216 390356209238502885103837 := by
  unfold tailWord_760216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13863677706937370700626251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18484903609249827600835001 13863677706937370700626251)
  ·
    refine ⟨20795516560406056050939377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13863677706937370700626251 20795516560406056050939377)
    ·
      refine ⟨15596637420304542038204533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20795516560406056050939377 15596637420304542038204533)
      ·
        refine ⟨1462184758153550816081675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15596637420304542038204533 1462184758153550816081675)
        ·
          refine ⟨2193277137230326224122513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1462184758153550816081675 2193277137230326224122513)
          ·
            refine ⟨1644957852922744668091885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2193277137230326224122513 1644957852922744668091885)
            ·
              refine ⟨616859194846029250534457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1644957852922744668091885 616859194846029250534457)
              ·
                refine ⟨462644396134521937900843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616859194846029250534457 462644396134521937900843)
                ·
                  refine ⟨693966594201782906851265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462644396134521937900843 693966594201782906851265)
                  ·
                    refine ⟨520474945651337180138449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 693966594201782906851265 520474945651337180138449)
                    ·
                      refine ⟨390356209238502885103837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520474945651337180138449 390356209238502885103837)
                      ·
                        rfl

theorem cell23_760216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_760216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760216 prefixEnd_760216 := by exact prefixLift 760216
  have htrace : WordTrace (prefixWord ++ tailWord_760216) baseStart_760216 baseEnd_760216 := by
    simpa [prefixWord, tailWord_760216, baseEnd_760216] using wordTrace_append hprefix tailTrace_760216
  have hstable : (prefixWord ++ tailWord_760216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760216).length < 2 ^ (prefixWord ++ tailWord_760216).sum := by decide
  have hdescent : baseEnd_760216 < baseStart_760216 := by decide
  rcases family_descends (prefixWord ++ tailWord_760216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760288 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 3]
def baseStart_760288 : Nat := 118140960795 + 760288 * 2 ^ 59
def prefixEnd_760288 : Nat := 4983230072969 + 3 ^ 40 * 760288 * 2
def baseEnd_760288 : Nat := 390393179845626603403505

theorem tailTrace_760288 : CollatzResearch.WordTrace tailWord_760288 prefixEnd_760288 390393179845626603403505 := by
  unfold tailWord_760288
  simp only [CollatzResearch.WordTrace]
  refine ⟨13864990734806948848936759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18486654313075931798582345 13864990734806948848936759)
  ·
    refine ⟨20797486102210423273405139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13864990734806948848936759 20797486102210423273405139)
    ·
      refine ⟨31196229153315634910107709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20797486102210423273405139 31196229153315634910107709)
      ·
        refine ⟨11698585932493363091290391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31196229153315634910107709 11698585932493363091290391)
        ·
          refine ⟨17547878898740044636935587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11698585932493363091290391 17547878898740044636935587)
          ·
            refine ⟨26321818348110066955403381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17547878898740044636935587 26321818348110066955403381)
            ·
              refine ⟨2467670470135318777069067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26321818348110066955403381 2467670470135318777069067)
              ·
                refine ⟨3701505705202978165603601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467670470135318777069067 3701505705202978165603601)
                ·
                  refine ⟨2776129278902233624202701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3701505705202978165603601 2776129278902233624202701)
                  ·
                    refine ⟨1041048479588337609076013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776129278902233624202701 1041048479588337609076013)
                    ·
                      refine ⟨390393179845626603403505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1041048479588337609076013 390393179845626603403505)
                      ·
                        rfl

theorem cell23_760288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_760288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760288 prefixEnd_760288 := by exact prefixLift 760288
  have htrace : WordTrace (prefixWord ++ tailWord_760288) baseStart_760288 baseEnd_760288 := by
    simpa [prefixWord, tailWord_760288, baseEnd_760288] using wordTrace_append hprefix tailTrace_760288
  have hstable : (prefixWord ++ tailWord_760288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760288).length < 2 ^ (prefixWord ++ tailWord_760288).sum := by decide
  have hdescent : baseEnd_760288 < baseStart_760288 := by decide
  rcases family_descends (prefixWord ++ tailWord_760288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760328 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_760328 : Nat := 118140960795 + 760328 * 2 ^ 59
def prefixEnd_760328 : Nat := 4983230072969 + 3 ^ 40 * 760328 * 2
def baseEnd_760328 : Nat := 390413719071806446903321

theorem tailTrace_760328 : CollatzResearch.WordTrace tailWord_760328 prefixEnd_760328 390413719071806446903321 := by
  unfold tailWord_760328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13865720194734492264664819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18487626926312656352886425 13865720194734492264664819)
  ·
    refine ⟨20798580292101738396997229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13865720194734492264664819 20798580292101738396997229)
    ·
      refine ⟨7799467609538151898873961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20798580292101738396997229 7799467609538151898873961)
      ·
        refine ⟨5849600707153613924155471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7799467609538151898873961 5849600707153613924155471)
        ·
          refine ⟨8774401060730420886233207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849600707153613924155471 8774401060730420886233207)
          ·
            refine ⟨13161601591095631329349811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8774401060730420886233207 13161601591095631329349811)
            ·
              refine ⟨19742402386643446994024717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13161601591095631329349811 19742402386643446994024717)
              ·
                refine ⟨7403400894991292622759269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19742402386643446994024717 7403400894991292622759269)
                ·
                  refine ⟨1388137667810867366767363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7403400894991292622759269 1388137667810867366767363)
                  ·
                    refine ⟨2082206501716301050151045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1388137667810867366767363 2082206501716301050151045)
                    ·
                      refine ⟨390413719071806446903321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2082206501716301050151045 390413719071806446903321)
                      ·
                        rfl

theorem cell23_760328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_760328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760328 prefixEnd_760328 := by exact prefixLift 760328
  have htrace : WordTrace (prefixWord ++ tailWord_760328) baseStart_760328 baseEnd_760328 := by
    simpa [prefixWord, tailWord_760328, baseEnd_760328] using wordTrace_append hprefix tailTrace_760328
  have hstable : (prefixWord ++ tailWord_760328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760328).length < 2 ^ (prefixWord ++ tailWord_760328).sum := by decide
  have hdescent : baseEnd_760328 < baseStart_760328 := by decide
  rcases family_descends (prefixWord ++ tailWord_760328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760355 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 3, 4]
def baseStart_760355 : Nat := 118140960795 + 760355 * 2 ^ 59
def prefixEnd_760355 : Nat := 4983230072969 + 3 ^ 40 * 760355 * 2
def baseEnd_760355 : Nat := 130142527683159280421899

theorem tailTrace_760355 : CollatzResearch.WordTrace tailWord_760355 prefixEnd_760355 130142527683159280421899 := by
  unfold tailWord_760355
  simp only [CollatzResearch.WordTrace]
  refine ⟨27732425160371168140562519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18488283440247445427041679 27732425160371168140562519)
  ·
    refine ⟨41598637740556752210843779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27732425160371168140562519 41598637740556752210843779)
    ·
      refine ⟨62397956610835128316265669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41598637740556752210843779 62397956610835128316265669)
      ·
        refine ⟨11699616864531586559299813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62397956610835128316265669 11699616864531586559299813)
        ·
          refine ⟨2193678162099672479868715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11699616864531586559299813 2193678162099672479868715)
          ·
            refine ⟨3290517243149508719803073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193678162099672479868715 3290517243149508719803073)
            ·
              refine ⟨2467887932362131539852305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290517243149508719803073 2467887932362131539852305)
              ·
                refine ⟨1850915949271598654889229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467887932362131539852305 1850915949271598654889229)
                ·
                  refine ⟨694093480976849495583461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1850915949271598654889229 694093480976849495583461)
                  ·
                    refine ⟨130142527683159280421899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694093480976849495583461 130142527683159280421899)
                    ·
                      rfl

theorem cell23_760355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 4].length) (baseStart_760355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760355 prefixEnd_760355 := by exact prefixLift 760355
  have htrace : WordTrace (prefixWord ++ tailWord_760355) baseStart_760355 baseEnd_760355 := by
    simpa [prefixWord, tailWord_760355, baseEnd_760355] using wordTrace_append hprefix tailTrace_760355
  have hstable : (prefixWord ++ tailWord_760355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760355).length < 2 ^ (prefixWord ++ tailWord_760355).sum := by decide
  have hdescent : baseEnd_760355 < baseStart_760355 := by decide
  rcases family_descends (prefixWord ++ tailWord_760355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760389 : List Nat := [1, 3, 1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_760389 : Nat := 118140960795 + 760389 * 2 ^ 59
def prefixEnd_760389 : Nat := 4983230072969 + 3 ^ 40 * 760389 * 2
def baseEnd_760389 : Nat := 130148347130576902746847

theorem tailTrace_760389 : CollatzResearch.WordTrace tailWord_760389 prefixEnd_760389 130148347130576902746847 := by
  unfold tailWord_760389
  simp only [CollatzResearch.WordTrace]
  refine ⟨27733665242247991947300221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18489110161498661298200147 27733665242247991947300221)
  ·
    refine ⟨10400124465842996980237583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27733665242247991947300221 10400124465842996980237583)
    ·
      refine ⟨15600186698764495470356375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10400124465842996980237583 15600186698764495470356375)
      ·
        refine ⟨23400280048146743205534563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15600186698764495470356375 23400280048146743205534563)
        ·
          refine ⟨35100420072220114808301845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23400280048146743205534563 35100420072220114808301845)
          ·
            refine ⟨1645332190885317881639149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35100420072220114808301845 1645332190885317881639149)
            ·
              refine ⟨616999571581994205614681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1645332190885317881639149 616999571581994205614681)
              ·
                refine ⟨462749678686495654211011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616999571581994205614681 462749678686495654211011)
                ·
                  refine ⟨694124518029743481316517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462749678686495654211011 694124518029743481316517)
                  ·
                    refine ⟨130148347130576902746847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694124518029743481316517 130148347130576902746847)
                    ·
                      rfl

theorem cell23_760389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_760389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760389 prefixEnd_760389 := by exact prefixLift 760389
  have htrace : WordTrace (prefixWord ++ tailWord_760389) baseStart_760389 baseEnd_760389 := by
    simpa [prefixWord, tailWord_760389, baseEnd_760389] using wordTrace_append hprefix tailTrace_760389
  have hstable : (prefixWord ++ tailWord_760389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760389).length < 2 ^ (prefixWord ++ tailWord_760389).sum := by decide
  have hdescent : baseEnd_760389 < baseStart_760389 := by decide
  rcases family_descends (prefixWord ++ tailWord_760389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760405 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_760405 : Nat := 118140960795 + 760405 * 2 ^ 59
def prefixEnd_760405 : Nat := 4983230072969 + 3 ^ 40 * 760405 * 2
def baseEnd_760405 : Nat := 390453257082202645640467

theorem tailTrace_760405 : CollatzResearch.WordTrace tailWord_760405 prefixEnd_760405 390453257082202645640467 := by
  unfold tailWord_760405
  simp only [CollatzResearch.WordTrace]
  refine ⟨27734248810190026679882669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18489499206793351119921779 27734248810190026679882669)
  ·
    refine ⟨10400343303821260004956001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27734248810190026679882669 10400343303821260004956001)
    ·
      refine ⟨7800257477865945003717001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10400343303821260004956001 7800257477865945003717001)
      ·
        refine ⟨5850193108399458752787751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7800257477865945003717001 5850193108399458752787751)
        ·
          refine ⟨8775289662599188129181627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850193108399458752787751 8775289662599188129181627)
          ·
            refine ⟨13162934493898782193772441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8775289662599188129181627 13162934493898782193772441)
            ·
              refine ⟨9872200870424086645329331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13162934493898782193772441 9872200870424086645329331)
              ·
                refine ⟨14808301305636129967993997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9872200870424086645329331 14808301305636129967993997)
                ·
                  refine ⟨5553112989613548737997749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14808301305636129967993997 5553112989613548737997749)
                  ·
                    refine ⟨520604342776270194187289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5553112989613548737997749 520604342776270194187289)
                    ·
                      refine ⟨390453257082202645640467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520604342776270194187289 390453257082202645640467)
                      ·
                        rfl

theorem cell23_760405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_760405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760405 prefixEnd_760405 := by exact prefixLift 760405
  have htrace : WordTrace (prefixWord ++ tailWord_760405) baseStart_760405 baseEnd_760405 := by
    simpa [prefixWord, tailWord_760405, baseEnd_760405] using wordTrace_append hprefix tailTrace_760405
  have hstable : (prefixWord ++ tailWord_760405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760405).length < 2 ^ (prefixWord ++ tailWord_760405).sum := by decide
  have hdescent : baseEnd_760405 < baseStart_760405 := by decide
  rcases family_descends (prefixWord ++ tailWord_760405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760428 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_760428 : Nat := 118140960795 + 760428 * 2 ^ 59
def prefixEnd_760428 : Nat := 4983230072969 + 3 ^ 40 * 760428 * 2
def baseEnd_760428 : Nat := 130155022379085351884287

theorem tailTrace_760428 : CollatzResearch.WordTrace tailWord_760428 prefixEnd_760428 130155022379085351884287 := by
  unfold tailWord_760428
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867543844553350803984969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18490058459404467738646625 13867543844553350803984969)
  ·
    refine ⟨10400657883415013102988727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13867543844553350803984969 10400657883415013102988727)
    ·
      refine ⟨15600986825122519654483091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10400657883415013102988727 15600986825122519654483091)
      ·
        refine ⟨23401480237683779481724637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15600986825122519654483091 23401480237683779481724637)
        ·
          refine ⟨8775555089131417305646739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23401480237683779481724637 8775555089131417305646739)
          ·
            refine ⟨13163332633697125958470109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8775555089131417305646739 13163332633697125958470109)
            ·
              refine ⟨4936249737636422234426291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13163332633697125958470109 4936249737636422234426291)
              ·
                refine ⟨7404374606454633351639437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936249737636422234426291 7404374606454633351639437)
                ·
                  refine ⟨2776640477420487506864789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7404374606454633351639437 2776640477420487506864789)
                  ·
                    refine ⟨130155022379085351884287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2776640477420487506864789 130155022379085351884287)
                    ·
                      rfl

theorem cell23_760428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_760428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760428 prefixEnd_760428 := by exact prefixLift 760428
  have htrace : WordTrace (prefixWord ++ tailWord_760428) baseStart_760428 baseEnd_760428 := by
    simpa [prefixWord, tailWord_760428, baseEnd_760428] using wordTrace_append hprefix tailTrace_760428
  have hstable : (prefixWord ++ tailWord_760428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760428).length < 2 ^ (prefixWord ++ tailWord_760428).sum := by decide
  have hdescent : baseEnd_760428 < baseStart_760428 := by decide
  rcases family_descends (prefixWord ++ tailWord_760428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760455 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_760455 : Nat := 118140960795 + 760455 * 2 ^ 59
def prefixEnd_760455 : Nat := 4983230072969 + 3 ^ 40 * 760455 * 2
def baseEnd_760455 : Nat := 390478931114927450015237

theorem tailTrace_760455 : CollatzResearch.WordTrace tailWord_760455 prefixEnd_760455 390478931114927450015237 := by
  unfold tailWord_760455
  simp only [CollatzResearch.WordTrace]
  refine ⟨27736072460008885219202819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18490714973339256812801879 27736072460008885219202819)
  ·
    refine ⟨41604108690013327828804229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27736072460008885219202819 41604108690013327828804229)
    ·
      refine ⟨7800770379377498967900793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41604108690013327828804229 7800770379377498967900793)
      ·
        refine ⟨5850577784533124225925595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7800770379377498967900793 5850577784533124225925595)
        ·
          refine ⟨8775866676799686338888393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850577784533124225925595 8775866676799686338888393)
          ·
            refine ⟨6581900007599764754166295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8775866676799686338888393 6581900007599764754166295)
            ·
              refine ⟨9872850011399647131249443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581900007599764754166295 9872850011399647131249443)
              ·
                refine ⟨14809275017099470696874165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9872850011399647131249443 14809275017099470696874165)
                ·
                  refine ⟨1388369532853075377831953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14809275017099470696874165 1388369532853075377831953)
                  ·
                    refine ⟨1041277149639806533373965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1388369532853075377831953 1041277149639806533373965)
                    ·
                      refine ⟨390478931114927450015237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1041277149639806533373965 390478931114927450015237)
                      ·
                        rfl

theorem cell23_760455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_760455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760455 prefixEnd_760455 := by exact prefixLift 760455
  have htrace : WordTrace (prefixWord ++ tailWord_760455) baseStart_760455 baseEnd_760455 := by
    simpa [prefixWord, tailWord_760455, baseEnd_760455] using wordTrace_append hprefix tailTrace_760455
  have hstable : (prefixWord ++ tailWord_760455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760455).length < 2 ^ (prefixWord ++ tailWord_760455).sum := by decide
  have hdescent : baseEnd_760455 < baseStart_760455 := by decide
  rcases family_descends (prefixWord ++ tailWord_760455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760462 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_760462 : Nat := 118140960795 + 760462 * 2 ^ 59
def prefixEnd_760462 : Nat := 4983230072969 + 3 ^ 40 * 760462 * 2
def baseEnd_760462 : Nat := 130160841826502974209235

theorem tailTrace_760462 : CollatzResearch.WordTrace tailWord_760462 prefixEnd_760462 130160841826502974209235 := by
  unfold tailWord_760462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3467040971372940676838455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18490885180655683609805093 3467040971372940676838455)
  ·
    refine ⟨5200561457059411015257683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3467040971372940676838455 5200561457059411015257683)
    ·
      refine ⟨7800842185589116522886525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5200561457059411015257683 7800842185589116522886525)
      ·
        refine ⟨2925315819595918696082447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7800842185589116522886525 2925315819595918696082447)
        ·
          refine ⟨4387973729393878044123671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925315819595918696082447 4387973729393878044123671)
          ·
            refine ⟨6581960594090817066185507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387973729393878044123671 6581960594090817066185507)
            ·
              refine ⟨9872940891136225599278261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581960594090817066185507 9872940891136225599278261)
              ·
                refine ⟨925588208544021149932337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9872940891136225599278261 925588208544021149932337)
                ·
                  refine ⟨694191156408015862449253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 925588208544021149932337 694191156408015862449253)
                  ·
                    refine ⟨130160841826502974209235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694191156408015862449253 130160841826502974209235)
                    ·
                      rfl

theorem cell23_760462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_760462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760462 prefixEnd_760462 := by exact prefixLift 760462
  have htrace : WordTrace (prefixWord ++ tailWord_760462) baseStart_760462 baseEnd_760462 := by
    simpa [prefixWord, tailWord_760462, baseEnd_760462] using wordTrace_append hprefix tailTrace_760462
  have hstable : (prefixWord ++ tailWord_760462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760462).length < 2 ^ (prefixWord ++ tailWord_760462).sum := by decide
  have hdescent : baseEnd_760462 < baseStart_760462 := by decide
  rcases family_descends (prefixWord ++ tailWord_760462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760472 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 1, 2, 3]
def baseStart_760472 : Nat := 118140960795 + 760472 * 2 ^ 59
def prefixEnd_760472 : Nat := 4983230072969 + 3 ^ 40 * 760472 * 2
def baseEnd_760472 : Nat := 390487660286053883502659

theorem tailTrace_760472 : CollatzResearch.WordTrace tailWord_760472 prefixEnd_760472 390487660286053883502659 := by
  unfold tailWord_760472
  simp only [CollatzResearch.WordTrace]
  refine ⟨13868346250473648561285835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18491128333964864748381113 13868346250473648561285835)
  ·
    refine ⟨20802519375710472841928753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13868346250473648561285835 20802519375710472841928753)
    ·
      refine ⟨15601889531782854631446565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20802519375710472841928753 15601889531782854631446565)
      ·
        refine ⟨2925354287209285243396231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15601889531782854631446565 2925354287209285243396231)
        ·
          refine ⟨4388031430813927865094347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925354287209285243396231 4388031430813927865094347)
          ·
            refine ⟨6582047146220891797641521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388031430813927865094347 6582047146220891797641521)
            ·
              refine ⟨4936535359665668848231141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6582047146220891797641521 4936535359665668848231141)
              ·
                refine ⟨925600379937312909043339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4936535359665668848231141 925600379937312909043339)
                ·
                  refine ⟨1388400569905969363565009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925600379937312909043339 1388400569905969363565009)
                  ·
                    refine ⟨1041300427429477022673757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1388400569905969363565009 1041300427429477022673757)
                    ·
                      refine ⟨390487660286053883502659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1041300427429477022673757 390487660286053883502659)
                      ·
                        rfl

theorem cell23_760472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_760472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760472 prefixEnd_760472 := by exact prefixLift 760472
  have htrace : WordTrace (prefixWord ++ tailWord_760472) baseStart_760472 baseEnd_760472 := by
    simpa [prefixWord, tailWord_760472, baseEnd_760472] using wordTrace_append hprefix tailTrace_760472
  have hstable : (prefixWord ++ tailWord_760472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760472).length < 2 ^ (prefixWord ++ tailWord_760472).sum := by decide
  have hdescent : baseEnd_760472 < baseStart_760472 := by decide
  rcases family_descends (prefixWord ++ tailWord_760472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760513 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 2, 4]
def baseStart_760513 : Nat := 118140960795 + 760513 * 2 ^ 59
def prefixEnd_760513 : Nat := 4983230072969 + 3 ^ 40 * 760513 * 2
def baseEnd_760513 : Nat := 130169570997629407696657

theorem tailTrace_760513 : CollatzResearch.WordTrace tailWord_760513 prefixEnd_760513 130169570997629407696657 := by
  unfold tailWord_760513
  simp only [CollatzResearch.WordTrace]
  refine ⟨27738187893798761124814193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18492125262532507416542795 27738187893798761124814193)
  ·
    refine ⟨20803640920349070843610645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27738187893798761124814193 20803640920349070843610645)
    ·
      refine ⟨975170668141362695794249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20803640920349070843610645 975170668141362695794249)
      ·
        refine ⟨731378001106022021845687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 975170668141362695794249 731378001106022021845687)
        ·
          refine ⟨1097067001659033032768531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731378001106022021845687 1097067001659033032768531)
          ·
            refine ⟨1645600502488549549152797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097067001659033032768531 1645600502488549549152797)
            ·
              refine ⟨617100188433206080932299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1645600502488549549152797 617100188433206080932299)
              ·
                refine ⟨925650282649809121398449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617100188433206080932299 925650282649809121398449)
                ·
                  refine ⟨694237711987356841048837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 925650282649809121398449 694237711987356841048837)
                  ·
                    refine ⟨130169570997629407696657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694237711987356841048837 130169570997629407696657)
                    ·
                      rfl

theorem cell23_760513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_760513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760513 prefixEnd_760513 := by exact prefixLift 760513
  have htrace : WordTrace (prefixWord ++ tailWord_760513) baseStart_760513 baseEnd_760513 := by
    simpa [prefixWord, tailWord_760513, baseEnd_760513] using wordTrace_append hprefix tailTrace_760513
  have hstable : (prefixWord ++ tailWord_760513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760513).length < 2 ^ (prefixWord ++ tailWord_760513).sum := by decide
  have hdescent : baseEnd_760513 < baseStart_760513 := by decide
  rcases family_descends (prefixWord ++ tailWord_760513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760529 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 1, 3, 2]
def baseStart_760529 : Nat := 118140960795 + 760529 * 2 ^ 59
def prefixEnd_760529 : Nat := 4983230072969 + 3 ^ 40 * 760529 * 2
def baseEnd_760529 : Nat := 390516928683360160489897

theorem tailTrace_760529 : CollatzResearch.WordTrace tailWord_760529 prefixEnd_760529 390516928683360160489897 := by
  unfold tailWord_760529
  simp only [CollatzResearch.WordTrace]
  refine ⟨27738771461740795857396641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18492514307827197238264427 27738771461740795857396641)
  ·
    refine ⟨20804078596305596893047481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27738771461740795857396641 20804078596305596893047481)
    ·
      refine ⟨15603058947229197669785611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20804078596305596893047481 15603058947229197669785611)
      ·
        refine ⟨23404588420843796504678417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15603058947229197669785611 23404588420843796504678417)
        ·
          refine ⟨17553441315632847378508813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23404588420843796504678417 17553441315632847378508813)
          ·
            refine ⟨6582540493362317766940805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17553441315632847378508813 6582540493362317766940805)
            ·
              refine ⟨1234226342505434581301401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6582540493362317766940805 1234226342505434581301401)
              ·
                refine ⟨925669756879075935976051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234226342505434581301401 925669756879075935976051)
                ·
                  refine ⟨1388504635318613903964077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925669756879075935976051 1388504635318613903964077)
                  ·
                    refine ⟨520689238244480213986529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1388504635318613903964077 520689238244480213986529)
                    ·
                      refine ⟨390516928683360160489897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520689238244480213986529 390516928683360160489897)
                      ·
                        rfl

theorem cell23_760529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_760529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760529 prefixEnd_760529 := by exact prefixLift 760529
  have htrace : WordTrace (prefixWord ++ tailWord_760529) baseStart_760529 baseEnd_760529 := by
    simpa [prefixWord, tailWord_760529, baseEnd_760529] using wordTrace_append hprefix tailTrace_760529
  have hstable : (prefixWord ++ tailWord_760529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760529).length < 2 ^ (prefixWord ++ tailWord_760529).sum := by decide
  have hdescent : baseEnd_760529 < baseStart_760529 := by decide
  rcases family_descends (prefixWord ++ tailWord_760529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760545 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_760545 : Nat := 118140960795 + 760545 * 2 ^ 59
def prefixEnd_760545 : Nat := 4983230072969 + 3 ^ 40 * 760545 * 2
def baseEnd_760545 : Nat := 390525144373832097889823

theorem tailTrace_760545 : CollatzResearch.WordTrace tailWord_760545 prefixEnd_760545 390525144373832097889823 := by
  unfold tailWord_760545
  simp only [CollatzResearch.WordTrace]
  refine ⟨27739355029682830589979089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18492903353121887059986059 27739355029682830589979089)
  ·
    refine ⟨20804516272262122942484317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27739355029682830589979089 20804516272262122942484317)
    ·
      refine ⟨7801693602098296103431619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20804516272262122942484317 7801693602098296103431619)
      ·
        refine ⟨11702540403147444155147429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7801693602098296103431619 11702540403147444155147429)
        ·
          refine ⟨2194226325590145779090143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11702540403147444155147429 2194226325590145779090143)
          ·
            refine ⟨3291339488385218668635215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194226325590145779090143 3291339488385218668635215)
            ·
              refine ⟨4937009232577828002952823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291339488385218668635215 4937009232577828002952823)
              ·
                refine ⟨7405513848866742004429235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937009232577828002952823 7405513848866742004429235)
                ·
                  refine ⟨11108270773300113006643853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405513848866742004429235 11108270773300113006643853)
                  ·
                    refine ⟨4165601539987542377491445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11108270773300113006643853 4165601539987542377491445)
                    ·
                      refine ⟨390525144373832097889823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4165601539987542377491445 390525144373832097889823)
                      ·
                        rfl

theorem cell23_760545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_760545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760545 prefixEnd_760545 := by exact prefixLift 760545
  have htrace : WordTrace (prefixWord ++ tailWord_760545) baseStart_760545 baseEnd_760545 := by
    simpa [prefixWord, tailWord_760545, baseEnd_760545] using wordTrace_append hprefix tailTrace_760545
  have hstable : (prefixWord ++ tailWord_760545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760545).length < 2 ^ (prefixWord ++ tailWord_760545).sum := by decide
  have hdescent : baseEnd_760545 < baseStart_760545 := by decide
  rcases family_descends (prefixWord ++ tailWord_760545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760559 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 4, 2, 2]
def baseStart_760559 : Nat := 118140960795 + 760559 * 2 ^ 59
def prefixEnd_760559 : Nat := 4983230072969 + 3 ^ 40 * 760559 * 2
def baseEnd_760559 : Nat := 390532333102995043114759

theorem tailTrace_760559 : CollatzResearch.WordTrace tailWord_760559 prefixEnd_760559 390532333102995043114759 := by
  unfold tailWord_760559
  simp only [CollatzResearch.WordTrace]
  refine ⟨27739865651632110980988731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18493243767754740653992487 27739865651632110980988731)
  ·
    refine ⟨41609798477448166471483097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27739865651632110980988731 41609798477448166471483097)
    ·
      refine ⟨31207348858086124853612323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41609798477448166471483097 31207348858086124853612323)
      ·
        refine ⟨46811023287129187280418485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31207348858086124853612323 46811023287129187280418485)
        ·
          refine ⟨4388533433168361307539233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46811023287129187280418485 4388533433168361307539233)
          ·
            refine ⟨3291400074876270980654425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4388533433168361307539233 3291400074876270980654425)
            ·
              refine ⟨2468550056157203235490819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3291400074876270980654425 2468550056157203235490819)
              ·
                refine ⟨3702825084235804853236229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468550056157203235490819 3702825084235804853236229)
                ·
                  refine ⟨694279703294213409981793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3702825084235804853236229 694279703294213409981793)
                  ·
                    refine ⟨520709777470660057486345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 694279703294213409981793 520709777470660057486345)
                    ·
                      refine ⟨390532333102995043114759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520709777470660057486345 390532333102995043114759)
                      ·
                        rfl

theorem cell23_760559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 2, 2].length) (baseStart_760559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760559 prefixEnd_760559 := by exact prefixLift 760559
  have htrace : WordTrace (prefixWord ++ tailWord_760559) baseStart_760559 baseEnd_760559 := by
    simpa [prefixWord, tailWord_760559, baseEnd_760559] using wordTrace_append hprefix tailTrace_760559
  have hstable : (prefixWord ++ tailWord_760559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760559).length < 2 ^ (prefixWord ++ tailWord_760559).sum := by decide
  have hdescent : baseEnd_760559 < baseStart_760559 := by decide
  rcases family_descends (prefixWord ++ tailWord_760559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760575 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 3]
def baseStart_760575 : Nat := 118140960795 + 760575 * 2 ^ 59
def prefixEnd_760575 : Nat := 4983230072969 + 3 ^ 40 * 760575 * 2
def baseEnd_760575 : Nat := 390540548793466980514685

theorem tailTrace_760575 : CollatzResearch.WordTrace tailWord_760575 prefixEnd_760575 390540548793466980514685 := by
  unfold tailWord_760575
  simp only [CollatzResearch.WordTrace]
  refine ⟨27740449219574145713571179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18493632813049430475714119 27740449219574145713571179)
  ·
    refine ⟨41610673829361218570356769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27740449219574145713571179 41610673829361218570356769)
    ·
      refine ⟨31208005372020913927767577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41610673829361218570356769 31208005372020913927767577)
      ·
        refine ⟨23406004029015685445825683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31208005372020913927767577 23406004029015685445825683)
        ·
          refine ⟨35109006043523528168738525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23406004029015685445825683 35109006043523528168738525)
          ·
            refine ⟨13165877266321323063276947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35109006043523528168738525 13165877266321323063276947)
            ·
              refine ⟨19748815899481984594915421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13165877266321323063276947 19748815899481984594915421)
              ·
                refine ⟨7405805962305744223093283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19748815899481984594915421 7405805962305744223093283)
                ·
                  refine ⟨11108708943458616334639925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405805962305744223093283 11108708943458616334639925)
                  ·
                    refine ⟨1041441463449245281372493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11108708943458616334639925 1041441463449245281372493)
                    ·
                      refine ⟨390540548793466980514685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1041441463449245281372493 390540548793466980514685)
                      ·
                        rfl

theorem cell23_760575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_760575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760575 prefixEnd_760575 := by exact prefixLift 760575
  have htrace : WordTrace (prefixWord ++ tailWord_760575) baseStart_760575 baseEnd_760575 := by
    simpa [prefixWord, tailWord_760575, baseEnd_760575] using wordTrace_append hprefix tailTrace_760575
  have hstable : (prefixWord ++ tailWord_760575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760575).length < 2 ^ (prefixWord ++ tailWord_760575).sum := by decide
  have hdescent : baseEnd_760575 < baseStart_760575 := by decide
  rcases family_descends (prefixWord ++ tailWord_760575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760645 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_760645 : Nat := 118140960795 + 760645 * 2 ^ 59
def prefixEnd_760645 : Nat := 4983230072969 + 3 ^ 40 * 760645 * 2
def baseEnd_760645 : Nat := 390576492439281706639363

theorem tailTrace_760645 : CollatzResearch.WordTrace tailWord_760645 prefixEnd_760645 390576492439281706639363 := by
  unfold tailWord_760645
  simp only [CollatzResearch.WordTrace]
  refine ⟨27743002329320547668619389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18495334886213698445746259 27743002329320547668619389)
  ·
    refine ⟨10403625873495205375732271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27743002329320547668619389 10403625873495205375732271)
    ·
      refine ⟨15605438810242808063598407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10403625873495205375732271 15605438810242808063598407)
      ·
        refine ⟨23408158215364212095397611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15605438810242808063598407 23408158215364212095397611)
        ·
          refine ⟨35112237323046318143096417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23408158215364212095397611 35112237323046318143096417)
          ·
            refine ⟨26334177992284738607322313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35112237323046318143096417 26334177992284738607322313)
            ·
              refine ⟨19750633494213553955491735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26334177992284738607322313 19750633494213553955491735)
              ·
                refine ⟨29625950241320330933237603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19750633494213553955491735 29625950241320330933237603)
                ·
                  refine ⟨44438925361980496399856405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29625950241320330933237603 44438925361980496399856405)
                  ·
                    refine ⟨2083074626342835768743269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44438925361980496399856405 2083074626342835768743269)
                    ·
                      refine ⟨390576492439281706639363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2083074626342835768743269 390576492439281706639363)
                      ·
                        rfl

theorem cell23_760645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_760645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760645 prefixEnd_760645 := by exact prefixLift 760645
  have htrace : WordTrace (prefixWord ++ tailWord_760645) baseStart_760645 baseEnd_760645 := by
    simpa [prefixWord, tailWord_760645, baseEnd_760645] using wordTrace_append hprefix tailTrace_760645
  have hstable : (prefixWord ++ tailWord_760645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760645).length < 2 ^ (prefixWord ++ tailWord_760645).sum := by decide
  have hdescent : baseEnd_760645 < baseStart_760645 := by decide
  rcases family_descends (prefixWord ++ tailWord_760645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760646 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_760646 : Nat := 118140960795 + 760646 * 2 ^ 59
def prefixEnd_760646 : Nat := 4983230072969 + 3 ^ 40 * 760646 * 2
def baseEnd_760646 : Nat := 130192335306645400908953

theorem tailTrace_760646 : CollatzResearch.WordTrace tailWord_760646 prefixEnd_760646 130192335306645400908953 := by
  unfold tailWord_760646
  simp only [CollatzResearch.WordTrace]
  refine ⟨866969962572403901231431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18495359201544616559603861 866969962572403901231431)
  ·
    refine ⟨1300454943858605851847147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 866969962572403901231431 1300454943858605851847147)
    ·
      refine ⟨1950682415787908777770721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1300454943858605851847147 1950682415787908777770721)
      ·
        refine ⟨1463011811840931583328041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1950682415787908777770721 1463011811840931583328041)
        ·
          refine ⟨1097258858880698687496031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1463011811840931583328041 1097258858880698687496031)
          ·
            refine ⟨1645888288321048031244047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097258858880698687496031 1645888288321048031244047)
            ·
              refine ⟨2468832432481572046866071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645888288321048031244047 2468832432481572046866071)
              ·
                refine ⟨3703248648722358070299107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468832432481572046866071 3703248648722358070299107)
                ·
                  refine ⟨5554872973083537105448661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703248648722358070299107 5554872973083537105448661)
                  ·
                    refine ⟨130192335306645400908953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5554872973083537105448661 130192335306645400908953)
                    ·
                      rfl

theorem cell23_760646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_760646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760646 prefixEnd_760646 := by exact prefixLift 760646
  have htrace : WordTrace (prefixWord ++ tailWord_760646) baseStart_760646 baseEnd_760646 := by
    simpa [prefixWord, tailWord_760646, baseEnd_760646] using wordTrace_append hprefix tailTrace_760646
  have hstable : (prefixWord ++ tailWord_760646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760646).length < 2 ^ (prefixWord ++ tailWord_760646).sum := by decide
  have hdescent : baseEnd_760646 < baseStart_760646 := by decide
  rcases family_descends (prefixWord ++ tailWord_760646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760649 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 4]
def baseStart_760649 : Nat := 118140960795 + 760649 * 2 ^ 59
def prefixEnd_760649 : Nat := 4983230072969 + 3 ^ 40 * 760649 * 2
def baseEnd_760649 : Nat := 390578546361899690989345

theorem tailTrace_760649 : CollatzResearch.WordTrace tailWord_760649 prefixEnd_760649 390578546361899690989345 := by
  unfold tailWord_760649
  simp only [CollatzResearch.WordTrace]
  refine ⟨27743148221306056351765001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18495432147537370901176667 27743148221306056351765001)
  ·
    refine ⟨20807361165979542263823751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27743148221306056351765001 20807361165979542263823751)
    ·
      refine ⟨31211041748969313395735627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20807361165979542263823751 31211041748969313395735627)
      ·
        refine ⟨46816562623453970093603441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31211041748969313395735627 46816562623453970093603441)
        ·
          refine ⟨35112421967590477570202581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46816562623453970093603441 35112421967590477570202581)
          ·
            refine ⟨822947389865401818051623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35112421967590477570202581 822947389865401818051623)
            ·
              refine ⟨1234421084798102727077435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822947389865401818051623 1234421084798102727077435)
              ·
                refine ⟨1851631627197154090616153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234421084798102727077435 1851631627197154090616153)
                ·
                  refine ⟨1388723720397865567962115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1851631627197154090616153 1388723720397865567962115)
                  ·
                    refine ⟨2083085580596798351943173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1388723720397865567962115 2083085580596798351943173)
                    ·
                      refine ⟨390578546361899690989345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2083085580596798351943173 390578546361899690989345)
                      ·
                        rfl

theorem cell23_760649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 4].length) (baseStart_760649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760649 prefixEnd_760649 := by exact prefixLift 760649
  have htrace : WordTrace (prefixWord ++ tailWord_760649) baseStart_760649 baseEnd_760649 := by
    simpa [prefixWord, tailWord_760649, baseEnd_760649] using wordTrace_append hprefix tailTrace_760649
  have hstable : (prefixWord ++ tailWord_760649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760649).length < 2 ^ (prefixWord ++ tailWord_760649).sum := by decide
  have hdescent : baseEnd_760649 < baseStart_760649 := by decide
  rcases family_descends (prefixWord ++ tailWord_760649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760676 : List Nat := [2, 3, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_760676 : Nat := 118140960795 + 760676 * 2 ^ 59
def prefixEnd_760676 : Nat := 4983230072969 + 3 ^ 40 * 760676 * 2
def baseEnd_760676 : Nat := 130197470113190361783907

theorem tailTrace_760676 : CollatzResearch.WordTrace tailWord_760676 prefixEnd_760676 130197470113190361783907 := by
  unfold tailWord_760676
  simp only [CollatzResearch.WordTrace]
  refine ⟨13872066496104119981498941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18496088661472159975331921 13872066496104119981498941)
  ·
    refine ⟨5202024936039044993062103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13872066496104119981498941 5202024936039044993062103)
    ·
      refine ⟨7803037404058567489593155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5202024936039044993062103 7803037404058567489593155)
      ·
        refine ⟨11704556106087851234389733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7803037404058567489593155 11704556106087851234389733)
        ·
          refine ⟨2194604269891472106448075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11704556106087851234389733 2194604269891472106448075)
          ·
            refine ⟨3291906404837208159672113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194604269891472106448075 3291906404837208159672113)
            ·
              refine ⟨2468929803627906119754085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3291906404837208159672113 2468929803627906119754085)
              ·
                refine ⟨462924338180232397453891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2468929803627906119754085 462924338180232397453891)
                ·
                  refine ⟨694386507270348596180837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462924338180232397453891 694386507270348596180837)
                  ·
                    refine ⟨130197470113190361783907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694386507270348596180837 130197470113190361783907)
                    ·
                      rfl

theorem cell23_760676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_760676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760676 prefixEnd_760676 := by exact prefixLift 760676
  have htrace : WordTrace (prefixWord ++ tailWord_760676) baseStart_760676 baseEnd_760676 := by
    simpa [prefixWord, tailWord_760676, baseEnd_760676] using wordTrace_append hprefix tailTrace_760676
  have hstable : (prefixWord ++ tailWord_760676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760676).length < 2 ^ (prefixWord ++ tailWord_760676).sum := by decide
  have hdescent : baseEnd_760676 < baseStart_760676 := by decide
  rcases family_descends (prefixWord ++ tailWord_760676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760689 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 6]
def baseStart_760689 : Nat := 118140960795 + 760689 * 2 ^ 59
def prefixEnd_760689 : Nat := 4983230072969 + 3 ^ 40 * 760689 * 2
def baseEnd_760689 : Nat := 43399898398675503832129

theorem tailTrace_760689 : CollatzResearch.WordTrace tailWord_760689 prefixEnd_760689 43399898398675503832129 := by
  unfold tailWord_760689
  simp only [CollatzResearch.WordTrace]
  refine ⟨27744607141161143183221121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18496404760774095455480747 27744607141161143183221121)
  ·
    refine ⟨20808455355870857387415841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27744607141161143183221121 20808455355870857387415841)
    ·
      refine ⟨15606341516903143040561881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20808455355870857387415841 15606341516903143040561881)
      ·
        refine ⟨11704756137677357280421411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15606341516903143040561881 11704756137677357280421411)
        ·
          refine ⟨17557134206516035920632117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11704756137677357280421411 17557134206516035920632117)
          ·
            refine ⟨1645981331860878367559261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17557134206516035920632117 1645981331860878367559261)
            ·
              refine ⟨617242999447829387834723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1645981331860878367559261 617242999447829387834723)
              ·
                refine ⟨925864499171744081752085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617242999447829387834723 925864499171744081752085)
                ·
                  refine ⟨43399898398675503832129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 925864499171744081752085 43399898398675503832129)
                  ·
                    rfl

theorem cell23_760689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 6].length) (baseStart_760689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760689 prefixEnd_760689 := by exact prefixLift 760689
  have htrace : WordTrace (prefixWord ++ tailWord_760689) baseStart_760689 baseEnd_760689 := by
    simpa [prefixWord, tailWord_760689, baseEnd_760689] using wordTrace_append hprefix tailTrace_760689
  have hstable : (prefixWord ++ tailWord_760689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760689).length < 2 ^ (prefixWord ++ tailWord_760689).sum := by decide
  have hdescent : baseEnd_760689 < baseStart_760689 := by decide
  rcases family_descends (prefixWord ++ tailWord_760689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760695 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_760695 : Nat := 118140960795 + 760695 * 2 ^ 59
def prefixEnd_760695 : Nat := 4983230072969 + 3 ^ 40 * 760695 * 2
def baseEnd_760695 : Nat := 390602166472006511014133

theorem tailTrace_760695 : CollatzResearch.WordTrace tailWord_760695 prefixEnd_760695 390602166472006511014133 := by
  unfold tailWord_760695
  simp only [CollatzResearch.WordTrace]
  refine ⟨27744825979139406207939539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18496550652759604138626359 27744825979139406207939539)
  ·
    refine ⟨41617238968709109311909309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27744825979139406207939539 41617238968709109311909309)
    ·
      refine ⟨15606464613265915991965991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41617238968709109311909309 15606464613265915991965991)
      ·
        refine ⟨23409696919898873987948987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15606464613265915991965991 23409696919898873987948987)
        ·
          refine ⟨35114545379848310981923481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23409696919898873987948987 35114545379848310981923481)
          ·
            refine ⟨26335909034886233236442611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35114545379848310981923481 26335909034886233236442611)
            ·
              refine ⟨39503863552329349854663917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26335909034886233236442611 39503863552329349854663917)
              ·
                refine ⟨14813948832123506195498969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39503863552329349854663917 14813948832123506195498969)
                ·
                  refine ⟨11110461624092629646624227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14813948832123506195498969 11110461624092629646624227)
                  ·
                    refine ⟨16665692436138944469936341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11110461624092629646624227 16665692436138944469936341)
                    ·
                      refine ⟨390602166472006511014133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16665692436138944469936341 390602166472006511014133)
                      ·
                        rfl

theorem cell23_760695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_760695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760695 prefixEnd_760695 := by exact prefixLift 760695
  have htrace : WordTrace (prefixWord ++ tailWord_760695) baseStart_760695 baseEnd_760695 := by
    simpa [prefixWord, tailWord_760695, baseEnd_760695] using wordTrace_append hprefix tailTrace_760695
  have hstable : (prefixWord ++ tailWord_760695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760695).length < 2 ^ (prefixWord ++ tailWord_760695).sum := by decide
  have hdescent : baseEnd_760695 < baseStart_760695 := by decide
  rcases family_descends (prefixWord ++ tailWord_760695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760699 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 3]
def baseStart_760699 : Nat := 118140960795 + 760699 * 2 ^ 59
def prefixEnd_760699 : Nat := 4983230072969 + 3 ^ 40 * 760699 * 2
def baseEnd_760699 : Nat := 390604220394624495364115

theorem tailTrace_760699 : CollatzResearch.WordTrace tailWord_760699 prefixEnd_760699 390604220394624495364115 := by
  unfold tailWord_760699
  simp only [CollatzResearch.WordTrace]
  refine ⟨27744971871124914891085151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18496647914083276594056767 27744971871124914891085151)
  ·
    refine ⟨41617457806687372336627727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27744971871124914891085151 41617457806687372336627727)
    ·
      refine ⟨62426186710031058504941591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41617457806687372336627727 62426186710031058504941591)
      ·
        refine ⟨93639280065046587757412387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62426186710031058504941591 93639280065046587757412387)
        ·
          refine ⟨140458920097569881636118581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93639280065046587757412387 140458920097569881636118581)
          ·
            refine ⟨13168023759147176403386117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140458920097569881636118581 13168023759147176403386117)
            ·
              refine ⟨2469004454840095575634897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13168023759147176403386117 2469004454840095575634897)
              ·
                refine ⟨1851753341130071681726173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469004454840095575634897 1851753341130071681726173)
                ·
                  refine ⟨694407502923776880647315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1851753341130071681726173 694407502923776880647315)
                  ·
                    refine ⟨1041611254385665320970973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 694407502923776880647315 1041611254385665320970973)
                    ·
                      refine ⟨390604220394624495364115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1041611254385665320970973 390604220394624495364115)
                      ·
                        rfl

theorem cell23_760699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 3].length) (baseStart_760699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760699 prefixEnd_760699 := by exact prefixLift 760699
  have htrace : WordTrace (prefixWord ++ tailWord_760699) baseStart_760699 baseEnd_760699 := by
    simpa [prefixWord, tailWord_760699, baseEnd_760699] using wordTrace_append hprefix tailTrace_760699
  have hstable : (prefixWord ++ tailWord_760699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760699).length < 2 ^ (prefixWord ++ tailWord_760699).sum := by decide
  have hdescent : baseEnd_760699 < baseStart_760699 := by decide
  rcases family_descends (prefixWord ++ tailWord_760699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760709 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 1, 5, 2]
def baseStart_760709 : Nat := 118140960795 + 760709 * 2 ^ 59
def prefixEnd_760709 : Nat := 4983230072969 + 3 ^ 40 * 760709 * 2
def baseEnd_760709 : Nat := 390609355201169456239069

theorem tailTrace_760709 : CollatzResearch.WordTrace tailWord_760709 prefixEnd_760709 390609355201169456239069 := by
  unfold tailWord_760709
  simp only [CollatzResearch.WordTrace]
  refine ⟨27745336601088686598949181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18496891067392457732632787 27745336601088686598949181)
  ·
    refine ⟨10404501225408257474605943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27745336601088686598949181 10404501225408257474605943)
    ·
      refine ⟨15606751838112386211908915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10404501225408257474605943 15606751838112386211908915)
      ·
        refine ⟨23410127757168579317863373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15606751838112386211908915 23410127757168579317863373)
        ·
          refine ⟨8778797908938217244198765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23410127757168579317863373 8778797908938217244198765)
          ·
            refine ⟨3292049215851831466574537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8778797908938217244198765 3292049215851831466574537)
            ·
              refine ⟨2469036911888873599930903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3292049215851831466574537 2469036911888873599930903)
              ·
                refine ⟨3703555367833310399896355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2469036911888873599930903 3703555367833310399896355)
                ·
                  refine ⟨5555333051749965599844533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703555367833310399896355 5555333051749965599844533)
                  ·
                    refine ⟨520812473601559274985425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5555333051749965599844533 520812473601559274985425)
                    ·
                      refine ⟨390609355201169456239069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520812473601559274985425 390609355201169456239069)
                      ·
                        rfl

theorem cell23_760709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_760709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760709 prefixEnd_760709 := by exact prefixLift 760709
  have htrace : WordTrace (prefixWord ++ tailWord_760709) baseStart_760709 baseEnd_760709 := by
    simpa [prefixWord, tailWord_760709, baseEnd_760709] using wordTrace_append hprefix tailTrace_760709
  have hstable : (prefixWord ++ tailWord_760709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760709).length < 2 ^ (prefixWord ++ tailWord_760709).sum := by decide
  have hdescent : baseEnd_760709 < baseStart_760709 := by decide
  rcases family_descends (prefixWord ++ tailWord_760709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760753 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 1, 5]
def baseStart_760753 : Nat := 118140960795 + 760753 * 2 ^ 59
def prefixEnd_760753 : Nat := 4983230072969 + 3 ^ 40 * 760753 * 2
def baseEnd_760753 : Nat := 130210649449989094696289

theorem tailTrace_760753 : CollatzResearch.WordTrace tailWord_760753 prefixEnd_760753 130210649449989094696289 := by
  unfold tailWord_760753
  simp only [CollatzResearch.WordTrace]
  refine ⟨27746941412929282113550913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18497960941952854742367275 27746941412929282113550913)
  ·
    refine ⟨20810206059696961585163185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27746941412929282113550913 20810206059696961585163185)
    ·
      refine ⟨15607654544772721188872389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20810206059696961585163185 15607654544772721188872389)
      ·
        refine ⟨2926435227144885222913573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15607654544772721188872389 2926435227144885222913573)
        ·
          refine ⟨548706605089665979296295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2926435227144885222913573 548706605089665979296295)
          ·
            refine ⟨823059907634498968944443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548706605089665979296295 823059907634498968944443)
            ·
              refine ⟨1234589861451748453416665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823059907634498968944443 1234589861451748453416665)
              ·
                refine ⟨925942396088811340062499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234589861451748453416665 925942396088811340062499)
                ·
                  refine ⟨1388913594133217010093749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925942396088811340062499 1388913594133217010093749)
                  ·
                    refine ⟨130210649449989094696289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1388913594133217010093749 130210649449989094696289)
                    ·
                      rfl

theorem cell23_760753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_760753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760753 prefixEnd_760753 := by exact prefixLift 760753
  have htrace : WordTrace (prefixWord ++ tailWord_760753) baseStart_760753 baseEnd_760753 := by
    simpa [prefixWord, tailWord_760753, baseEnd_760753] using wordTrace_append hprefix tailTrace_760753
  have hstable : (prefixWord ++ tailWord_760753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760753).length < 2 ^ (prefixWord ++ tailWord_760753).sum := by decide
  have hdescent : baseEnd_760753 < baseStart_760753 := by decide
  rcases family_descends (prefixWord ++ tailWord_760753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760776 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_760776 : Nat := 118140960795 + 760776 * 2 ^ 59
def prefixEnd_760776 : Nat := 4983230072969 + 3 ^ 40 * 760776 * 2
def baseEnd_760776 : Nat := 390643758405020694101261

theorem tailTrace_760776 : CollatzResearch.WordTrace tailWord_760776 prefixEnd_760776 390643758405020694101261 := by
  unfold tailWord_760776
  simp only [CollatzResearch.WordTrace]
  refine ⟨13873890145922978520819091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18498520194563971361092121 13873890145922978520819091)
  ·
    refine ⟨20810835218884467781228637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13873890145922978520819091 20810835218884467781228637)
    ·
      refine ⟨7804063207081675417960739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20810835218884467781228637 7804063207081675417960739)
      ·
        refine ⟨11706094810622513126941109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7804063207081675417960739 11706094810622513126941109)
        ·
          refine ⟨1097446388495860605650729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11706094810622513126941109 1097446388495860605650729)
          ·
            refine ⟨823084791371895454238047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1097446388495860605650729 823084791371895454238047)
            ·
              refine ⟨1234627187057843181357071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823084791371895454238047 1234627187057843181357071)
              ·
                refine ⟨1851940780586764772035607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234627187057843181357071 1851940780586764772035607)
                ·
                  refine ⟨2777911170880147158053411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851940780586764772035607 2777911170880147158053411)
                  ·
                    refine ⟨4166866756320220737080117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2777911170880147158053411 4166866756320220737080117)
                    ·
                      refine ⟨390643758405020694101261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4166866756320220737080117 390643758405020694101261)
                      ·
                        rfl

theorem cell23_760776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_760776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760776 prefixEnd_760776 := by exact prefixLift 760776
  have htrace : WordTrace (prefixWord ++ tailWord_760776) baseStart_760776 baseEnd_760776 := by
    simpa [prefixWord, tailWord_760776, baseEnd_760776] using wordTrace_append hprefix tailTrace_760776
  have hstable : (prefixWord ++ tailWord_760776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760776).length < 2 ^ (prefixWord ++ tailWord_760776).sum := by decide
  have hdescent : baseEnd_760776 < baseStart_760776 := by decide
  rcases family_descends (prefixWord ++ tailWord_760776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760792 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 2, 7]
def baseStart_760792 : Nat := 118140960795 + 760792 * 2 ^ 59
def prefixEnd_760792 : Nat := 4983230072969 + 3 ^ 40 * 760792 * 2
def baseEnd_760792 : Nat := 130217324698497543833729

theorem tailTrace_760792 : CollatzResearch.WordTrace tailWord_760792 prefixEnd_760792 130217324698497543833729 := by
  unfold tailWord_760792
  simp only [CollatzResearch.WordTrace]
  refine ⟨13874181929893995887110315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18498909239858661182813753 13874181929893995887110315)
  ·
    refine ⟨20811272894840993830665473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13874181929893995887110315 20811272894840993830665473)
    ·
      refine ⟨15608454671130745372999105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20811272894840993830665473 15608454671130745372999105)
      ·
        refine ⟨11706341003348059029749329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15608454671130745372999105 11706341003348059029749329)
        ·
          refine ⟨8779755752511044272311997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11706341003348059029749329 8779755752511044272311997)
          ·
            refine ⟨3292408407191641602116999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8779755752511044272311997 3292408407191641602116999)
            ·
              refine ⟨4938612610787462403175499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292408407191641602116999 4938612610787462403175499)
              ·
                refine ⟨7407918916181193604763249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938612610787462403175499 7407918916181193604763249)
                ·
                  refine ⟨5555939187135895203572437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7407918916181193604763249 5555939187135895203572437)
                  ·
                    refine ⟨130217324698497543833729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5555939187135895203572437 130217324698497543833729)
                    ·
                      rfl

theorem cell23_760792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_760792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760792 prefixEnd_760792 := by exact prefixLift 760792
  have htrace : WordTrace (prefixWord ++ tailWord_760792) baseStart_760792 baseEnd_760792 := by
    simpa [prefixWord, tailWord_760792, baseEnd_760792] using wordTrace_append hprefix tailTrace_760792
  have hstable : (prefixWord ++ tailWord_760792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760792).length < 2 ^ (prefixWord ++ tailWord_760792).sum := by decide
  have hdescent : baseEnd_760792 < baseStart_760792 := by decide
  rcases family_descends (prefixWord ++ tailWord_760792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760816 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 1, 3, 2]
def baseStart_760816 : Nat := 118140960795 + 760816 * 2 ^ 59
def prefixEnd_760816 : Nat := 4983230072969 + 3 ^ 40 * 760816 * 2
def baseEnd_760816 : Nat := 390664297631200537601077

theorem tailTrace_760816 : CollatzResearch.WordTrace tailWord_760816 prefixEnd_760816 390664297631200537601077 := by
  unfold tailWord_760816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13874619605850521936547151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18499492807800695915396201 13874619605850521936547151)
  ·
    refine ⟨20811929408775782904820727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13874619605850521936547151 20811929408775782904820727)
    ·
      refine ⟨31217894113163674357231091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20811929408775782904820727 31217894113163674357231091)
      ·
        refine ⟨46826841169745511535846637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31217894113163674357231091 46826841169745511535846637)
        ·
          refine ⟨17560065438654566825942489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46826841169745511535846637 17560065438654566825942489)
          ·
            refine ⟨13170049078990925119456867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17560065438654566825942489 13170049078990925119456867)
            ·
              refine ⟨19755073618486387679185301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13170049078990925119456867 19755073618486387679185301)
              ·
                refine ⟨926019075866549422461811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19755073618486387679185301 926019075866549422461811)
                ·
                  refine ⟨1389028613799824133692717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926019075866549422461811 1389028613799824133692717)
                  ·
                    refine ⟨520885730174934050134769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389028613799824133692717 520885730174934050134769)
                    ·
                      refine ⟨390664297631200537601077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520885730174934050134769 390664297631200537601077)
                      ·
                        rfl

theorem cell23_760816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 3, 2].length) (baseStart_760816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760816 prefixEnd_760816 := by exact prefixLift 760816
  have htrace : WordTrace (prefixWord ++ tailWord_760816) baseStart_760816 baseEnd_760816 := by
    simpa [prefixWord, tailWord_760816, baseEnd_760816] using wordTrace_append hprefix tailTrace_760816
  have hstable : (prefixWord ++ tailWord_760816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760816).length < 2 ^ (prefixWord ++ tailWord_760816).sum := by decide
  have hdescent : baseEnd_760816 < baseStart_760816 := by decide
  rcases family_descends (prefixWord ++ tailWord_760816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760832 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_760832 : Nat := 118140960795 + 760832 * 2 ^ 59
def prefixEnd_760832 : Nat := 4983230072969 + 3 ^ 40 * 760832 * 2
def baseEnd_760832 : Nat := 390672513321672475001003

theorem tailTrace_760832 : CollatzResearch.WordTrace tailWord_760832 prefixEnd_760832 390672513321672475001003 := by
  unfold tailWord_760832
  simp only [CollatzResearch.WordTrace]
  refine ⟨13874911389821539302838375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18499881853095385737117833 13874911389821539302838375)
  ·
    refine ⟨20812367084732308954257563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13874911389821539302838375 20812367084732308954257563)
    ·
      refine ⟨31218550627098463431386345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20812367084732308954257563 31218550627098463431386345)
      ·
        refine ⟨23413912970323847573539759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31218550627098463431386345 23413912970323847573539759)
        ·
          refine ⟨35120869455485771360309639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23413912970323847573539759 35120869455485771360309639)
          ·
            refine ⟨52681304183228657040464459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35120869455485771360309639 52681304183228657040464459)
            ·
              refine ⟨79021956274842985560696689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52681304183228657040464459 79021956274842985560696689)
              ·
                refine ⟨59266467206132239170522517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79021956274842985560696689 59266467206132239170522517)
                ·
                  refine ⟨2778115650287448711118243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59266467206132239170522517 2778115650287448711118243)
                  ·
                    refine ⟨4167173475431173066677365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2778115650287448711118243 4167173475431173066677365)
                    ·
                      refine ⟨390672513321672475001003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4167173475431173066677365 390672513321672475001003)
                      ·
                        rfl

theorem cell23_760832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_760832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760832 prefixEnd_760832 := by exact prefixLift 760832
  have htrace : WordTrace (prefixWord ++ tailWord_760832) baseStart_760832 baseEnd_760832 := by
    simpa [prefixWord, tailWord_760832, baseEnd_760832] using wordTrace_append hprefix tailTrace_760832
  have hstable : (prefixWord ++ tailWord_760832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760832).length < 2 ^ (prefixWord ++ tailWord_760832).sum := by decide
  have hdescent : baseEnd_760832 < baseStart_760832 := by decide
  rcases family_descends (prefixWord ++ tailWord_760832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760833 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_760833 : Nat := 118140960795 + 760833 * 2 ^ 59
def prefixEnd_760833 : Nat := 4983230072969 + 3 ^ 40 * 760833 * 2
def baseEnd_760833 : Nat := 390673026802326971088499

theorem tailTrace_760833 : CollatzResearch.WordTrace tailWord_760833 prefixEnd_760833 390673026802326971088499 := by
  unfold tailWord_760833
  simp only [CollatzResearch.WordTrace]
  refine ⟨27749859252639455776463153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18499906168426303850975435 27749859252639455776463153)
  ·
    refine ⟨20812394439479591832347365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27749859252639455776463153 20812394439479591832347365)
    ·
      refine ⟨3902323957402423468565131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20812394439479591832347365 3902323957402423468565131)
      ·
        refine ⟨5853485936103635202847697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3902323957402423468565131 5853485936103635202847697)
        ·
          refine ⟨4390114452077726402135773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5853485936103635202847697 4390114452077726402135773)
          ·
            refine ⟨1646292919529147400800915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4390114452077726402135773 1646292919529147400800915)
            ·
              refine ⟨2469439379293721101201373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646292919529147400800915 2469439379293721101201373)
              ·
                refine ⟨926039767235145412950515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2469439379293721101201373 926039767235145412950515)
                ·
                  refine ⟨1389059650852718119425773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926039767235145412950515 1389059650852718119425773)
                  ·
                    refine ⟨520897369069769294784665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389059650852718119425773 520897369069769294784665)
                    ·
                      refine ⟨390673026802326971088499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520897369069769294784665 390673026802326971088499)
                      ·
                        rfl

theorem cell23_760833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_760833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760833 prefixEnd_760833 := by exact prefixLift 760833
  have htrace : WordTrace (prefixWord ++ tailWord_760833) baseStart_760833 baseEnd_760833 := by
    simpa [prefixWord, tailWord_760833, baseEnd_760833] using wordTrace_append hprefix tailTrace_760833
  have hstable : (prefixWord ++ tailWord_760833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760833).length < 2 ^ (prefixWord ++ tailWord_760833).sum := by decide
  have hdescent : baseEnd_760833 < baseStart_760833 := by decide
  rcases family_descends (prefixWord ++ tailWord_760833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760863 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 1, 4, 2]
def baseStart_760863 : Nat := 118140960795 + 760863 * 2 ^ 59
def prefixEnd_760863 : Nat := 4983230072969 + 3 ^ 40 * 760863 * 2
def baseEnd_760863 : Nat := 390688431221961853713361

theorem tailTrace_760863 : CollatzResearch.WordTrace tailWord_760863 prefixEnd_760863 390688431221961853713361 := by
  unfold tailWord_760863
  simp only [CollatzResearch.WordTrace]
  refine ⟨27750953442530770900055243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18500635628353847266703495 27750953442530770900055243)
  ·
    refine ⟨41626430163796156350082865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27750953442530770900055243 41626430163796156350082865)
    ·
      refine ⟨31219822622847117262562149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41626430163796156350082865 31219822622847117262562149)
      ·
        refine ⟨5853716741783834486730403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31219822622847117262562149 5853716741783834486730403)
        ·
          refine ⟨8780575112675751730095605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5853716741783834486730403 8780575112675751730095605)
          ·
            refine ⟨823178916813351724696463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8780575112675751730095605 823178916813351724696463)
            ·
              refine ⟨1234768375220027587044695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823178916813351724696463 1234768375220027587044695)
              ·
                refine ⟨1852152562830041380567043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234768375220027587044695 1852152562830041380567043)
                ·
                  refine ⟨2778228844245062070850565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852152562830041380567043 2778228844245062070850565)
                  ·
                    refine ⟨520917908295949138284481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2778228844245062070850565 520917908295949138284481)
                    ·
                      refine ⟨390688431221961853713361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 520917908295949138284481 390688431221961853713361)
                      ·
                        rfl

theorem cell23_760863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_760863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760863 prefixEnd_760863 := by exact prefixLift 760863
  have htrace : WordTrace (prefixWord ++ tailWord_760863) baseStart_760863 baseEnd_760863 := by
    simpa [prefixWord, tailWord_760863, baseEnd_760863] using wordTrace_append hprefix tailTrace_760863
  have hstable : (prefixWord ++ tailWord_760863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760863).length < 2 ^ (prefixWord ++ tailWord_760863).sum := by decide
  have hdescent : baseEnd_760863 < baseStart_760863 := by decide
  rcases family_descends (prefixWord ++ tailWord_760863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760899 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 2, 5]
def baseStart_760899 : Nat := 118140960795 + 760899 * 2 ^ 59
def prefixEnd_760899 : Nat := 4983230072969 + 3 ^ 40 * 760899 * 2
def baseEnd_760899 : Nat := 130235638841841237621065

theorem tailTrace_760899 : CollatzResearch.WordTrace tailWord_760899 prefixEnd_760899 130235638841841237621065 := by
  unfold tailWord_760899
  simp only [CollatzResearch.WordTrace]
  refine ⟨27752266470400349048365751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18501510980266899365577167 27752266470400349048365751)
  ·
    refine ⟨41628399705600523572548627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27752266470400349048365751 41628399705600523572548627)
    ·
      refine ⟨62442599558400785358822941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41628399705600523572548627 62442599558400785358822941)
      ·
        refine ⟨23415974834400294509558603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62442599558400785358822941 23415974834400294509558603)
        ·
          refine ⟨35123962251600441764337905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23415974834400294509558603 35123962251600441764337905)
          ·
            refine ⟨26342971688700331323253429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35123962251600441764337905 26342971688700331323253429)
            ·
              refine ⟨2469653595815656061555009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26342971688700331323253429 2469653595815656061555009)
              ·
                refine ⟨1852240196861742046166257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469653595815656061555009 1852240196861742046166257)
                ·
                  refine ⟨1389180147646306534624693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1852240196861742046166257 1389180147646306534624693)
                  ·
                    refine ⟨130235638841841237621065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1389180147646306534624693 130235638841841237621065)
                    ·
                      rfl

theorem cell23_760899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 5].length) (baseStart_760899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760899 prefixEnd_760899 := by exact prefixLift 760899
  have htrace : WordTrace (prefixWord ++ tailWord_760899) baseStart_760899 baseEnd_760899 := by
    simpa [prefixWord, tailWord_760899, baseEnd_760899] using wordTrace_append hprefix tailTrace_760899
  have hstable : (prefixWord ++ tailWord_760899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760899).length < 2 ^ (prefixWord ++ tailWord_760899).sum := by decide
  have hdescent : baseEnd_760899 < baseStart_760899 := by decide
  rcases family_descends (prefixWord ++ tailWord_760899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760903 : List Nat := [1, 1, 4, 1, 3, 3, 3, 2, 5]
def baseStart_760903 : Nat := 118140960795 + 760903 * 2 ^ 59
def prefixEnd_760903 : Nat := 4983230072969 + 3 ^ 40 * 760903 * 2
def baseEnd_760903 : Nat := 43412107827571299690353

theorem tailTrace_760903 : CollatzResearch.WordTrace tailWord_760903 prefixEnd_760903 43412107827571299690353 := by
  unfold tailWord_760903
  simp only [CollatzResearch.WordTrace]
  refine ⟨27752412362385857731511363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18501608241590571821007575 27752412362385857731511363)
  ·
    refine ⟨41628618543578786597267045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27752412362385857731511363 41628618543578786597267045)
    ·
      refine ⟨7805365976921022486987571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41628618543578786597267045 7805365976921022486987571)
      ·
        refine ⟨11708048965381533730481357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7805365976921022486987571 11708048965381533730481357)
        ·
          refine ⟨4390518362018075148930509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11708048965381533730481357 4390518362018075148930509)
          ·
            refine ⟨1646444385756778180848941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4390518362018075148930509 1646444385756778180848941)
            ·
              refine ⟨617416644658791817818353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1646444385756778180848941 617416644658791817818353)
              ·
                refine ⟨463062483494093863363765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617416644658791817818353 463062483494093863363765)
                ·
                  refine ⟨43412107827571299690353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 463062483494093863363765 43412107827571299690353)
                  ·
                    rfl

theorem cell23_760903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 5].length) (baseStart_760903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760903 prefixEnd_760903 := by exact prefixLift 760903
  have htrace : WordTrace (prefixWord ++ tailWord_760903) baseStart_760903 baseEnd_760903 := by
    simpa [prefixWord, tailWord_760903, baseEnd_760903] using wordTrace_append hprefix tailTrace_760903
  have hstable : (prefixWord ++ tailWord_760903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760903).length < 2 ^ (prefixWord ++ tailWord_760903).sum := by decide
  have hdescent : baseEnd_760903 < baseStart_760903 := by decide
  rcases family_descends (prefixWord ++ tailWord_760903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760919 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_760919 : Nat := 118140960795 + 760919 * 2 ^ 59
def prefixEnd_760919 : Nat := 4983230072969 + 3 ^ 40 * 760919 * 2
def baseEnd_760919 : Nat := 390717186138613634613103

theorem tailTrace_760919 : CollatzResearch.WordTrace tailWord_760919 prefixEnd_760919 390717186138613634613103 := by
  unfold tailWord_760919
  simp only [CollatzResearch.WordTrace]
  refine ⟨27752995930327892464093811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18501997286885261642729207 27752995930327892464093811)
  ·
    refine ⟨41629493895491838696140717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27752995930327892464093811 41629493895491838696140717)
    ·
      refine ⟨15611060210809439511052769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41629493895491838696140717 15611060210809439511052769)
      ·
        refine ⟨11708295158107079633289577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15611060210809439511052769 11708295158107079633289577)
        ·
          refine ⟨8781221368580309724967183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11708295158107079633289577 8781221368580309724967183)
          ·
            refine ⟨13171832052870464587450775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8781221368580309724967183 13171832052870464587450775)
            ·
              refine ⟨19757748079305696881176163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13171832052870464587450775 19757748079305696881176163)
              ·
                refine ⟨29636622118958545321764245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19757748079305696881176163 29636622118958545321764245)
                ·
                  refine ⟨1389216661826181811957699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29636622118958545321764245 1389216661826181811957699)
                  ·
                    refine ⟨2083824992739272717936549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1389216661826181811957699 2083824992739272717936549)
                    ·
                      refine ⟨390717186138613634613103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2083824992739272717936549 390717186138613634613103)
                      ·
                        rfl

theorem cell23_760919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_760919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760919 prefixEnd_760919 := by exact prefixLift 760919
  have htrace : WordTrace (prefixWord ++ tailWord_760919) baseStart_760919 baseEnd_760919 := by
    simpa [prefixWord, tailWord_760919, baseEnd_760919] using wordTrace_append hprefix tailTrace_760919
  have hstable : (prefixWord ++ tailWord_760919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760919).length < 2 ^ (prefixWord ++ tailWord_760919).sum := by decide
  have hdescent : baseEnd_760919 < baseStart_760919 := by decide
  rcases family_descends (prefixWord ++ tailWord_760919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760956 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_760956 : Nat := 118140960795 + 760956 * 2 ^ 59
def prefixEnd_760956 : Nat := 4983230072969 + 3 ^ 40 * 760956 * 2
def baseEnd_760956 : Nat := 390736184922829989850433

theorem tailTrace_760956 : CollatzResearch.WordTrace tailWord_760956 prefixEnd_760956 390736184922829989850433 := by
  unfold tailWord_760956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13877172715596923891595361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18502896954129231855460481 13877172715596923891595361)
  ·
    refine ⟨10407879536697692918696521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13877172715596923891595361 10407879536697692918696521)
    ·
      refine ⟨7805909652523269689022391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10407879536697692918696521 7805909652523269689022391)
      ·
        refine ⟨11708864478784904533533587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7805909652523269689022391 11708864478784904533533587)
        ·
          refine ⟨17563296718177356800300381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11708864478784904533533587 17563296718177356800300381)
          ·
            refine ⟨6586236269316508800112643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17563296718177356800300381 6586236269316508800112643)
            ·
              refine ⟨9879354403974763200168965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586236269316508800112643 9879354403974763200168965)
              ·
                refine ⟨1852378950745268100031681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9879354403974763200168965 1852378950745268100031681)
                ·
                  refine ⟨1389284213058951075023761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1852378950745268100031681 1389284213058951075023761)
                  ·
                    refine ⟨1041963159794213306267821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1389284213058951075023761 1041963159794213306267821)
                    ·
                      refine ⟨390736184922829989850433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1041963159794213306267821 390736184922829989850433)
                      ·
                        rfl

theorem cell23_760956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_760956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760956 prefixEnd_760956 := by exact prefixLift 760956
  have htrace : WordTrace (prefixWord ++ tailWord_760956) baseStart_760956 baseEnd_760956 := by
    simpa [prefixWord, tailWord_760956, baseEnd_760956] using wordTrace_append hprefix tailTrace_760956
  have hstable : (prefixWord ++ tailWord_760956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760956).length < 2 ^ (prefixWord ++ tailWord_760956).sum := by decide
  have hdescent : baseEnd_760956 < baseStart_760956 := by decide
  rcases family_descends (prefixWord ++ tailWord_760956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760963 : List Nat := [1, 1, 1, 3, 3, 2, 3, 4, 1, 4]
def baseStart_760963 : Nat := 118140960795 + 760963 * 2 ^ 59
def prefixEnd_760963 : Nat := 4983230072969 + 3 ^ 40 * 760963 * 2
def baseEnd_760963 : Nat := 130246593095803820820967

theorem tailTrace_760963 : CollatzResearch.WordTrace tailWord_760963 prefixEnd_760963 130246593095803820820967 := by
  unfold tailWord_760963
  simp only [CollatzResearch.WordTrace]
  refine ⟨27754600742168487978695543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18503067161445658652463695 27754600742168487978695543)
  ·
    refine ⟨41631901113252731968043315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27754600742168487978695543 41631901113252731968043315)
    ·
      refine ⟨62447851669879097952064973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41631901113252731968043315 62447851669879097952064973)
      ·
        refine ⟨23417944376204661732024365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62447851669879097952064973 23417944376204661732024365)
        ·
          refine ⟨8781729141076748149509137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23417944376204661732024365 8781729141076748149509137)
          ·
            refine ⟨6586296855807561112131853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8781729141076748149509137 6586296855807561112131853)
            ·
              refine ⟨2469861320927835417049445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6586296855807561112131853 2469861320927835417049445)
              ·
                refine ⟨463098997673969140696771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2469861320927835417049445 463098997673969140696771)
                ·
                  refine ⟨694648496510953711045157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463098997673969140696771 694648496510953711045157)
                  ·
                    refine ⟨130246593095803820820967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694648496510953711045157 130246593095803820820967)
                    ·
                      rfl

theorem cell23_760963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 4].length) (baseStart_760963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760963 prefixEnd_760963 := by exact prefixLift 760963
  have htrace : WordTrace (prefixWord ++ tailWord_760963) baseStart_760963 baseEnd_760963 := by
    simpa [prefixWord, tailWord_760963, baseEnd_760963] using wordTrace_append hprefix tailTrace_760963
  have hstable : (prefixWord ++ tailWord_760963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760963).length < 2 ^ (prefixWord ++ tailWord_760963).sum := by decide
  have hdescent : baseEnd_760963 < baseStart_760963 := by decide
  rcases family_descends (prefixWord ++ tailWord_760963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760990 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_760990 : Nat := 118140960795 + 760990 * 2 ^ 59
def prefixEnd_760990 : Nat := 4983230072969 + 3 ^ 40 * 760990 * 2
def baseEnd_760990 : Nat := 390753643265082856825277

theorem tailTrace_760990 : CollatzResearch.WordTrace tailWord_760990 prefixEnd_760990 390753643265082856825277 := by
  unfold tailWord_760990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3469448189133833948741053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18503723675380447726618949 3469448189133833948741053)
  ·
    refine ⟨1301043070925187730777895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3469448189133833948741053 1301043070925187730777895)
    ·
      refine ⟨1951564606387781596166843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301043070925187730777895 1951564606387781596166843)
      ·
        refine ⟨2927346909581672394250265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951564606387781596166843 2927346909581672394250265)
        ·
          refine ⟨2195510182186254295687699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2927346909581672394250265 2195510182186254295687699)
          ·
            refine ⟨3293265273279381443531549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195510182186254295687699 3293265273279381443531549)
            ·
              refine ⟨1234974477479768041324331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3293265273279381443531549 1234974477479768041324331)
              ·
                refine ⟨1852461716219652061986497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234974477479768041324331 1852461716219652061986497)
                ·
                  refine ⟨1389346287164739046489873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1852461716219652061986497 1389346287164739046489873)
                  ·
                    refine ⟨1042009715373554284867405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1389346287164739046489873 1042009715373554284867405)
                    ·
                      refine ⟨390753643265082856825277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1042009715373554284867405 390753643265082856825277)
                      ·
                        rfl

theorem cell23_760990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_760990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_760990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_760990 prefixEnd_760990 := by exact prefixLift 760990
  have htrace : WordTrace (prefixWord ++ tailWord_760990) baseStart_760990 baseEnd_760990 := by
    simpa [prefixWord, tailWord_760990, baseEnd_760990] using wordTrace_append hprefix tailTrace_760990
  have hstable : (prefixWord ++ tailWord_760990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760990).length < 2 ^ (prefixWord ++ tailWord_760990).sum := by decide
  have hdescent : baseEnd_760990 < baseStart_760990 := by decide
  rcases family_descends (prefixWord ++ tailWord_760990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761020 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_761020 : Nat := 118140960795 + 761020 * 2 ^ 59
def prefixEnd_761020 : Nat := 4983230072969 + 3 ^ 40 * 761020 * 2
def baseEnd_761020 : Nat := 390769047684717739450139

theorem tailTrace_761020 : CollatzResearch.WordTrace tailWord_761020 prefixEnd_761020 390769047684717739450139 := by
  unfold tailWord_761020
  simp only [CollatzResearch.WordTrace]
  refine ⟨13878339851480993356760257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18504453135307991142347009 13878339851480993356760257)
  ·
    refine ⟨10408754888610745017570193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13878339851480993356760257 10408754888610745017570193)
    ·
      refine ⟨7806566166458058763177645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10408754888610745017570193 7806566166458058763177645)
      ·
        refine ⟨2927462312421772036191617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7806566166458058763177645 2927462312421772036191617)
        ·
          refine ⟨2195596734316329027143713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2927462312421772036191617 2195596734316329027143713)
          ·
            refine ⟨1646697550737246770357785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2195596734316329027143713 1646697550737246770357785)
            ·
              refine ⟨1235023163052935077768339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646697550737246770357785 1235023163052935077768339)
              ·
                refine ⟨1852534744579402616652509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235023163052935077768339 1852534744579402616652509)
                ·
                  refine ⟨694700529217275981244691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1852534744579402616652509 694700529217275981244691)
                  ·
                    refine ⟨1042050793825913971867037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 694700529217275981244691 1042050793825913971867037)
                    ·
                      refine ⟨390769047684717739450139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1042050793825913971867037 390769047684717739450139)
                      ·
                        rfl

theorem cell23_761020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_761020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761020 prefixEnd_761020 := by exact prefixLift 761020
  have htrace : WordTrace (prefixWord ++ tailWord_761020) baseStart_761020 baseEnd_761020 := by
    simpa [prefixWord, tailWord_761020, baseEnd_761020] using wordTrace_append hprefix tailTrace_761020
  have hstable : (prefixWord ++ tailWord_761020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761020).length < 2 ^ (prefixWord ++ tailWord_761020).sum := by decide
  have hdescent : baseEnd_761020 < baseStart_761020 := by decide
  rcases family_descends (prefixWord ++ tailWord_761020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761066 : List Nat := [3, 1, 3, 1, 1, 5, 9]
def baseStart_761066 : Nat := 118140960795 + 761066 * 2 ^ 59
def prefixEnd_761066 : Nat := 4983230072969 + 3 ^ 40 * 761066 * 2
def baseEnd_761066 : Nat := 4824600836973142709567

theorem tailTrace_761066 : CollatzResearch.WordTrace tailWord_761066 prefixEnd_761066 4824600836973142709567 := by
  unfold tailWord_761066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6939589365198834142423763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18505571640530224379796701 6939589365198834142423763)
  ·
    refine ⟨10409384047798251213635645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6939589365198834142423763 10409384047798251213635645)
    ·
      refine ⟨3903519017924344205113367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10409384047798251213635645 3903519017924344205113367)
      ·
        refine ⟨5855278526886516307670051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3903519017924344205113367 5855278526886516307670051)
        ·
          refine ⟨8782917790329774461505077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5855278526886516307670051 8782917790329774461505077)
          ·
            refine ⟨823398542843416355766101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8782917790329774461505077 823398542843416355766101)
            ·
              refine ⟨4824600836973142709567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 823398542843416355766101 4824600836973142709567)
              ·
                rfl

theorem cell23_761066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 9].length) (baseStart_761066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761066 prefixEnd_761066 := by exact prefixLift 761066
  have htrace : WordTrace (prefixWord ++ tailWord_761066) baseStart_761066 baseEnd_761066 := by
    simpa [prefixWord, tailWord_761066, baseEnd_761066] using wordTrace_append hprefix tailTrace_761066
  have hstable : (prefixWord ++ tailWord_761066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761066).length < 2 ^ (prefixWord ++ tailWord_761066).sum := by decide
  have hdescent : baseEnd_761066 < baseStart_761066 := by decide
  rcases family_descends (prefixWord ++ tailWord_761066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761079 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 1, 9]
def baseStart_761079 : Nat := 118140960795 + 761079 * 2 ^ 59
def prefixEnd_761079 : Nat := 4983230072969 + 3 ^ 40 * 761079 * 2
def baseEnd_761079 : Nat := 130266447681111002870789

theorem tailTrace_761079 : CollatzResearch.WordTrace tailWord_761079 prefixEnd_761079 130266447681111002870789 := by
  unfold tailWord_761079
  simp only [CollatzResearch.WordTrace]
  refine ⟨27758831609748239789918291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18505887739832159859945527 27758831609748239789918291)
  ·
    refine ⟨41638247414622359684877437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27758831609748239789918291 41638247414622359684877437)
    ·
      refine ⟨15614342780483384881829039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41638247414622359684877437 15614342780483384881829039)
      ·
        refine ⟨23421514170725077322743559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15614342780483384881829039 23421514170725077322743559)
        ·
          refine ⟨35132271256087615984115339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23421514170725077322743559 35132271256087615984115339)
          ·
            refine ⟨52698406884131423976173009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35132271256087615984115339 52698406884131423976173009)
            ·
              refine ⟨39523805163098567982129757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52698406884131423976173009 39523805163098567982129757)
              ·
                refine ⟨14821426936161962993298659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39523805163098567982129757 14821426936161962993298659)
                ·
                  refine ⟨22232140404242944489947989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14821426936161962993298659 22232140404242944489947989)
                  ·
                    refine ⟨130266447681111002870789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 22232140404242944489947989 130266447681111002870789)
                    ·
                      rfl

theorem cell23_761079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_761079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761079 prefixEnd_761079 := by exact prefixLift 761079
  have htrace : WordTrace (prefixWord ++ tailWord_761079) baseStart_761079 baseEnd_761079 := by
    simpa [prefixWord, tailWord_761079, baseEnd_761079] using wordTrace_append hprefix tailTrace_761079
  have hstable : (prefixWord ++ tailWord_761079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761079).length < 2 ^ (prefixWord ++ tailWord_761079).sum := by decide
  have hdescent : baseEnd_761079 < baseStart_761079 := by decide
  rcases family_descends (prefixWord ++ tailWord_761079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761136 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 3]
def baseStart_761136 : Nat := 118140960795 + 761136 * 2 ^ 59
def prefixEnd_761136 : Nat := 4983230072969 + 3 ^ 40 * 761136 * 2
def baseEnd_761136 : Nat := 390828611440639285599605

theorem tailTrace_761136 : CollatzResearch.WordTrace tailWord_761136 prefixEnd_761136 390828611440639285599605 := by
  unfold tailWord_761136
  simp only [CollatzResearch.WordTrace]
  refine ⟨13880455285270869262371631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18507273713694492349828841 13880455285270869262371631)
  ·
    refine ⟨20820682927906303893557447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13880455285270869262371631 20820682927906303893557447)
    ·
      refine ⟨31231024391859455840336171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20820682927906303893557447 31231024391859455840336171)
      ·
        refine ⟨46846536587789183760504257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31231024391859455840336171 46846536587789183760504257)
        ·
          refine ⟨35134902440841887820378193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46846536587789183760504257 35134902440841887820378193)
          ·
            refine ⟨26351176830631415865283645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35134902440841887820378193 26351176830631415865283645)
            ·
              refine ⟨9881691311486780949481367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26351176830631415865283645 9881691311486780949481367)
              ·
                refine ⟨14822536967230171424222051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9881691311486780949481367 14822536967230171424222051)
                ·
                  refine ⟨22233805450845257136333077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14822536967230171424222051 22233805450845257136333077)
                  ·
                    refine ⟨1042209630508371428265613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22233805450845257136333077 1042209630508371428265613)
                    ·
                      refine ⟨390828611440639285599605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1042209630508371428265613 390828611440639285599605)
                      ·
                        rfl

theorem cell23_761136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_761136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761136 prefixEnd_761136 := by exact prefixLift 761136
  have htrace : WordTrace (prefixWord ++ tailWord_761136) baseStart_761136 baseEnd_761136 := by
    simpa [prefixWord, tailWord_761136, baseEnd_761136] using wordTrace_append hprefix tailTrace_761136
  have hstable : (prefixWord ++ tailWord_761136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761136).length < 2 ^ (prefixWord ++ tailWord_761136).sum := by decide
  have hdescent : baseEnd_761136 < baseStart_761136 := by decide
  rcases family_descends (prefixWord ++ tailWord_761136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761184 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 2, 2, 2]
def baseStart_761184 : Nat := 118140960795 + 761184 * 2 ^ 59
def prefixEnd_761184 : Nat := 4983230072969 + 3 ^ 40 * 761184 * 2
def baseEnd_761184 : Nat := 390853258512055097799385

theorem tailTrace_761184 : CollatzResearch.WordTrace tailWord_761184 prefixEnd_761184 390853258512055097799385 := by
  unfold tailWord_761184
  simp only [CollatzResearch.WordTrace]
  refine ⟨13881330637183921361245303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18508440849578561814993737 13881330637183921361245303)
  ·
    refine ⟨20821995955775882041867955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13881330637183921361245303 20821995955775882041867955)
    ·
      refine ⟨31232993933663823062801933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20821995955775882041867955 31232993933663823062801933)
      ·
        refine ⟨11712372725123933648550725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31232993933663823062801933 11712372725123933648550725)
        ·
          refine ⟨2196069885960737559103261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11712372725123933648550725 2196069885960737559103261)
          ·
            refine ⟨823526207235276584663723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2196069885960737559103261 823526207235276584663723)
            ·
              refine ⟨1235289310852914876995585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823526207235276584663723 1235289310852914876995585)
              ·
                refine ⟨926466983139686157746689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235289310852914876995585 926466983139686157746689)
                ·
                  refine ⟨694850237354764618310017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 926466983139686157746689 694850237354764618310017)
                  ·
                    refine ⟨521137678016073463732513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 694850237354764618310017 521137678016073463732513)
                    ·
                      refine ⟨390853258512055097799385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521137678016073463732513 390853258512055097799385)
                      ·
                        rfl

theorem cell23_761184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_761184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761184 prefixEnd_761184 := by exact prefixLift 761184
  have htrace : WordTrace (prefixWord ++ tailWord_761184) baseStart_761184 baseEnd_761184 := by
    simpa [prefixWord, tailWord_761184, baseEnd_761184] using wordTrace_append hprefix tailTrace_761184
  have hstable : (prefixWord ++ tailWord_761184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761184).length < 2 ^ (prefixWord ++ tailWord_761184).sum := by decide
  have hdescent : baseEnd_761184 < baseStart_761184 := by decide
  rcases family_descends (prefixWord ++ tailWord_761184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761193 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 2, 5, 2]
def baseStart_761193 : Nat := 118140960795 + 761193 * 2 ^ 59
def prefixEnd_761193 : Nat := 4983230072969 + 3 ^ 40 * 761193 * 2
def baseEnd_761193 : Nat := 390857879837945562586843

theorem tailTrace_761193 : CollatzResearch.WordTrace tailWord_761193 prefixEnd_761193 390857879837945562586843 := by
  unfold tailWord_761193
  simp only [CollatzResearch.WordTrace]
  refine ⟨27762989531335237259568233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18508659687556824839712155 27762989531335237259568233)
  ·
    refine ⟨20822242148501427944676175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27762989531335237259568233 20822242148501427944676175)
    ·
      refine ⟨31233363222752141917014263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20822242148501427944676175 31233363222752141917014263)
      ·
        refine ⟨46850044834128212875521395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31233363222752141917014263 46850044834128212875521395)
        ·
          refine ⟨70275067251192319313282093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46850044834128212875521395 70275067251192319313282093)
          ·
            refine ⟨26353150219197119742480785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70275067251192319313282093 26353150219197119742480785)
            ·
              refine ⟨19764862664397839806860589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26353150219197119742480785 19764862664397839806860589)
              ·
                refine ⟨7411823499149189927572721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19764862664397839806860589 7411823499149189927572721)
                ·
                  refine ⟨5558867624361892445679541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7411823499149189927572721 5558867624361892445679541)
                  ·
                    refine ⟨521143839783927416782457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5558867624361892445679541 521143839783927416782457)
                    ·
                      refine ⟨390857879837945562586843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521143839783927416782457 390857879837945562586843)
                      ·
                        rfl

theorem cell23_761193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 5, 2].length) (baseStart_761193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761193 prefixEnd_761193 := by exact prefixLift 761193
  have htrace : WordTrace (prefixWord ++ tailWord_761193) baseStart_761193 baseEnd_761193 := by
    simpa [prefixWord, tailWord_761193, baseEnd_761193] using wordTrace_append hprefix tailTrace_761193
  have hstable : (prefixWord ++ tailWord_761193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761193).length < 2 ^ (prefixWord ++ tailWord_761193).sum := by decide
  have hdescent : baseEnd_761193 < baseStart_761193 := by decide
  rcases family_descends (prefixWord ++ tailWord_761193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761223 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_761223 : Nat := 118140960795 + 761223 * 2 ^ 59
def prefixEnd_761223 : Nat := 4983230072969 + 3 ^ 40 * 761223 * 2
def baseEnd_761223 : Nat := 390873284257580445211705

theorem tailTrace_761223 : CollatzResearch.WordTrace tailWord_761223 prefixEnd_761223 390873284257580445211705 := by
  unfold tailWord_761223
  simp only [CollatzResearch.WordTrace]
  refine ⟨27764083721226552383160323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18509389147484368255440215 27764083721226552383160323)
  ·
    refine ⟨41646125581839828574740485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27764083721226552383160323 41646125581839828574740485)
    ·
      refine ⟨7808648546594967857763841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41646125581839828574740485 7808648546594967857763841)
      ·
        refine ⟨5856486409946225893322881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7808648546594967857763841 5856486409946225893322881)
        ·
          refine ⟨4392364807459669419992161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5856486409946225893322881 4392364807459669419992161)
          ·
            refine ⟨3294273605594752064994121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4392364807459669419992161 3294273605594752064994121)
            ·
              refine ⟨2470705204196064048745591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3294273605594752064994121 2470705204196064048745591)
              ·
                refine ⟨3706057806294096073118387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470705204196064048745591 3706057806294096073118387)
                ·
                  refine ⟨5559086709441144109677581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706057806294096073118387 5559086709441144109677581)
                  ·
                    refine ⟨2084657516040429041129093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5559086709441144109677581 2084657516040429041129093)
                    ·
                      refine ⟨390873284257580445211705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2084657516040429041129093 390873284257580445211705)
                      ·
                        rfl

theorem cell23_761223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_761223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761223 prefixEnd_761223 := by exact prefixLift 761223
  have htrace : WordTrace (prefixWord ++ tailWord_761223) baseStart_761223 baseEnd_761223 := by
    simpa [prefixWord, tailWord_761223, baseEnd_761223] using wordTrace_append hprefix tailTrace_761223
  have hstable : (prefixWord ++ tailWord_761223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761223).length < 2 ^ (prefixWord ++ tailWord_761223).sum := by decide
  have hdescent : baseEnd_761223 < baseStart_761223 := by decide
  rcases family_descends (prefixWord ++ tailWord_761223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761334 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_761334 : Nat := 118140960795 + 761334 * 2 ^ 59
def prefixEnd_761334 : Nat := 4983230072969 + 3 ^ 40 * 761334 * 2
def baseEnd_761334 : Nat := 390930280610229510923695

theorem tailTrace_761334 : CollatzResearch.WordTrace tailWord_761334 prefixEnd_761334 390930280610229510923695 := by
  unfold tailWord_761334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735508263989026146278191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18512088149216278893634037 1735508263989026146278191)
  ·
    refine ⟨2603262395983539219417287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1735508263989026146278191 2603262395983539219417287)
    ·
      refine ⟨3904893593975308829125931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603262395983539219417287 3904893593975308829125931)
      ·
        refine ⟨5857340390962963243688897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904893593975308829125931 5857340390962963243688897)
        ·
          refine ⟨4393005293222222432766673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5857340390962963243688897 4393005293222222432766673)
          ·
            refine ⟨3294753969916666824575005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4393005293222222432766673 3294753969916666824575005)
            ·
              refine ⟨1235532738718750059215627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3294753969916666824575005 1235532738718750059215627)
              ·
                refine ⟨1853299108078125088823441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235532738718750059215627 1853299108078125088823441)
                ·
                  refine ⟨1389974331058593816617581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1853299108078125088823441 1389974331058593816617581)
                  ·
                    refine ⟨521240374146972681231593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389974331058593816617581 521240374146972681231593)
                    ·
                      refine ⟨390930280610229510923695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521240374146972681231593 390930280610229510923695)
                      ·
                        rfl

theorem cell23_761334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_761334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761334 prefixEnd_761334 := by exact prefixLift 761334
  have htrace : WordTrace (prefixWord ++ tailWord_761334) baseStart_761334 baseEnd_761334 := by
    simpa [prefixWord, tailWord_761334, baseEnd_761334] using wordTrace_append hprefix tailTrace_761334
  have hstable : (prefixWord ++ tailWord_761334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761334).length < 2 ^ (prefixWord ++ tailWord_761334).sum := by decide
  have hdescent : baseEnd_761334 < baseStart_761334 := by decide
  rcases family_descends (prefixWord ++ tailWord_761334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761343 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_761343 : Nat := 118140960795 + 761343 * 2 ^ 59
def prefixEnd_761343 : Nat := 4983230072969 + 3 ^ 40 * 761343 * 2
def baseEnd_761343 : Nat := 390934901936119975711153

theorem tailTrace_761343 : CollatzResearch.WordTrace tailWord_761343 prefixEnd_761343 390934901936119975711153 := by
  unfold tailWord_761343
  simp only [CollatzResearch.WordTrace]
  refine ⟨27768460480791812877528683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18512306987194541918352455 27768460480791812877528683)
  ·
    refine ⟨41652690721187719316293025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27768460480791812877528683 41652690721187719316293025)
    ·
      refine ⟨31239518040890789487219769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41652690721187719316293025 31239518040890789487219769)
      ·
        refine ⟨23429638530668092115414827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31239518040890789487219769 23429638530668092115414827)
        ·
          refine ⟨35144457796002138173122241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23429638530668092115414827 35144457796002138173122241)
          ·
            refine ⟨26358343347001603629841681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35144457796002138173122241 26358343347001603629841681)
            ·
              refine ⟨19768757510251202722381261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26358343347001603629841681 19768757510251202722381261)
              ·
                refine ⟨7413284066344201020892973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19768757510251202722381261 7413284066344201020892973)
                ·
                  refine ⟨2779981524879075382834865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7413284066344201020892973 2779981524879075382834865)
                  ·
                    refine ⟨2084986143659306537126149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2779981524879075382834865 2084986143659306537126149)
                    ·
                      refine ⟨390934901936119975711153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2084986143659306537126149 390934901936119975711153)
                      ·
                        rfl

theorem cell23_761343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_761343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761343 prefixEnd_761343 := by exact prefixLift 761343
  have htrace : WordTrace (prefixWord ++ tailWord_761343) baseStart_761343 baseEnd_761343 := by
    simpa [prefixWord, tailWord_761343, baseEnd_761343] using wordTrace_append hprefix tailTrace_761343
  have hstable : (prefixWord ++ tailWord_761343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761343).length < 2 ^ (prefixWord ++ tailWord_761343).sum := by decide
  have hdescent : baseEnd_761343 < baseStart_761343 := by decide
  rcases family_descends (prefixWord ++ tailWord_761343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761377 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_761377 : Nat := 118140960795 + 761377 * 2 ^ 59
def prefixEnd_761377 : Nat := 4983230072969 + 3 ^ 40 * 761377 * 2
def baseEnd_761377 : Nat := 390952360278372842685997

theorem tailTrace_761377 : CollatzResearch.WordTrace tailWord_761377 prefixEnd_761377 390952360278372842685997 := by
  unfold tailWord_761377
  simp only [CollatzResearch.WordTrace]
  refine ⟨27769700562668636684266385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18513133708445757789510923 27769700562668636684266385)
  ·
    refine ⟨20827275422001477513199789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27769700562668636684266385 20827275422001477513199789)
    ·
      refine ⟨7810228283250554067449921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20827275422001477513199789 7810228283250554067449921)
      ·
        refine ⟨5857671212437915550587441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7810228283250554067449921 5857671212437915550587441)
        ·
          refine ⟨4393253409328436662940581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5857671212437915550587441 4393253409328436662940581)
          ·
            refine ⟨823735014249081874301359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4393253409328436662940581 823735014249081874301359)
            ·
              refine ⟨1235602521373622811452039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823735014249081874301359 1235602521373622811452039)
              ·
                refine ⟨1853403782060434217178059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235602521373622811452039 1853403782060434217178059)
                ·
                  refine ⟨2780105673090651325767089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853403782060434217178059 2780105673090651325767089)
                  ·
                    refine ⟨2085079254817988494325317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2780105673090651325767089 2085079254817988494325317)
                    ·
                      refine ⟨390952360278372842685997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2085079254817988494325317 390952360278372842685997)
                      ·
                        rfl

theorem cell23_761377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_761377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761377 prefixEnd_761377 := by exact prefixLift 761377
  have htrace : WordTrace (prefixWord ++ tailWord_761377) baseStart_761377 baseEnd_761377 := by
    simpa [prefixWord, tailWord_761377, baseEnd_761377] using wordTrace_append hprefix tailTrace_761377
  have hstable : (prefixWord ++ tailWord_761377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761377).length < 2 ^ (prefixWord ++ tailWord_761377).sum := by decide
  have hdescent : baseEnd_761377 < baseStart_761377 := by decide
  rcases family_descends (prefixWord ++ tailWord_761377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761397 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_761397 : Nat := 118140960795 + 761397 * 2 ^ 59
def prefixEnd_761397 : Nat := 4983230072969 + 3 ^ 40 * 761397 * 2
def baseEnd_761397 : Nat := 390962629891462764435905

theorem tailTrace_761397 : CollatzResearch.WordTrace tailWord_761397 prefixEnd_761397 390962629891462764435905 := by
  unfold tailWord_761397
  simp only [CollatzResearch.WordTrace]
  refine ⟨27770430022596180099994445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18513620015064120066662963 27770430022596180099994445)
  ·
    refine ⟨10413911258473567537497917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27770430022596180099994445 10413911258473567537497917)
    ·
      refine ⟨3905216721927587826561719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10413911258473567537497917 3905216721927587826561719)
      ·
        refine ⟨5857825082891381739842579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905216721927587826561719 5857825082891381739842579)
        ·
          refine ⟨8786737624337072609763869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5857825082891381739842579 8786737624337072609763869)
          ·
            refine ⟨3295026609126402228661451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8786737624337072609763869 3295026609126402228661451)
            ·
              refine ⟨4942539913689603342992177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3295026609126402228661451 4942539913689603342992177)
              ·
                refine ⟨3706904935267202507244133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4942539913689603342992177 3706904935267202507244133)
                ·
                  refine ⟨695044675362600470108275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3706904935267202507244133 695044675362600470108275)
                  ·
                    refine ⟨1042567013043900705162413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 695044675362600470108275 1042567013043900705162413)
                    ·
                      refine ⟨390962629891462764435905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1042567013043900705162413 390962629891462764435905)
                      ·
                        rfl

theorem cell23_761397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_761397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761397 prefixEnd_761397 := by exact prefixLift 761397
  have htrace : WordTrace (prefixWord ++ tailWord_761397) baseStart_761397 baseEnd_761397 := by
    simpa [prefixWord, tailWord_761397, baseEnd_761397] using wordTrace_append hprefix tailTrace_761397
  have hstable : (prefixWord ++ tailWord_761397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761397).length < 2 ^ (prefixWord ++ tailWord_761397).sum := by decide
  have hdescent : baseEnd_761397 < baseStart_761397 := by decide
  rcases family_descends (prefixWord ++ tailWord_761397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761423 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_761423 : Nat := 118140960795 + 761423 * 2 ^ 59
def prefixEnd_761423 : Nat := 4983230072969 + 3 ^ 40 * 761423 * 2
def baseEnd_761423 : Nat := 390975980388479662710785

theorem tailTrace_761423 : CollatzResearch.WordTrace tailWord_761423 prefixEnd_761423 390975980388479662710785 := by
  unfold tailWord_761423
  simp only [CollatzResearch.WordTrace]
  refine ⟨27771378320501986540440923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18514252213667991026960615 27771378320501986540440923)
  ·
    refine ⟨41657067480752979810661385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27771378320501986540440923 41657067480752979810661385)
    ·
      refine ⟨31242800610564734857996039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41657067480752979810661385 31242800610564734857996039)
      ·
        refine ⟨46864200915847102286994059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31242800610564734857996039 46864200915847102286994059)
        ·
          refine ⟨70296301373770653430491089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46864200915847102286994059 70296301373770653430491089)
          ·
            refine ⟨52722226030327990072868317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70296301373770653430491089 52722226030327990072868317)
            ·
              refine ⟨19770834761372996277325619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52722226030327990072868317 19770834761372996277325619)
              ·
                refine ⟨29656252142059494415988429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19770834761372996277325619 29656252142059494415988429)
                ·
                  refine ⟨11121094553272310405995661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29656252142059494415988429 11121094553272310405995661)
                  ·
                    refine ⟨4170410457477116402248373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11121094553272310405995661 4170410457477116402248373)
                    ·
                      refine ⟨390975980388479662710785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4170410457477116402248373 390975980388479662710785)
                      ·
                        rfl

theorem cell23_761423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_761423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761423 prefixEnd_761423 := by exact prefixLift 761423
  have htrace : WordTrace (prefixWord ++ tailWord_761423) baseStart_761423 baseEnd_761423 := by
    simpa [prefixWord, tailWord_761423, baseEnd_761423] using wordTrace_append hprefix tailTrace_761423
  have hstable : (prefixWord ++ tailWord_761423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761423).length < 2 ^ (prefixWord ++ tailWord_761423).sum := by decide
  have hdescent : baseEnd_761423 < baseStart_761423 := by decide
  rcases family_descends (prefixWord ++ tailWord_761423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761431 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 2, 1, 3]
def baseStart_761431 : Nat := 118140960795 + 761431 * 2 ^ 59
def prefixEnd_761431 : Nat := 4983230072969 + 3 ^ 40 * 761431 * 2
def baseEnd_761431 : Nat := 390980088233715631410749

theorem tailTrace_761431 : CollatzResearch.WordTrace tailWord_761431 prefixEnd_761431 390980088233715631410749 := by
  unfold tailWord_761431
  simp only [CollatzResearch.WordTrace]
  refine ⟨27771670104473003906732147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18514446736315335937821431 27771670104473003906732147)
  ·
    refine ⟨41657505156709505860098221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27771670104473003906732147 41657505156709505860098221)
    ·
      refine ⟨15621564433766064697536833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41657505156709505860098221 15621564433766064697536833)
      ·
        refine ⟨11716173325324548523152625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15621564433766064697536833 11716173325324548523152625)
        ·
          refine ⟨8787129993993411392364469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11716173325324548523152625 8787129993993411392364469)
          ·
            refine ⟨823793436936882318034169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8787129993993411392364469 823793436936882318034169)
            ·
              refine ⟨617845077702661738525627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823793436936882318034169 617845077702661738525627)
              ·
                refine ⟨926767616553992607788441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617845077702661738525627 926767616553992607788441)
                ·
                  refine ⟨695075712415494455841331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 926767616553992607788441 695075712415494455841331)
                  ·
                    refine ⟨1042613568623241683761997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 695075712415494455841331 1042613568623241683761997)
                    ·
                      refine ⟨390980088233715631410749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1042613568623241683761997 390980088233715631410749)
                      ·
                        rfl

theorem cell23_761431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_761431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761431 prefixEnd_761431 := by exact prefixLift 761431
  have htrace : WordTrace (prefixWord ++ tailWord_761431) baseStart_761431 baseEnd_761431 := by
    simpa [prefixWord, tailWord_761431, baseEnd_761431] using wordTrace_append hprefix tailTrace_761431
  have hstable : (prefixWord ++ tailWord_761431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761431).length < 2 ^ (prefixWord ++ tailWord_761431).sum := by decide
  have hdescent : baseEnd_761431 < baseStart_761431 := by decide
  rcases family_descends (prefixWord ++ tailWord_761431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761433 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_761433 : Nat := 118140960795 + 761433 * 2 ^ 59
def prefixEnd_761433 : Nat := 4983230072969 + 3 ^ 40 * 761433 * 2
def baseEnd_761433 : Nat := 390981115195024623585739

theorem tailTrace_761433 : CollatzResearch.WordTrace tailWord_761433 prefixEnd_761433 390981115195024623585739 := by
  unfold tailWord_761433
  simp only [CollatzResearch.WordTrace]
  refine ⟨27771743050465758248304953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18514495366977172165536635 27771743050465758248304953)
  ·
    refine ⟨20828807287849318686228715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27771743050465758248304953 20828807287849318686228715)
    ·
      refine ⟨31243210931773978029343073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20828807287849318686228715 31243210931773978029343073)
      ·
        refine ⟨23432408198830483522007305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31243210931773978029343073 23432408198830483522007305)
        ·
          refine ⟨17574306149122862641505479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23432408198830483522007305 17574306149122862641505479)
          ·
            refine ⟨26361459223684293962258219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17574306149122862641505479 26361459223684293962258219)
            ·
              refine ⟨39542188835526440943387329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26361459223684293962258219 39542188835526440943387329)
              ·
                refine ⟨29656641626644830707540497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39542188835526440943387329 29656641626644830707540497)
                ·
                  refine ⟨22242481219983623030655373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29656641626644830707540497 22242481219983623030655373)
                  ·
                    refine ⟨8340930457493858636495765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22242481219983623030655373 8340930457493858636495765)
                    ·
                      refine ⟨390981115195024623585739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8340930457493858636495765 390981115195024623585739)
                      ·
                        rfl

theorem cell23_761433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_761433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761433 prefixEnd_761433 := by exact prefixLift 761433
  have htrace : WordTrace (prefixWord ++ tailWord_761433) baseStart_761433 baseEnd_761433 := by
    simpa [prefixWord, tailWord_761433, baseEnd_761433] using wordTrace_append hprefix tailTrace_761433
  have hstable : (prefixWord ++ tailWord_761433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761433).length < 2 ^ (prefixWord ++ tailWord_761433).sum := by decide
  have hdescent : baseEnd_761433 < baseStart_761433 := by decide
  rcases family_descends (prefixWord ++ tailWord_761433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761477 : List Nat := [1, 3, 1, 1, 4, 1, 3, 4, 5]
def baseStart_761477 : Nat := 118140960795 + 761477 * 2 ^ 59
def prefixEnd_761477 : Nat := 4983230072969 + 3 ^ 40 * 761477 * 2
def baseEnd_761477 : Nat := 43444856482646939048393

theorem tailTrace_761477 : CollatzResearch.WordTrace tailWord_761477 prefixEnd_761477 43444856482646939048393 := by
  unfold tailWord_761477
  simp only [CollatzResearch.WordTrace]
  refine ⟨27773347862306353762906685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18515565241537569175271123 27773347862306353762906685)
  ·
    refine ⟨10415005448364882661090007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27773347862306353762906685 10415005448364882661090007)
    ·
      refine ⟨15622508172547323991635011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10415005448364882661090007 15622508172547323991635011)
      ·
        refine ⟨23433762258820985987452517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15622508172547323991635011 23433762258820985987452517)
        ·
          refine ⟨4393830423528934872647347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23433762258820985987452517 4393830423528934872647347)
          ·
            refine ⟨6590745635293402308971021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393830423528934872647347 6590745635293402308971021)
            ·
              refine ⟨2471529613235025865864133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6590745635293402308971021 2471529613235025865864133)
              ·
                refine ⟨463411802481567349849525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2471529613235025865864133 463411802481567349849525)
                ·
                  refine ⟨43444856482646939048393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 463411802481567349849525 43444856482646939048393)
                  ·
                    rfl

theorem cell23_761477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_761477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761477 prefixEnd_761477 := by exact prefixLift 761477
  have htrace : WordTrace (prefixWord ++ tailWord_761477) baseStart_761477 baseEnd_761477 := by
    simpa [prefixWord, tailWord_761477, baseEnd_761477] using wordTrace_append hprefix tailTrace_761477
  have hstable : (prefixWord ++ tailWord_761477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761477).length < 2 ^ (prefixWord ++ tailWord_761477).sum := by decide
  have hdescent : baseEnd_761477 < baseStart_761477 := by decide
  rcases family_descends (prefixWord ++ tailWord_761477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761554 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_761554 : Nat := 118140960795 + 761554 * 2 ^ 59
def prefixEnd_761554 : Nat := 4983230072969 + 3 ^ 40 * 761554 * 2
def baseEnd_761554 : Nat := 130347748784739550057561

theorem tailTrace_761554 : CollatzResearch.WordTrace tailWord_761554 prefixEnd_761554 130347748784739550057561 := by
  unfold tailWord_761554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944039070756848978364929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18517437522018263942306477 6944039070756848978364929)
  ·
    refine ⟨5208029303067636733773697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6944039070756848978364929 5208029303067636733773697)
    ·
      refine ⟨3906021977300727550330273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5208029303067636733773697 3906021977300727550330273)
      ·
        refine ⟨2929516482975545662747705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3906021977300727550330273 2929516482975545662747705)
        ·
          refine ⟨2197137362231659247060779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2929516482975545662747705 2197137362231659247060779)
          ·
            refine ⟨3295706043347488870591169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197137362231659247060779 3295706043347488870591169)
            ·
              refine ⟨2471779532510616652943377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3295706043347488870591169 2471779532510616652943377)
              ·
                refine ⟨1853834649382962489707533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471779532510616652943377 1853834649382962489707533)
                ·
                  refine ⟨695187993518610933640325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1853834649382962489707533 695187993518610933640325)
                  ·
                    refine ⟨130347748784739550057561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 695187993518610933640325 130347748784739550057561)
                    ·
                      rfl

theorem cell23_761554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_761554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761554 prefixEnd_761554 := by exact prefixLift 761554
  have htrace : WordTrace (prefixWord ++ tailWord_761554) baseStart_761554 baseEnd_761554 := by
    simpa [prefixWord, tailWord_761554, baseEnd_761554] using wordTrace_append hprefix tailTrace_761554
  have hstable : (prefixWord ++ tailWord_761554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761554).length < 2 ^ (prefixWord ++ tailWord_761554).sum := by decide
  have hdescent : baseEnd_761554 < baseStart_761554 := by decide
  rcases family_descends (prefixWord ++ tailWord_761554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761588 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_761588 : Nat := 118140960795 + 761588 * 2 ^ 59
def prefixEnd_761588 : Nat := 4983230072969 + 3 ^ 40 * 761588 * 2
def baseEnd_761588 : Nat := 130353568232157172382509

theorem tailTrace_761588 : CollatzResearch.WordTrace tailWord_761588 prefixEnd_761588 130353568232157172382509 := by
  unfold tailWord_761588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13888698182452109860098709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18518264243269479813464945 13888698182452109860098709)
  ·
    refine ⟨651032727302442649692127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13888698182452109860098709 651032727302442649692127)
    ·
      refine ⟨976549090953663974538191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 651032727302442649692127 976549090953663974538191)
      ·
        refine ⟨1464823636430495961807287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 976549090953663974538191 1464823636430495961807287)
        ·
          refine ⟨2197235454645743942710931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464823636430495961807287 2197235454645743942710931)
          ·
            refine ⟨3295853181968615914066397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197235454645743942710931 3295853181968615914066397)
            ·
              refine ⟨1235944943238230967774899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3295853181968615914066397 1235944943238230967774899)
              ·
                refine ⟨1853917414857346451662349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235944943238230967774899 1853917414857346451662349)
                ·
                  refine ⟨695219030571504919373381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1853917414857346451662349 695219030571504919373381)
                  ·
                    refine ⟨130353568232157172382509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 695219030571504919373381 130353568232157172382509)
                    ·
                      rfl

theorem cell23_761588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_761588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761588 prefixEnd_761588 := by exact prefixLift 761588
  have htrace : WordTrace (prefixWord ++ tailWord_761588) baseStart_761588 baseEnd_761588 := by
    simpa [prefixWord, tailWord_761588, baseEnd_761588] using wordTrace_append hprefix tailTrace_761588
  have hstable : (prefixWord ++ tailWord_761588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761588).length < 2 ^ (prefixWord ++ tailWord_761588).sum := by decide
  have hdescent : baseEnd_761588 < baseStart_761588 := by decide
  rcases family_descends (prefixWord ++ tailWord_761588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761614 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_761614 : Nat := 118140960795 + 761614 * 2 ^ 59
def prefixEnd_761614 : Nat := 4983230072969 + 3 ^ 40 * 761614 * 2
def baseEnd_761614 : Nat := 130358018397829471807469

theorem tailTrace_761614 : CollatzResearch.WordTrace tailWord_761614 prefixEnd_761614 130358018397829471807469 := by
  unfold tailWord_761614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3472293082851253270080487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18518896441873350773762597 3472293082851253270080487)
  ·
    refine ⟨5208439624276879905120731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3472293082851253270080487 5208439624276879905120731)
    ·
      refine ⟨7812659436415319857681097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5208439624276879905120731 7812659436415319857681097)
      ·
        refine ⟨5859494577311489893260823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7812659436415319857681097 5859494577311489893260823)
        ·
          refine ⟨8789241865967234839891235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859494577311489893260823 8789241865967234839891235)
          ·
            refine ⟨13183862798950852259836853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8789241865967234839891235 13183862798950852259836853)
            ·
              refine ⟨1235987137401642399359705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13183862798950852259836853 1235987137401642399359705)
              ·
                refine ⟨926990353051231799519779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235987137401642399359705 926990353051231799519779)
                ·
                  refine ⟨1390485529576847699279669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926990353051231799519779 1390485529576847699279669)
                  ·
                    refine ⟨130358018397829471807469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1390485529576847699279669 130358018397829471807469)
                    ·
                      rfl

theorem cell23_761614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_761614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761614 prefixEnd_761614 := by exact prefixLift 761614
  have htrace : WordTrace (prefixWord ++ tailWord_761614) baseStart_761614 baseEnd_761614 := by
    simpa [prefixWord, tailWord_761614, baseEnd_761614] using wordTrace_append hprefix tailTrace_761614
  have hstable : (prefixWord ++ tailWord_761614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761614).length < 2 ^ (prefixWord ++ tailWord_761614).sum := by decide
  have hdescent : baseEnd_761614 < baseStart_761614 := by decide
  rcases family_descends (prefixWord ++ tailWord_761614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761621 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_761621 : Nat := 118140960795 + 761621 * 2 ^ 59
def prefixEnd_761621 : Nat := 4983230072969 + 3 ^ 40 * 761621 * 2
def baseEnd_761621 : Nat := 391077649558069888034875

theorem tailTrace_761621 : CollatzResearch.WordTrace tailWord_761621 prefixEnd_761621 391077649558069888034875 := by
  unfold tailWord_761621
  simp only [CollatzResearch.WordTrace]
  refine ⟨27778599973784666356148717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18519066649189777570765811 27778599973784666356148717)
  ·
    refine ⟨10416974990169249883555769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27778599973784666356148717 10416974990169249883555769)
    ·
      refine ⟨7812731242626937412666827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10416974990169249883555769 7812731242626937412666827)
      ·
        refine ⟨11719096863940406119000241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7812731242626937412666827 11719096863940406119000241)
        ·
          refine ⟨8789322647955304589250181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11719096863940406119000241 8789322647955304589250181)
          ·
            refine ⟨1647997996491619610484409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8789322647955304589250181 1647997996491619610484409)
            ·
              refine ⟨1235998497368714707863307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647997996491619610484409 1235998497368714707863307)
              ·
                refine ⟨1853997746053072061794961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235998497368714707863307 1853997746053072061794961)
                ·
                  refine ⟨1390498309539804046346221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1853997746053072061794961 1390498309539804046346221)
                  ·
                    refine ⟨521436866077426517379833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390498309539804046346221 521436866077426517379833)
                    ·
                      refine ⟨391077649558069888034875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521436866077426517379833 391077649558069888034875)
                      ·
                        rfl

theorem cell23_761621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_761621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761621 prefixEnd_761621 := by exact prefixLift 761621
  have htrace : WordTrace (prefixWord ++ tailWord_761621) baseStart_761621 baseEnd_761621 := by
    simpa [prefixWord, tailWord_761621, baseEnd_761621] using wordTrace_append hprefix tailTrace_761621
  have hstable : (prefixWord ++ tailWord_761621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761621).length < 2 ^ (prefixWord ++ tailWord_761621).sum := by decide
  have hdescent : baseEnd_761621 < baseStart_761621 := by decide
  rcases family_descends (prefixWord ++ tailWord_761621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761644 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_761644 : Nat := 118140960795 + 761644 * 2 ^ 59
def prefixEnd_761644 : Nat := 4983230072969 + 3 ^ 40 * 761644 * 2
def baseEnd_761644 : Nat := 130363153204374432682423

theorem tailTrace_761644 : CollatzResearch.WordTrace tailWord_761644 prefixEnd_761644 130363153204374432682423 := by
  unfold tailWord_761644
  simp only [CollatzResearch.WordTrace]
  refine ⟨13889719426350670642117993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18519625901800894189490657 13889719426350670642117993)
  ·
    refine ⟨10417289569763002981588495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13889719426350670642117993 10417289569763002981588495)
    ·
      refine ⟨15625934354644504472382743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417289569763002981588495 15625934354644504472382743)
      ·
        refine ⟨23438901531966756708574115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15625934354644504472382743 23438901531966756708574115)
        ·
          refine ⟨35158352297950135062861173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23438901531966756708574115 35158352297950135062861173)
          ·
            refine ⟨3296095527932825162143235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35158352297950135062861173 3296095527932825162143235)
            ·
              refine ⟨4944143291899237743214853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296095527932825162143235 4944143291899237743214853)
              ·
                refine ⟨927026867231107076852785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4944143291899237743214853 927026867231107076852785)
                ·
                  refine ⟨695270150423330307639589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 927026867231107076852785 695270150423330307639589)
                  ·
                    refine ⟨130363153204374432682423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 695270150423330307639589 130363153204374432682423)
                    ·
                      rfl

theorem cell23_761644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_761644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761644 prefixEnd_761644 := by exact prefixLift 761644
  have htrace : WordTrace (prefixWord ++ tailWord_761644) baseStart_761644 baseEnd_761644 := by
    simpa [prefixWord, tailWord_761644, baseEnd_761644] using wordTrace_append hprefix tailTrace_761644
  have hstable : (prefixWord ++ tailWord_761644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761644).length < 2 ^ (prefixWord ++ tailWord_761644).sum := by decide
  have hdescent : baseEnd_761644 < baseStart_761644 := by decide
  rcases family_descends (prefixWord ++ tailWord_761644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761661 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_761661 : Nat := 118140960795 + 761661 * 2 ^ 59
def prefixEnd_761661 : Nat := 4983230072969 + 3 ^ 40 * 761661 * 2
def baseEnd_761661 : Nat := 130366062928083243844897

theorem tailTrace_761661 : CollatzResearch.WordTrace tailWord_761661 prefixEnd_761661 130366062928083243844897 := by
  unfold tailWord_761661
  simp only [CollatzResearch.WordTrace]
  refine ⟨27780058893639753187604837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18520039262426502125069891 27780058893639753187604837)
  ·
    refine ⟨5208761042557453722675907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27780058893639753187604837 5208761042557453722675907)
    ·
      refine ⟨7813141563836180584013861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5208761042557453722675907 7813141563836180584013861)
      ·
        refine ⟨1464964043219283859502599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7813141563836180584013861 1464964043219283859502599)
        ·
          refine ⟨2197446064828925789253899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464964043219283859502599 2197446064828925789253899)
          ·
            refine ⟨3296169097243388683880849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197446064828925789253899 3296169097243388683880849)
            ·
              refine ⟨2472126822932541512910637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296169097243388683880849 2472126822932541512910637)
              ·
                refine ⟨927047558599703067341489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2472126822932541512910637 927047558599703067341489)
                ·
                  refine ⟨695285668949777300506117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 927047558599703067341489 695285668949777300506117)
                  ·
                    refine ⟨130366062928083243844897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 695285668949777300506117 130366062928083243844897)
                    ·
                      rfl

theorem cell23_761661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_761661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761661 prefixEnd_761661 := by exact prefixLift 761661
  have htrace : WordTrace (prefixWord ++ tailWord_761661) baseStart_761661 baseEnd_761661 := by
    simpa [prefixWord, tailWord_761661, baseEnd_761661] using wordTrace_append hprefix tailTrace_761661
  have hstable : (prefixWord ++ tailWord_761661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761661).length < 2 ^ (prefixWord ++ tailWord_761661).sum := by decide
  have hdescent : baseEnd_761661 < baseStart_761661 := by decide
  rcases family_descends (prefixWord ++ tailWord_761661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761685 : List Nat := [1, 3, 2, 2, 2, 3, 2, 3, 1, 2, 2]
def baseStart_761685 : Nat := 118140960795 + 761685 * 2 ^ 59
def prefixEnd_761685 : Nat := 4983230072969 + 3 ^ 40 * 761685 * 2
def baseEnd_761685 : Nat := 391110512319957637634581

theorem tailTrace_761685 : CollatzResearch.WordTrace tailWord_761685 prefixEnd_761685 391110512319957637634581 := by
  unfold tailWord_761685
  simp only [CollatzResearch.WordTrace]
  refine ⟨27780934245552805286478509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18520622830368536857652339 27780934245552805286478509)
  ·
    refine ⟨10417850342082301982429441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27780934245552805286478509 10417850342082301982429441)
    ·
      refine ⟨7813387756561726486822081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10417850342082301982429441 7813387756561726486822081)
      ·
        refine ⟨5860040817421294865116561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7813387756561726486822081 5860040817421294865116561)
        ·
          refine ⟨4395030613065971148837421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5860040817421294865116561 4395030613065971148837421)
          ·
            refine ⟨1648136479899739180814033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4395030613065971148837421 1648136479899739180814033)
            ·
              refine ⟨1236102359924804385610525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1648136479899739180814033 1236102359924804385610525)
              ·
                refine ⟨463538384971801644603947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1236102359924804385610525 463538384971801644603947)
                ·
                  refine ⟨695307577457702466905921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463538384971801644603947 695307577457702466905921)
                  ·
                    refine ⟨521480683093276850179441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 695307577457702466905921 521480683093276850179441)
                    ·
                      refine ⟨391110512319957637634581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521480683093276850179441 391110512319957637634581)
                      ·
                        rfl

theorem cell23_761685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_761685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761685 prefixEnd_761685 := by exact prefixLift 761685
  have htrace : WordTrace (prefixWord ++ tailWord_761685) baseStart_761685 baseEnd_761685 := by
    simpa [prefixWord, tailWord_761685, baseEnd_761685] using wordTrace_append hprefix tailTrace_761685
  have hstable : (prefixWord ++ tailWord_761685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761685).length < 2 ^ (prefixWord ++ tailWord_761685).sum := by decide
  have hdescent : baseEnd_761685 < baseStart_761685 := by decide
  rcases family_descends (prefixWord ++ tailWord_761685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761727 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_761727 : Nat := 118140960795 + 761727 * 2 ^ 59
def prefixEnd_761727 : Nat := 4983230072969 + 3 ^ 40 * 761727 * 2
def baseEnd_761727 : Nat := 391132078507446473309387

theorem tailTrace_761727 : CollatzResearch.WordTrace tailWord_761727 prefixEnd_761727 391132078507446473309387 := by
  unfold tailWord_761727
  simp only [CollatzResearch.WordTrace]
  refine ⟨27782466111400646459507435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18521644074267097639671623 27782466111400646459507435)
  ·
    refine ⟨41673699167100969689261153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27782466111400646459507435 41673699167100969689261153)
    ·
      refine ⟨31255274375325727266945865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41673699167100969689261153 31255274375325727266945865)
      ·
        refine ⟨23441455781494295450209399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31255274375325727266945865 23441455781494295450209399)
        ·
          refine ⟨35162183672241443175314099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23441455781494295450209399 35162183672241443175314099)
          ·
            refine ⟨52743275508362164762971149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35162183672241443175314099 52743275508362164762971149)
            ·
              refine ⟨19778728315635811786114181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52743275508362164762971149 19778728315635811786114181)
              ·
                refine ⟨3708511559181714709896409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19778728315635811786114181 3708511559181714709896409)
                ·
                  refine ⟨2781383669386286032422307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3708511559181714709896409 2781383669386286032422307)
                  ·
                    refine ⟨4172075504079429048633461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2781383669386286032422307 4172075504079429048633461)
                    ·
                      refine ⟨391132078507446473309387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4172075504079429048633461 391132078507446473309387)
                      ·
                        rfl

theorem cell23_761727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_761727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761727 prefixEnd_761727 := by exact prefixLift 761727
  have htrace : WordTrace (prefixWord ++ tailWord_761727) baseStart_761727 baseEnd_761727 := by
    simpa [prefixWord, tailWord_761727, baseEnd_761727] using wordTrace_append hprefix tailTrace_761727
  have hstable : (prefixWord ++ tailWord_761727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761727).length < 2 ^ (prefixWord ++ tailWord_761727).sum := by decide
  have hdescent : baseEnd_761727 < baseStart_761727 := by decide
  rcases family_descends (prefixWord ++ tailWord_761727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761764 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 7]
def baseStart_761764 : Nat := 118140960795 + 761764 * 2 ^ 59
def prefixEnd_761764 : Nat := 4983230072969 + 3 ^ 40 * 761764 * 2
def baseEnd_761764 : Nat := 43461230810184758727413

theorem tailTrace_761764 : CollatzResearch.WordTrace tailWord_761764 prefixEnd_761764 43461230810184758727413 := by
  unfold tailWord_761764
  simp only [CollatzResearch.WordTrace]
  refine ⟨13891907806133300889302173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18522543741511067852402897 13891907806133300889302173)
  ·
    refine ⟨5209465427299987833488315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13891907806133300889302173 5209465427299987833488315)
    ·
      refine ⟨7814198140949981750232473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5209465427299987833488315 7814198140949981750232473)
      ·
        refine ⟨5860648605712486312674355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7814198140949981750232473 5860648605712486312674355)
        ·
          refine ⟨8790972908568729469011533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5860648605712486312674355 8790972908568729469011533)
          ·
            refine ⟨3296614840713273550879325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8790972908568729469011533 3296614840713273550879325)
            ·
              refine ⟨1236230565267477581579747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3296614840713273550879325 1236230565267477581579747)
              ·
                refine ⟨1854345847901216372369621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236230565267477581579747 1854345847901216372369621)
                ·
                  refine ⟨43461230810184758727413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1854345847901216372369621 43461230810184758727413)
                  ·
                    rfl

theorem cell23_761764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_761764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761764 prefixEnd_761764 := by exact prefixLift 761764
  have htrace : WordTrace (prefixWord ++ tailWord_761764) baseStart_761764 baseEnd_761764 := by
    simpa [prefixWord, tailWord_761764, baseEnd_761764] using wordTrace_append hprefix tailTrace_761764
  have hstable : (prefixWord ++ tailWord_761764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761764).length < 2 ^ (prefixWord ++ tailWord_761764).sum := by decide
  have hdescent : baseEnd_761764 < baseStart_761764 := by decide
  rcases family_descends (prefixWord ++ tailWord_761764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761787 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 5]
def baseStart_761787 : Nat := 118140960795 + 761787 * 2 ^ 59
def prefixEnd_761787 : Nat := 4983230072969 + 3 ^ 40 * 761787 * 2
def baseEnd_761787 : Nat := 391162887346716238559111

theorem tailTrace_761787 : CollatzResearch.WordTrace tailWord_761787 prefixEnd_761787 391162887346716238559111 := by
  unfold tailWord_761787
  simp only [CollatzResearch.WordTrace]
  refine ⟨27784654491183276706691615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18523102994122184471127743 27784654491183276706691615)
  ·
    refine ⟨41676981736774915060037423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27784654491183276706691615 41676981736774915060037423)
    ·
      refine ⟨62515472605162372590056135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41676981736774915060037423 62515472605162372590056135)
      ·
        refine ⟨93773208907743558885084203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62515472605162372590056135 93773208907743558885084203)
        ·
          refine ⟨140659813361615338327626305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93773208907743558885084203 140659813361615338327626305)
          ·
            refine ⟨105494860021211503745719729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140659813361615338327626305 105494860021211503745719729)
            ·
              refine ⟨79121145015908627809289797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105494860021211503745719729 79121145015908627809289797)
              ·
                refine ⟨14835214690482867714241837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79121145015908627809289797 14835214690482867714241837)
                ·
                  refine ⟨5563205508931075392840689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14835214690482867714241837 5563205508931075392840689)
                  ·
                    refine ⟨4172404131698306544630517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563205508931075392840689 4172404131698306544630517)
                    ·
                      refine ⟨391162887346716238559111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4172404131698306544630517 391162887346716238559111)
                      ·
                        rfl

theorem cell23_761787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_761787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761787 prefixEnd_761787 := by exact prefixLift 761787
  have htrace : WordTrace (prefixWord ++ tailWord_761787) baseStart_761787 baseEnd_761787 := by
    simpa [prefixWord, tailWord_761787, baseEnd_761787] using wordTrace_append hprefix tailTrace_761787
  have hstable : (prefixWord ++ tailWord_761787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761787).length < 2 ^ (prefixWord ++ tailWord_761787).sum := by decide
  have hdescent : baseEnd_761787 < baseStart_761787 := by decide
  rcases family_descends (prefixWord ++ tailWord_761787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761804 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_761804 : Nat := 118140960795 + 761804 * 2 ^ 59
def prefixEnd_761804 : Nat := 4983230072969 + 3 ^ 40 * 761804 * 2
def baseEnd_761804 : Nat := 391171616517842672046533

theorem tailTrace_761804 : CollatzResearch.WordTrace tailWord_761804 prefixEnd_761804 391171616517842672046533 := by
  unfold tailWord_761804
  simp only [CollatzResearch.WordTrace]
  refine ⟨13892637266060844305030233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18523516354747792406706977 13892637266060844305030233)
  ·
    refine ⟨10419477949545633228772675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13892637266060844305030233 10419477949545633228772675)
    ·
      refine ⟨15629216924318449843159013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10419477949545633228772675 15629216924318449843159013)
      ·
        refine ⟨2930478173309709345592315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15629216924318449843159013 2930478173309709345592315)
        ·
          refine ⟨4395717259964564018388473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930478173309709345592315 4395717259964564018388473)
          ·
            refine ⟨3296787944973423013791355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4395717259964564018388473 3296787944973423013791355)
            ·
              refine ⟨4945181917460134520687033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296787944973423013791355 4945181917460134520687033)
              ·
                refine ⟨3708886438095100890515275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4945181917460134520687033 3708886438095100890515275)
                ·
                  refine ⟨5563329657142651335772913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708886438095100890515275 5563329657142651335772913)
                  ·
                    refine ⟨4172497242856988501829685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5563329657142651335772913 4172497242856988501829685)
                    ·
                      refine ⟨391171616517842672046533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4172497242856988501829685 391171616517842672046533)
                      ·
                        rfl

theorem cell23_761804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_761804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761804 prefixEnd_761804 := by exact prefixLift 761804
  have htrace : WordTrace (prefixWord ++ tailWord_761804) baseStart_761804 baseEnd_761804 := by
    simpa [prefixWord, tailWord_761804, baseEnd_761804] using wordTrace_append hprefix tailTrace_761804
  have hstable : (prefixWord ++ tailWord_761804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761804).length < 2 ^ (prefixWord ++ tailWord_761804).sum := by decide
  have hdescent : baseEnd_761804 < baseStart_761804 := by decide
  rcases family_descends (prefixWord ++ tailWord_761804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761824 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 7, 4]
def baseStart_761824 : Nat := 118140960795 + 761824 * 2 ^ 59
def prefixEnd_761824 : Nat := 4983230072969 + 3 ^ 40 * 761824 * 2
def baseEnd_761824 : Nat := 130393962043644197932147

theorem tailTrace_761824 : CollatzResearch.WordTrace tailWord_761824 prefixEnd_761824 130393962043644197932147 := by
  unfold tailWord_761824
  simp only [CollatzResearch.WordTrace]
  refine ⟨13893001996024616012894263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18524002661366154683859017 13893001996024616012894263)
  ·
    refine ⟨20839502994036924019341395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13893001996024616012894263 20839502994036924019341395)
    ·
      refine ⟨31259254491055386029012093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20839502994036924019341395 31259254491055386029012093)
      ·
        refine ⟨11722220434145769760879535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31259254491055386029012093 11722220434145769760879535)
        ·
          refine ⟨17583330651218654641319303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11722220434145769760879535 17583330651218654641319303)
          ·
            refine ⟨26374995976827981961978955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17583330651218654641319303 26374995976827981961978955)
            ·
              refine ⟨39562493965241972942968433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26374995976827981961978955 39562493965241972942968433)
              ·
                refine ⟨29671870473931479707226325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39562493965241972942968433 29671870473931479707226325)
                ·
                  refine ⟨695434464232769055638117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 29671870473931479707226325 695434464232769055638117)
                  ·
                    refine ⟨130393962043644197932147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 695434464232769055638117 130393962043644197932147)
                    ·
                      rfl

theorem cell23_761824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 4].length) (baseStart_761824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761824 prefixEnd_761824 := by exact prefixLift 761824
  have htrace : WordTrace (prefixWord ++ tailWord_761824) baseStart_761824 baseEnd_761824 := by
    simpa [prefixWord, tailWord_761824, baseEnd_761824] using wordTrace_append hprefix tailTrace_761824
  have hstable : (prefixWord ++ tailWord_761824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761824).length < 2 ^ (prefixWord ++ tailWord_761824).sum := by decide
  have hdescent : baseEnd_761824 < baseStart_761824 := by decide
  rcases family_descends (prefixWord ++ tailWord_761824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761851 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 3]
def baseStart_761851 : Nat := 118140960795 + 761851 * 2 ^ 59
def prefixEnd_761851 : Nat := 4983230072969 + 3 ^ 40 * 761851 * 2
def baseEnd_761851 : Nat := 391195750108603988158817

theorem tailTrace_761851 : CollatzResearch.WordTrace tailWord_761851 prefixEnd_761851 391195750108603988158817 := by
  unfold tailWord_761851
  simp only [CollatzResearch.WordTrace]
  refine ⟨27786988762951415637021407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18524659175300943758014271 27786988762951415637021407)
  ·
    refine ⟨41680483144427123455532111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27786988762951415637021407 41680483144427123455532111)
    ·
      refine ⟨62520724716640685183298167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41680483144427123455532111 62520724716640685183298167)
      ·
        refine ⟨93781087074961027774947251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62520724716640685183298167 93781087074961027774947251)
        ·
          refine ⟨140671630612441541662420877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93781087074961027774947251 140671630612441541662420877)
          ·
            refine ⟨52751861479665578123407829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140671630612441541662420877 52751861479665578123407829)
            ·
              refine ⟨1236371753429661987267371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 52751861479665578123407829 1236371753429661987267371)
              ·
                refine ⟨1854557630144492980901057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236371753429661987267371 1854557630144492980901057)
                ·
                  refine ⟨1390918222608369735675793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1854557630144492980901057 1390918222608369735675793)
                  ·
                    refine ⟨1043188666956277301756845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1390918222608369735675793 1043188666956277301756845)
                    ·
                      refine ⟨391195750108603988158817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1043188666956277301756845 391195750108603988158817)
                      ·
                        rfl

theorem cell23_761851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 3].length) (baseStart_761851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761851 prefixEnd_761851 := by exact prefixLift 761851
  have htrace : WordTrace (prefixWord ++ tailWord_761851) baseStart_761851 baseEnd_761851 := by
    simpa [prefixWord, tailWord_761851, baseEnd_761851] using wordTrace_append hprefix tailTrace_761851
  have hstable : (prefixWord ++ tailWord_761851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761851).length < 2 ^ (prefixWord ++ tailWord_761851).sum := by decide
  have hdescent : baseEnd_761851 < baseStart_761851 := by decide
  rcases family_descends (prefixWord ++ tailWord_761851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761891 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 3, 5, 2]
def baseStart_761891 : Nat := 118140960795 + 761891 * 2 ^ 59
def prefixEnd_761891 : Nat := 4983230072969 + 3 ^ 40 * 761891 * 2
def baseEnd_761891 : Nat := 391216289334783831658633

theorem tailTrace_761891 : CollatzResearch.WordTrace tailWord_761891 prefixEnd_761891 391216289334783831658633 := by
  unfold tailWord_761891
  simp only [CollatzResearch.WordTrace]
  refine ⟨27788447682806502468477527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18525631788537668312318351 27788447682806502468477527)
  ·
    refine ⟨41682671524209753702716291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27788447682806502468477527 41682671524209753702716291)
    ·
      refine ⟨62524007286314630554074437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41682671524209753702716291 62524007286314630554074437)
      ·
        refine ⟨11723251366183993228888957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62524007286314630554074437 11723251366183993228888957)
        ·
          refine ⟨4396219262318997460833359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11723251366183993228888957 4396219262318997460833359)
          ·
            refine ⟨6594328893478496191250039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396219262318997460833359 6594328893478496191250039)
            ·
              refine ⟨9891493340217744286875059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6594328893478496191250039 9891493340217744286875059)
              ·
                refine ⟨14837240010326616430312589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9891493340217744286875059 14837240010326616430312589)
                ·
                  refine ⟨5563965003872481161367221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14837240010326616430312589 5563965003872481161367221)
                  ·
                    refine ⟨521621719113045108878177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5563965003872481161367221 521621719113045108878177)
                    ·
                      refine ⟨391216289334783831658633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521621719113045108878177 391216289334783831658633)
                      ·
                        rfl

theorem cell23_761891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_761891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761891 prefixEnd_761891 := by exact prefixLift 761891
  have htrace : WordTrace (prefixWord ++ tailWord_761891) baseStart_761891 baseEnd_761891 := by
    simpa [prefixWord, tailWord_761891, baseEnd_761891] using wordTrace_append hprefix tailTrace_761891
  have hstable : (prefixWord ++ tailWord_761891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761891).length < 2 ^ (prefixWord ++ tailWord_761891).sum := by decide
  have hdescent : baseEnd_761891 < baseStart_761891 := by decide
  rcases family_descends (prefixWord ++ tailWord_761891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761914 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_761914 : Nat := 118140960795 + 761914 * 2 ^ 59
def prefixEnd_761914 : Nat := 4983230072969 + 3 ^ 40 * 761914 * 2
def baseEnd_761914 : Nat := 130409366463279080557009

theorem tailTrace_761914 : CollatzResearch.WordTrace tailWord_761914 prefixEnd_761914 130409366463279080557009 := by
  unfold tailWord_761914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947321640430794349141199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18526191041148784931043197 6947321640430794349141199)
  ·
    refine ⟨10420982460646191523711799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6947321640430794349141199 10420982460646191523711799)
    ·
      refine ⟨15631473690969287285567699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10420982460646191523711799 15631473690969287285567699)
      ·
        refine ⟨23447210536453930928351549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15631473690969287285567699 23447210536453930928351549)
        ·
          refine ⟨8792703951170224098131831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23447210536453930928351549 8792703951170224098131831)
          ·
            refine ⟨13189055926755336147197747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8792703951170224098131831 13189055926755336147197747)
            ·
              refine ⟨19783583890133004220796621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13189055926755336147197747 19783583890133004220796621)
              ·
                refine ⟨7418843958799876582798733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19783583890133004220796621 7418843958799876582798733)
                ·
                  refine ⟨2782066484549953718549525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7418843958799876582798733 2782066484549953718549525)
                  ·
                    refine ⟨130409366463279080557009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2782066484549953718549525 130409366463279080557009)
                    ·
                      rfl

theorem cell23_761914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_761914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761914 prefixEnd_761914 := by exact prefixLift 761914
  have htrace : WordTrace (prefixWord ++ tailWord_761914) baseStart_761914 baseEnd_761914 := by
    simpa [prefixWord, tailWord_761914, baseEnd_761914] using wordTrace_append hprefix tailTrace_761914
  have hstable : (prefixWord ++ tailWord_761914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761914).length < 2 ^ (prefixWord ++ tailWord_761914).sum := by decide
  have hdescent : baseEnd_761914 < baseStart_761914 := by decide
  rcases family_descends (prefixWord ++ tailWord_761914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761941 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_761941 : Nat := 118140960795 + 761941 * 2 ^ 59
def prefixEnd_761941 : Nat := 4983230072969 + 3 ^ 40 * 761941 * 2
def baseEnd_761941 : Nat := 391241963367508636033403

theorem tailTrace_761941 : CollatzResearch.WordTrace tailWord_761941 prefixEnd_761941 391241963367508636033403 := by
  unfold tailWord_761941
  simp only [CollatzResearch.WordTrace]
  refine ⟨27790271332625361007797677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18526847555083574005198451 27790271332625361007797677)
  ·
    refine ⟨10421351749734510377924129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27790271332625361007797677 10421351749734510377924129)
    ·
      refine ⟨7816013812300882783443097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10421351749734510377924129 7816013812300882783443097)
      ·
        refine ⟨5862010359225662087582323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7816013812300882783443097 5862010359225662087582323)
        ·
          refine ⟨8793015538838493131373485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5862010359225662087582323 8793015538838493131373485)
          ·
            refine ⟨3297380827064434924265057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8793015538838493131373485 3297380827064434924265057)
            ·
              refine ⟨2473035620298326193198793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3297380827064434924265057 2473035620298326193198793)
              ·
                refine ⟨1854776715223744644899095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2473035620298326193198793 1854776715223744644899095)
                ·
                  refine ⟨2782165072835616967348643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854776715223744644899095 2782165072835616967348643)
                  ·
                    refine ⟨4173247609253425451022965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2782165072835616967348643 4173247609253425451022965)
                    ·
                      refine ⟨391241963367508636033403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4173247609253425451022965 391241963367508636033403)
                      ·
                        rfl

theorem cell23_761941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_761941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761941 prefixEnd_761941 := by exact prefixLift 761941
  have htrace : WordTrace (prefixWord ++ tailWord_761941) baseStart_761941 baseEnd_761941 := by
    simpa [prefixWord, tailWord_761941, baseEnd_761941] using wordTrace_append hprefix tailTrace_761941
  have hstable : (prefixWord ++ tailWord_761941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761941).length < 2 ^ (prefixWord ++ tailWord_761941).sum := by decide
  have hdescent : baseEnd_761941 < baseStart_761941 := by decide
  rcases family_descends (prefixWord ++ tailWord_761941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761944 : List Nat := [2, 1, 2, 2, 1, 4, 1, 10]
def baseStart_761944 : Nat := 118140960795 + 761944 * 2 ^ 59
def prefixEnd_761944 : Nat := 4983230072969 + 3 ^ 40 * 761944 * 2
def baseEnd_761944 : Nat := 14490500141091560159107

theorem tailTrace_761944 : CollatzResearch.WordTrace tailWord_761944 prefixEnd_761944 14490500141091560159107 := by
  unfold tailWord_761944
  simp only [CollatzResearch.WordTrace]
  refine ⟨13895190375807246260078443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18526920501076328346771257 13895190375807246260078443)
  ·
    refine ⟨20842785563710869390117665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13895190375807246260078443 20842785563710869390117665)
    ·
      refine ⟨15632089172783152042588249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20842785563710869390117665 15632089172783152042588249)
      ·
        refine ⟨11724066879587364031941187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15632089172783152042588249 11724066879587364031941187)
        ·
          refine ⟨17586100319381046047911781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11724066879587364031941187 17586100319381046047911781)
          ·
            refine ⟨3297393809883946133983459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17586100319381046047911781 3297393809883946133983459)
            ·
              refine ⟨4946090714825919200975189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297393809883946133983459 4946090714825919200975189)
              ·
                refine ⟨14490500141091560159107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4946090714825919200975189 14490500141091560159107)
                ·
                  rfl

theorem cell23_761944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 10].length) (baseStart_761944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761944 prefixEnd_761944 := by exact prefixLift 761944
  have htrace : WordTrace (prefixWord ++ tailWord_761944) baseStart_761944 baseEnd_761944 := by
    simpa [prefixWord, tailWord_761944, baseEnd_761944] using wordTrace_append hprefix tailTrace_761944
  have hstable : (prefixWord ++ tailWord_761944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761944).length < 2 ^ (prefixWord ++ tailWord_761944).sum := by decide
  have hdescent : baseEnd_761944 < baseStart_761944 := by decide
  rcases family_descends (prefixWord ++ tailWord_761944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761975 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 1, 2, 3]
def baseStart_761975 : Nat := 118140960795 + 761975 * 2 ^ 59
def prefixEnd_761975 : Nat := 4983230072969 + 3 ^ 40 * 761975 * 2
def baseEnd_761975 : Nat := 391259421709761503008247

theorem tailTrace_761975 : CollatzResearch.WordTrace tailWord_761975 prefixEnd_761975 391259421709761503008247 := by
  unfold tailWord_761975
  simp only [CollatzResearch.WordTrace]
  refine ⟨27791511414502184814535379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18527674276334789876356919 27791511414502184814535379)
  ·
    refine ⟨41687267121753277221803069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27791511414502184814535379 41687267121753277221803069)
    ·
      refine ⟨15632725170657478958176151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41687267121753277221803069 15632725170657478958176151)
      ·
        refine ⟨23449087755986218437264227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15632725170657478958176151 23449087755986218437264227)
        ·
          refine ⟨35173631633979327655896341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23449087755986218437264227 35173631633979327655896341)
          ·
            refine ⟨1648763982842780983870141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35173631633979327655896341 1648763982842780983870141)
            ·
              refine ⟨618286493566042868951303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1648763982842780983870141 618286493566042868951303)
              ·
                refine ⟨927429740349064303426955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618286493566042868951303 927429740349064303426955)
                ·
                  refine ⟨1391144610523596455140433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927429740349064303426955 1391144610523596455140433)
                  ·
                    refine ⟨1043358457892697341355325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1391144610523596455140433 1043358457892697341355325)
                    ·
                      refine ⟨391259421709761503008247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1043358457892697341355325 391259421709761503008247)
                      ·
                        rfl

theorem cell23_761975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_761975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761975 prefixEnd_761975 := by exact prefixLift 761975
  have htrace : WordTrace (prefixWord ++ tailWord_761975) baseStart_761975 baseEnd_761975 := by
    simpa [prefixWord, tailWord_761975, baseEnd_761975] using wordTrace_append hprefix tailTrace_761975
  have hstable : (prefixWord ++ tailWord_761975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761975).length < 2 ^ (prefixWord ++ tailWord_761975).sum := by decide
  have hdescent : baseEnd_761975 < baseStart_761975 := by decide
  rcases family_descends (prefixWord ++ tailWord_761975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761989 : List Nat := [1, 3, 1, 1, 5, 1, 4, 2, 1, 2, 2]
def baseStart_761989 : Nat := 118140960795 + 761989 * 2 ^ 59
def prefixEnd_761989 : Nat := 4983230072969 + 3 ^ 40 * 761989 * 2
def baseEnd_761989 : Nat := 391266610438924448233183

theorem tailTrace_761989 : CollatzResearch.WordTrace tailWord_761989 prefixEnd_761989 391266610438924448233183 := by
  unfold tailWord_761989
  simp only [CollatzResearch.WordTrace]
  refine ⟨27792022036451465205545021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18528014690967643470363347 27792022036451465205545021)
  ·
    refine ⟨10422008263669299452079383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27792022036451465205545021 10422008263669299452079383)
    ·
      refine ⟨15633012395503949178119075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10422008263669299452079383 15633012395503949178119075)
      ·
        refine ⟨23449518593255923767178613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15633012395503949178119075 23449518593255923767178613)
        ·
          refine ⟨2198392368117742853172995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23449518593255923767178613 2198392368117742853172995)
          ·
            refine ⟨3297588552176614279759493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198392368117742853172995 3297588552176614279759493)
            ·
              refine ⟨618297853533115177454905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3297588552176614279759493 618297853533115177454905)
              ·
                refine ⟨463723390149836383091179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618297853533115177454905 463723390149836383091179)
                ·
                  refine ⟨695585085224754574636769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463723390149836383091179 695585085224754574636769)
                  ·
                    refine ⟨521688813918565930977577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 695585085224754574636769 521688813918565930977577)
                    ·
                      refine ⟨391266610438924448233183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521688813918565930977577 391266610438924448233183)
                      ·
                        rfl

theorem cell23_761989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 2, 2].length) (baseStart_761989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_761989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_761989 prefixEnd_761989 := by exact prefixLift 761989
  have htrace : WordTrace (prefixWord ++ tailWord_761989) baseStart_761989 baseEnd_761989 := by
    simpa [prefixWord, tailWord_761989, baseEnd_761989] using wordTrace_append hprefix tailTrace_761989
  have hstable : (prefixWord ++ tailWord_761989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761989).length < 2 ^ (prefixWord ++ tailWord_761989).sum := by decide
  have hdescent : baseEnd_761989 < baseStart_761989 := by decide
  rcases family_descends (prefixWord ++ tailWord_761989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762015 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 3, 3, 2]
def baseStart_762015 : Nat := 118140960795 + 762015 * 2 ^ 59
def prefixEnd_762015 : Nat := 4983230072969 + 3 ^ 40 * 762015 * 2
def baseEnd_762015 : Nat := 391279960935941346508063

theorem tailTrace_762015 : CollatzResearch.WordTrace tailWord_762015 prefixEnd_762015 391279960935941346508063 := by
  unfold tailWord_762015
  simp only [CollatzResearch.WordTrace]
  refine ⟨27792970334357271645991499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18528646889571514430660999 27792970334357271645991499)
  ·
    refine ⟨41689455501535907468987249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27792970334357271645991499 41689455501535907468987249)
    ·
      refine ⟨31267091626151930601740437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41689455501535907468987249 31267091626151930601740437)
      ·
        refine ⟨1465644919975871746956583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31267091626151930601740437 1465644919975871746956583)
        ·
          refine ⟨2198467379963807620434875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465644919975871746956583 2198467379963807620434875)
          ·
            refine ⟨3297701069945711430652313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198467379963807620434875 3297701069945711430652313)
            ·
              refine ⟨2473275802459283572989235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3297701069945711430652313 2473275802459283572989235)
              ·
                refine ⟨3709913703688925359483853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473275802459283572989235 3709913703688925359483853)
                ·
                  refine ⟨1391217638883347009806445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3709913703688925359483853 1391217638883347009806445)
                  ·
                    refine ⟨521706614581255128677417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391217638883347009806445 521706614581255128677417)
                    ·
                      refine ⟨391279960935941346508063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521706614581255128677417 391279960935941346508063)
                      ·
                        rfl

theorem cell23_762015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_762015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762015 prefixEnd_762015 := by exact prefixLift 762015
  have htrace : WordTrace (prefixWord ++ tailWord_762015) baseStart_762015 baseEnd_762015 := by
    simpa [prefixWord, tailWord_762015, baseEnd_762015] using wordTrace_append hprefix tailTrace_762015
  have hstable : (prefixWord ++ tailWord_762015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762015).length < 2 ^ (prefixWord ++ tailWord_762015).sum := by decide
  have hdescent : baseEnd_762015 < baseStart_762015 := by decide
  rcases family_descends (prefixWord ++ tailWord_762015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762026 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_762026 : Nat := 118140960795 + 762026 * 2 ^ 59
def prefixEnd_762026 : Nat := 4983230072969 + 3 ^ 40 * 762026 * 2
def baseEnd_762026 : Nat := 391285609223140803470513

theorem tailTrace_762026 : CollatzResearch.WordTrace tailWord_762026 prefixEnd_762026 391285609223140803470513 := by
  unfold tailWord_762026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948342884329355131160483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18528914358211613683094621 6948342884329355131160483)
  ·
    refine ⟨10422514326494032696740725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6948342884329355131160483 10422514326494032696740725)
    ·
      refine ⟨977110718108815565319443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10422514326494032696740725 977110718108815565319443)
      ·
        refine ⟨1465666077163223347979165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977110718108815565319443 1465666077163223347979165)
        ·
          refine ⟨549624778936208755492187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1465666077163223347979165 549624778936208755492187)
          ·
            refine ⟨824437168404313133238281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549624778936208755492187 824437168404313133238281)
            ·
              refine ⟨618327876303234849928711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824437168404313133238281 618327876303234849928711)
              ·
                refine ⟨927491814454852274893067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618327876303234849928711 927491814454852274893067)
                ·
                  refine ⟨1391237721682278412339601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927491814454852274893067 1391237721682278412339601)
                  ·
                    refine ⟨1043428291261708809254701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1391237721682278412339601 1043428291261708809254701)
                    ·
                      refine ⟨391285609223140803470513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1043428291261708809254701 391285609223140803470513)
                      ·
                        rfl

theorem cell23_762026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_762026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762026 prefixEnd_762026 := by exact prefixLift 762026
  have htrace : WordTrace (prefixWord ++ tailWord_762026) baseStart_762026 baseEnd_762026 := by
    simpa [prefixWord, tailWord_762026, baseEnd_762026] using wordTrace_append hprefix tailTrace_762026
  have hstable : (prefixWord ++ tailWord_762026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762026).length < 2 ^ (prefixWord ++ tailWord_762026).sum := by decide
  have hdescent : baseEnd_762026 < baseStart_762026 := by decide
  rcases family_descends (prefixWord ++ tailWord_762026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762041 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_762041 : Nat := 118140960795 + 762041 * 2 ^ 59
def prefixEnd_762041 : Nat := 4983230072969 + 3 ^ 40 * 762041 * 2
def baseEnd_762041 : Nat := 391293311432958244782943

theorem tailTrace_762041 : CollatzResearch.WordTrace tailWord_762041 prefixEnd_762041 391293311432958244782943 := by
  unfold tailWord_762041
  simp only [CollatzResearch.WordTrace]
  refine ⟨27793918632263078086437977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18529279088175385390958651 27793918632263078086437977)
  ·
    refine ⟨20845438974197308564828483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27793918632263078086437977 20845438974197308564828483)
    ·
      refine ⟨31268158461295962847242725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20845438974197308564828483 31268158461295962847242725)
      ·
        refine ⟨5862779711492993033858011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31268158461295962847242725 5862779711492993033858011)
        ·
          refine ⟨8794169567239489550787017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5862779711492993033858011 8794169567239489550787017)
          ·
            refine ⟨6595627175429617163090263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8794169567239489550787017 6595627175429617163090263)
            ·
              refine ⟨9893440763144425744635395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6595627175429617163090263 9893440763144425744635395)
              ·
                refine ⟨14840161144716638616953093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9893440763144425744635395 14840161144716638616953093)
                ·
                  refine ⟨2782530214634369740678705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14840161144716638616953093 2782530214634369740678705)
                  ·
                    refine ⟨2086897660975777305509029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2782530214634369740678705 2086897660975777305509029)
                    ·
                      refine ⟨391293311432958244782943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2086897660975777305509029 391293311432958244782943)
                      ·
                        rfl

theorem cell23_762041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_762041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762041 prefixEnd_762041 := by exact prefixLift 762041
  have htrace : WordTrace (prefixWord ++ tailWord_762041) baseStart_762041 baseEnd_762041 := by
    simpa [prefixWord, tailWord_762041, baseEnd_762041] using wordTrace_append hprefix tailTrace_762041
  have hstable : (prefixWord ++ tailWord_762041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762041).length < 2 ^ (prefixWord ++ tailWord_762041).sum := by decide
  have hdescent : baseEnd_762041 < baseStart_762041 := by decide
  rcases family_descends (prefixWord ++ tailWord_762041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762062 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_762062 : Nat := 118140960795 + 762062 * 2 ^ 59
def prefixEnd_762062 : Nat := 4983230072969 + 3 ^ 40 * 762062 * 2
def baseEnd_762062 : Nat := 391304094526702662620347

theorem tailTrace_762062 : CollatzResearch.WordTrace tailWord_762062 prefixEnd_762062 391304094526702662620347 := by
  unfold tailWord_762062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3474335570648374834119055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18529789710124665781968293 3474335570648374834119055)
  ·
    refine ⟨5211503355972562251178583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3474335570648374834119055 5211503355972562251178583)
    ·
      refine ⟨7817255033958843376767875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211503355972562251178583 7817255033958843376767875)
      ·
        refine ⟨11725882550938265065151813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817255033958843376767875 11725882550938265065151813)
        ·
          refine ⟨2198602978300924699715965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11725882550938265065151813 2198602978300924699715965)
          ·
            refine ⟨824476116862846762393487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2198602978300924699715965 824476116862846762393487)
            ·
              refine ⟨1236714175294270143590231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824476116862846762393487 1236714175294270143590231)
              ·
                refine ⟨1855071262941405215385347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236714175294270143590231 1855071262941405215385347)
                ·
                  refine ⟨2782606894412107823078021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855071262941405215385347 2782606894412107823078021)
                  ·
                    refine ⟨521738792702270216827129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2782606894412107823078021 521738792702270216827129)
                    ·
                      refine ⟨391304094526702662620347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521738792702270216827129 391304094526702662620347)
                      ·
                        rfl

theorem cell23_762062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_762062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762062 prefixEnd_762062 := by exact prefixLift 762062
  have htrace : WordTrace (prefixWord ++ tailWord_762062) baseStart_762062 baseEnd_762062 := by
    simpa [prefixWord, tailWord_762062, baseEnd_762062] using wordTrace_append hprefix tailTrace_762062
  have hstable : (prefixWord ++ tailWord_762062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762062).length < 2 ^ (prefixWord ++ tailWord_762062).sum := by decide
  have hdescent : baseEnd_762062 < baseStart_762062 := by decide
  rcases family_descends (prefixWord ++ tailWord_762062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762081 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 1, 7]
def baseStart_762081 : Nat := 118140960795 + 762081 * 2 ^ 59
def prefixEnd_762081 : Nat := 4983230072969 + 3 ^ 40 * 762081 * 2
def baseEnd_762081 : Nat := 130437950219712696094253

theorem tailTrace_762081 : CollatzResearch.WordTrace tailWord_762081 prefixEnd_762081 130437950219712696094253 := by
  unfold tailWord_762081
  simp only [CollatzResearch.WordTrace]
  refine ⟨27795377552118164917894097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18530251701412109945262731 27795377552118164917894097)
  ·
    refine ⟨20846533164088623688420573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27795377552118164917894097 20846533164088623688420573)
    ·
      refine ⟨7817449936533233883157715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20846533164088623688420573 7817449936533233883157715)
      ·
        refine ⟨11726174904799850824736573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817449936533233883157715 11726174904799850824736573)
        ·
          refine ⟨4397315589299944059276215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11726174904799850824736573 4397315589299944059276215)
          ·
            refine ⟨6595973383949916088914323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4397315589299944059276215 6595973383949916088914323)
            ·
              refine ⟨9893960075924874133371485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6595973383949916088914323 9893960075924874133371485)
              ·
                refine ⟨3710235028471827800014307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9893960075924874133371485 3710235028471827800014307)
                ·
                  refine ⟨5565352542707741700021461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710235028471827800014307 5565352542707741700021461)
                  ·
                    refine ⟨130437950219712696094253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5565352542707741700021461 130437950219712696094253)
                    ·
                      rfl

theorem cell23_762081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_762081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762081 prefixEnd_762081 := by exact prefixLift 762081
  have htrace : WordTrace (prefixWord ++ tailWord_762081) baseStart_762081 baseEnd_762081 := by
    simpa [prefixWord, tailWord_762081, baseEnd_762081] using wordTrace_append hprefix tailTrace_762081
  have hstable : (prefixWord ++ tailWord_762081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762081).length < 2 ^ (prefixWord ++ tailWord_762081).sum := by decide
  have hdescent : baseEnd_762081 < baseStart_762081 := by decide
  rcases family_descends (prefixWord ++ tailWord_762081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762085 : List Nat := [1, 3, 1, 4, 2, 1, 3, 3, 5]
def baseStart_762085 : Nat := 118140960795 + 762085 * 2 ^ 59
def prefixEnd_762085 : Nat := 4983230072969 + 3 ^ 40 * 762085 * 2
def baseEnd_762085 : Nat := 43479544953528452514749

theorem tailTrace_762085 : CollatzResearch.WordTrace tailWord_762085 prefixEnd_762085 43479544953528452514749 := by
  unfold tailWord_762085
  simp only [CollatzResearch.WordTrace]
  refine ⟨27795523444103673601039709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18530348962735782400693139 27795523444103673601039709)
  ·
    refine ⟨10423321291538877600389891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27795523444103673601039709 10423321291538877600389891)
    ·
      refine ⟨15634981937308316400584837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10423321291538877600389891 15634981937308316400584837)
      ·
        refine ⟨2931559113245309325109657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15634981937308316400584837 2931559113245309325109657)
        ·
          refine ⟨2198669334933981993832243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2931559113245309325109657 2198669334933981993832243)
          ·
            refine ⟨3298004002400972990748365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198669334933981993832243 3298004002400972990748365)
            ·
              refine ⟨1236751500900364871530637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3298004002400972990748365 1236751500900364871530637)
              ·
                refine ⟨463781812837636826823989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1236751500900364871530637 463781812837636826823989)
                ·
                  refine ⟨43479544953528452514749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 463781812837636826823989 43479544953528452514749)
                  ·
                    rfl

theorem cell23_762085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_762085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762085 prefixEnd_762085 := by exact prefixLift 762085
  have htrace : WordTrace (prefixWord ++ tailWord_762085) baseStart_762085 baseEnd_762085 := by
    simpa [prefixWord, tailWord_762085, baseEnd_762085] using wordTrace_append hprefix tailTrace_762085
  have hstable : (prefixWord ++ tailWord_762085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762085).length < 2 ^ (prefixWord ++ tailWord_762085).sum := by decide
  have hdescent : baseEnd_762085 < baseStart_762085 := by decide
  rcases family_descends (prefixWord ++ tailWord_762085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762091 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 5]
def baseStart_762091 : Nat := 118140960795 + 762091 * 2 ^ 59
def prefixEnd_762091 : Nat := 4983230072969 + 3 ^ 40 * 762091 * 2
def baseEnd_762091 : Nat := 391318985465683049157713

theorem tailTrace_762091 : CollatzResearch.WordTrace tailWord_762091 prefixEnd_762091 391318985465683049157713 := by
  unfold tailWord_762091
  simp only [CollatzResearch.WordTrace]
  refine ⟨27795742282081936625758127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18530494854721291083838751 27795742282081936625758127)
  ·
    refine ⟨41693613423122904938637191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27795742282081936625758127 41693613423122904938637191)
    ·
      refine ⟨62540420134684357407955787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41693613423122904938637191 62540420134684357407955787)
      ·
        refine ⟨93810630202026536111933681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62540420134684357407955787 93810630202026536111933681)
        ·
          refine ⟨70357972651519902083950261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93810630202026536111933681 70357972651519902083950261)
          ·
            refine ⟨6596059936079990820370337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70357972651519902083950261 6596059936079990820370337)
            ·
              refine ⟨4947044952059993115277753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6596059936079990820370337 4947044952059993115277753)
              ·
                refine ⟨3710283714044994836458315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4947044952059993115277753 3710283714044994836458315)
                ·
                  refine ⟨5565425571067492254687473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710283714044994836458315 5565425571067492254687473)
                  ·
                    refine ⟨4174069178300619191015605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5565425571067492254687473 4174069178300619191015605)
                    ·
                      refine ⟨391318985465683049157713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4174069178300619191015605 391318985465683049157713)
                      ·
                        rfl

theorem cell23_762091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_762091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762091 prefixEnd_762091 := by exact prefixLift 762091
  have htrace : WordTrace (prefixWord ++ tailWord_762091) baseStart_762091 baseEnd_762091 := by
    simpa [prefixWord, tailWord_762091, baseEnd_762091] using wordTrace_append hprefix tailTrace_762091
  have hstable : (prefixWord ++ tailWord_762091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762091).length < 2 ^ (prefixWord ++ tailWord_762091).sum := by decide
  have hdescent : baseEnd_762091 < baseStart_762091 := by decide
  rcases family_descends (prefixWord ++ tailWord_762091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762098 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_762098 : Nat := 118140960795 + 762098 * 2 ^ 59
def prefixEnd_762098 : Nat := 4983230072969 + 3 ^ 40 * 762098 * 2
def baseEnd_762098 : Nat := 130440859943421507256727

theorem tailTrace_762098 : CollatzResearch.WordTrace tailWord_762098 prefixEnd_762098 130440859943421507256727 := by
  unfold tailWord_762098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948999398264144205315737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18530665062037717880841965 6948999398264144205315737)
  ·
    refine ⟨5211749548698108153986803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6948999398264144205315737 5211749548698108153986803)
    ·
      refine ⟨7817624323047162230980205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211749548698108153986803 7817624323047162230980205)
      ·
        refine ⟨2931609121142685836617577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7817624323047162230980205 2931609121142685836617577)
        ·
          refine ⟨2198706840857014377463183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2931609121142685836617577 2198706840857014377463183)
          ·
            refine ⟨3298060261285521566194775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198706840857014377463183 3298060261285521566194775)
            ·
              refine ⟨4947090391928282349292163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298060261285521566194775 4947090391928282349292163)
              ·
                refine ⟨7420635587892423523938245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4947090391928282349292163 7420635587892423523938245)
                ·
                  refine ⟨1391369172729829410738421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7420635587892423523938245 1391369172729829410738421)
                  ·
                    refine ⟨130440859943421507256727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1391369172729829410738421 130440859943421507256727)
                    ·
                      rfl

theorem cell23_762098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_762098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762098 prefixEnd_762098 := by exact prefixLift 762098
  have htrace : WordTrace (prefixWord ++ tailWord_762098) baseStart_762098 baseEnd_762098 := by
    simpa [prefixWord, tailWord_762098, baseEnd_762098] using wordTrace_append hprefix tailTrace_762098
  have hstable : (prefixWord ++ tailWord_762098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762098).length < 2 ^ (prefixWord ++ tailWord_762098).sum := by decide
  have hdescent : baseEnd_762098 < baseStart_762098 := by decide
  rcases family_descends (prefixWord ++ tailWord_762098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762108 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_762108 : Nat := 118140960795 + 762108 * 2 ^ 59
def prefixEnd_762108 : Nat := 4983230072969 + 3 ^ 40 * 762108 * 2
def baseEnd_762108 : Nat := 391327714636809482645135

theorem tailTrace_762108 : CollatzResearch.WordTrace tailWord_762108 prefixEnd_762108 391327714636809482645135 := by
  unfold tailWord_762108
  simp only [CollatzResearch.WordTrace]
  refine ⟨13898181161510174264563489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18530908215346899019417985 13898181161510174264563489)
  ·
    refine ⟨10423635871132630698422617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13898181161510174264563489 10423635871132630698422617)
    ·
      refine ⟨7817726903349473023816963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10423635871132630698422617 7817726903349473023816963)
      ·
        refine ⟨11726590355024209535725445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817726903349473023816963 11726590355024209535725445)
        ·
          refine ⟨2198735691567039287948521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11726590355024209535725445 2198735691567039287948521)
          ·
            refine ⟨1649051768675279465961391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2198735691567039287948521 1649051768675279465961391)
            ·
              refine ⟨2473577653012919198942087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649051768675279465961391 2473577653012919198942087)
              ·
                refine ⟨3710366479519378798413131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473577653012919198942087 3710366479519378798413131)
                ·
                  refine ⟨5565549719279068197619697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710366479519378798413131 5565549719279068197619697)
                  ·
                    refine ⟨4174162289459301148214773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5565549719279068197619697 4174162289459301148214773)
                    ·
                      refine ⟨391327714636809482645135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4174162289459301148214773 391327714636809482645135)
                      ·
                        rfl

theorem cell23_762108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_762108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762108 prefixEnd_762108 := by exact prefixLift 762108
  have htrace : WordTrace (prefixWord ++ tailWord_762108) baseStart_762108 baseEnd_762108 := by
    simpa [prefixWord, tailWord_762108, baseEnd_762108] using wordTrace_append hprefix tailTrace_762108
  have hstable : (prefixWord ++ tailWord_762108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762108).length < 2 ^ (prefixWord ++ tailWord_762108).sum := by decide
  have hdescent : baseEnd_762108 < baseStart_762108 := by decide
  rcases family_descends (prefixWord ++ tailWord_762108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762131 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 4]
def baseStart_762131 : Nat := 118140960795 + 762131 * 2 ^ 59
def prefixEnd_762131 : Nat := 4983230072969 + 3 ^ 40 * 762131 * 2
def baseEnd_762131 : Nat := 391339524691862892657529

theorem tailTrace_762131 : CollatzResearch.WordTrace tailWord_762131 prefixEnd_762131 391339524691862892657529 := by
  unfold tailWord_762131
  simp only [CollatzResearch.WordTrace]
  refine ⟨27797201201937023457214247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18531467467958015638142831 27797201201937023457214247)
  ·
    refine ⟨41695801802905535185821371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27797201201937023457214247 41695801802905535185821371)
    ·
      refine ⟨62543702704358302778732057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41695801802905535185821371 62543702704358302778732057)
      ·
        refine ⟨46907777028268727084049043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62543702704358302778732057 46907777028268727084049043)
        ·
          refine ⟨70361665542403090626073565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46907777028268727084049043 70361665542403090626073565)
          ·
            refine ⟨26385624578401158984777587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70361665542403090626073565 26385624578401158984777587)
            ·
              refine ⟨39578436867601738477166381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26385624578401158984777587 39578436867601738477166381)
              ·
                refine ⟨14841913825350651928937393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39578436867601738477166381 14841913825350651928937393)
                ·
                  refine ⟨11131435369012988946703045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14841913825350651928937393 11131435369012988946703045)
                  ·
                    refine ⟨2087144131689935427506821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11131435369012988946703045 2087144131689935427506821)
                    ·
                      refine ⟨391339524691862892657529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2087144131689935427506821 391339524691862892657529)
                      ·
                        rfl

theorem cell23_762131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_762131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762131 prefixEnd_762131 := by exact prefixLift 762131
  have htrace : WordTrace (prefixWord ++ tailWord_762131) baseStart_762131 baseEnd_762131 := by
    simpa [prefixWord, tailWord_762131, baseEnd_762131] using wordTrace_append hprefix tailTrace_762131
  have hstable : (prefixWord ++ tailWord_762131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762131).length < 2 ^ (prefixWord ++ tailWord_762131).sum := by decide
  have hdescent : baseEnd_762131 < baseStart_762131 := by decide
  rcases family_descends (prefixWord ++ tailWord_762131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762135 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_762135 : Nat := 118140960795 + 762135 * 2 ^ 59
def prefixEnd_762135 : Nat := 4983230072969 + 3 ^ 40 * 762135 * 2
def baseEnd_762135 : Nat := 391341578614480877007511

theorem tailTrace_762135 : CollatzResearch.WordTrace tailWord_762135 prefixEnd_762135 391341578614480877007511 := by
  unfold tailWord_762135
  simp only [CollatzResearch.WordTrace]
  refine ⟨27797347093922532140359859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18531564729281688093573239 27797347093922532140359859)
  ·
    refine ⟨41696020640883798210539789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27797347093922532140359859 41696020640883798210539789)
    ·
      refine ⟨15636007740331424328952421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41696020640883798210539789 15636007740331424328952421)
      ·
        refine ⟨2931751451312142061678579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15636007740331424328952421 2931751451312142061678579)
        ·
          refine ⟨4397627176968213092517869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2931751451312142061678579 4397627176968213092517869)
          ·
            refine ⟨1649110191363079909694201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4397627176968213092517869 1649110191363079909694201)
            ·
              refine ⟨1236832643522309932270651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1649110191363079909694201 1236832643522309932270651)
              ·
                refine ⟨1855248965283464898405977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236832643522309932270651 1855248965283464898405977)
                ·
                  refine ⟨1391436723962598673804483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1855248965283464898405977 1391436723962598673804483)
                  ·
                    refine ⟨2087155085943898010706725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1391436723962598673804483 2087155085943898010706725)
                    ·
                      refine ⟨391341578614480877007511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2087155085943898010706725 391341578614480877007511)
                      ·
                        rfl

theorem cell23_762135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_762135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762135 prefixEnd_762135 := by exact prefixLift 762135
  have htrace : WordTrace (prefixWord ++ tailWord_762135) baseStart_762135 baseEnd_762135 := by
    simpa [prefixWord, tailWord_762135, baseEnd_762135] using wordTrace_append hprefix tailTrace_762135
  have hstable : (prefixWord ++ tailWord_762135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762135).length < 2 ^ (prefixWord ++ tailWord_762135).sum := by decide
  have hdescent : baseEnd_762135 < baseStart_762135 := by decide
  rcases family_descends (prefixWord ++ tailWord_762135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762188 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_762188 : Nat := 118140960795 + 762188 * 2 ^ 59
def prefixEnd_762188 : Nat := 4983230072969 + 3 ^ 40 * 762188 * 2
def baseEnd_762188 : Nat := 130456264363056389881589

theorem tailTrace_762188 : CollatzResearch.WordTrace tailWord_762188 prefixEnd_762188 130456264363056389881589 := by
  unfold tailWord_762188
  simp only [CollatzResearch.WordTrace]
  refine ⟨13899640081365261096019609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18532853441820348128026145 13899640081365261096019609)
  ·
    refine ⟨10424730061023945822014707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13899640081365261096019609 10424730061023945822014707)
    ·
      refine ⟨15637095091535918733022061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10424730061023945822014707 15637095091535918733022061)
      ·
        refine ⟨5863910659325969524883273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15637095091535918733022061 5863910659325969524883273)
        ·
          refine ⟨4397932994494477143662455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5863910659325969524883273 4397932994494477143662455)
          ·
            refine ⟨6596899491741715715493683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4397932994494477143662455 6596899491741715715493683)
            ·
              refine ⟨9895349237612573573240525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596899491741715715493683 9895349237612573573240525)
              ·
                refine ⟨3710755964104715089965197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9895349237612573573240525 3710755964104715089965197)
                ·
                  refine ⟨1391533486539268158736949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3710755964104715089965197 1391533486539268158736949)
                  ·
                    refine ⟨130456264363056389881589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1391533486539268158736949 130456264363056389881589)
                    ·
                      rfl

theorem cell23_762188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_762188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762188 prefixEnd_762188 := by exact prefixLift 762188
  have htrace : WordTrace (prefixWord ++ tailWord_762188) baseStart_762188 baseEnd_762188 := by
    simpa [prefixWord, tailWord_762188, baseEnd_762188] using wordTrace_append hprefix tailTrace_762188
  have hstable : (prefixWord ++ tailWord_762188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762188).length < 2 ^ (prefixWord ++ tailWord_762188).sum := by decide
  have hdescent : baseEnd_762188 < baseStart_762188 := by decide
  rcases family_descends (prefixWord ++ tailWord_762188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762195 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 2, 3, 2]
def baseStart_762195 : Nat := 118140960795 + 762195 * 2 ^ 59
def prefixEnd_762195 : Nat := 4983230072969 + 3 ^ 40 * 762195 * 2
def baseEnd_762195 : Nat := 391372387453750642257235

theorem tailTrace_762195 : CollatzResearch.WordTrace tailWord_762195 prefixEnd_762195 391372387453750642257235 := by
  unfold tailWord_762195
  simp only [CollatzResearch.WordTrace]
  refine ⟨27799535473705162387544039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18533023649136774925029359 27799535473705162387544039)
  ·
    refine ⟨41699303210557743581316059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27799535473705162387544039 41699303210557743581316059)
    ·
      refine ⟨62548954815836615371974089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41699303210557743581316059 62548954815836615371974089)
      ·
        refine ⟨46911716111877461528980567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62548954815836615371974089 46911716111877461528980567)
        ·
          refine ⟨70367574167816192293470851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46911716111877461528980567 70367574167816192293470851)
          ·
            refine ⟨105551361251724288440206277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70367574167816192293470851 105551361251724288440206277)
            ·
              refine ⟨19790880234698304082538677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105551361251724288440206277 19790880234698304082538677)
              ·
                refine ⟨1855395022002966007738001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19790880234698304082538677 1855395022002966007738001)
                ·
                  refine ⟨1391546266502224505803501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1855395022002966007738001 1391546266502224505803501)
                  ·
                    refine ⟨521829849938334189676313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391546266502224505803501 521829849938334189676313)
                    ·
                      refine ⟨391372387453750642257235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521829849938334189676313 391372387453750642257235)
                      ·
                        rfl

theorem cell23_762195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 3, 2].length) (baseStart_762195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762195 prefixEnd_762195 := by exact prefixLift 762195
  have htrace : WordTrace (prefixWord ++ tailWord_762195) baseStart_762195 baseEnd_762195 := by
    simpa [prefixWord, tailWord_762195, baseEnd_762195] using wordTrace_append hprefix tailTrace_762195
  have hstable : (prefixWord ++ tailWord_762195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762195).length < 2 ^ (prefixWord ++ tailWord_762195).sum := by decide
  have hdescent : baseEnd_762195 < baseStart_762195 := by decide
  rcases family_descends (prefixWord ++ tailWord_762195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762235 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 1, 6]
def baseStart_762235 : Nat := 118140960795 + 762235 * 2 ^ 59
def prefixEnd_762235 : Nat := 4983230072969 + 3 ^ 40 * 762235 * 2
def baseEnd_762235 : Nat := 130464308893310161919017

theorem tailTrace_762235 : CollatzResearch.WordTrace tailWord_762235 prefixEnd_762235 130464308893310161919017 := by
  unfold tailWord_762235
  simp only [CollatzResearch.WordTrace]
  refine ⟨27800994393560249219000159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18533996262373499479333439 27800994393560249219000159)
  ·
    refine ⟨41701491590340373828500239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27800994393560249219000159 41701491590340373828500239)
    ·
      refine ⟨62552237385510560742750359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41701491590340373828500239 62552237385510560742750359)
      ·
        refine ⟨93828356078265841114125539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62552237385510560742750359 93828356078265841114125539)
        ·
          refine ⟨140742534117398761671188309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93828356078265841114125539 140742534117398761671188309)
          ·
            refine ⟨824663285844133369167119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 140742534117398761671188309 824663285844133369167119)
            ·
              refine ⟨1236994928766200053750679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824663285844133369167119 1236994928766200053750679)
              ·
                refine ⟨1855492393149300080626019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236994928766200053750679 1855492393149300080626019)
                ·
                  refine ⟨2783238589723950120939029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855492393149300080626019 2783238589723950120939029)
                  ·
                    refine ⟨130464308893310161919017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2783238589723950120939029 130464308893310161919017)
                    ·
                      rfl

theorem cell23_762235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 6].length) (baseStart_762235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762235 prefixEnd_762235 := by exact prefixLift 762235
  have htrace : WordTrace (prefixWord ++ tailWord_762235) baseStart_762235 baseEnd_762235 := by
    simpa [prefixWord, tailWord_762235, baseEnd_762235] using wordTrace_append hprefix tailTrace_762235
  have hstable : (prefixWord ++ tailWord_762235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762235).length < 2 ^ (prefixWord ++ tailWord_762235).sum := by decide
  have hdescent : baseEnd_762235 < baseStart_762235 := by decide
  rcases family_descends (prefixWord ++ tailWord_762235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762248 : List Nat := [2, 1, 3, 3, 1, 1, 3, 9]
def baseStart_762248 : Nat := 118140960795 + 762248 * 2 ^ 59
def prefixEnd_762248 : Nat := 4983230072969 + 3 ^ 40 * 762248 * 2
def baseEnd_762248 : Nat := 14496281552905145736833

theorem tailTrace_762248 : CollatzResearch.WordTrace tailWord_762248 prefixEnd_762248 14496281552905145736833 := by
  unfold tailWord_762248
  simp only [CollatzResearch.WordTrace]
  refine ⟨13900734271256576219611699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18534312361675434959482265 13900734271256576219611699)
  ·
    refine ⟨20851101406884864329417549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13900734271256576219611699 20851101406884864329417549)
    ·
      refine ⟨7819163027581824123531581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20851101406884864329417549 7819163027581824123531581)
      ·
        refine ⟨2932186135343184046324343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7819163027581824123531581 2932186135343184046324343)
        ·
          refine ⟨4398279203014776069486515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932186135343184046324343 4398279203014776069486515)
          ·
            refine ⟨6597418804522164104229773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398279203014776069486515 6597418804522164104229773)
            ·
              refine ⟨2474032051695811539086165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6597418804522164104229773 2474032051695811539086165)
              ·
                refine ⟨14496281552905145736833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2474032051695811539086165 14496281552905145736833)
                ·
                  rfl

theorem cell23_762248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 9].length) (baseStart_762248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762248 prefixEnd_762248 := by exact prefixLift 762248
  have htrace : WordTrace (prefixWord ++ tailWord_762248) baseStart_762248 baseEnd_762248 := by
    simpa [prefixWord, tailWord_762248, baseEnd_762248] using wordTrace_append hprefix tailTrace_762248
  have hstable : (prefixWord ++ tailWord_762248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762248).length < 2 ^ (prefixWord ++ tailWord_762248).sum := by decide
  have hdescent : baseEnd_762248 < baseStart_762248 := by decide
  rcases family_descends (prefixWord ++ tailWord_762248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762326 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_762326 : Nat := 118140960795 + 762326 * 2 ^ 59
def prefixEnd_762326 : Nat := 4983230072969 + 3 ^ 40 * 762326 * 2
def baseEnd_762326 : Nat := 391439653419489629719133

theorem tailTrace_762326 : CollatzResearch.WordTrace tailWord_762326 prefixEnd_762326 391439653419489629719133 := by
  unfold tailWord_762326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737769589764410735035177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18536208957487047840375221 1737769589764410735035177)
  ·
    refine ⟨1303327192323308051276383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1737769589764410735035177 1303327192323308051276383)
    ·
      refine ⟨1954990788484962076914575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303327192323308051276383 1954990788484962076914575)
      ·
        refine ⟨2932486182727443115371863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954990788484962076914575 2932486182727443115371863)
        ·
          refine ⟨4398729274091164673057795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932486182727443115371863 4398729274091164673057795)
          ·
            refine ⟨6598093911136747009586693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398729274091164673057795 6598093911136747009586693)
            ·
              refine ⟨1237142608338140064297505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6598093911136747009586693 1237142608338140064297505)
              ·
                refine ⟨927856956253605048223129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237142608338140064297505 927856956253605048223129)
                ·
                  refine ⟨695892717190203786167347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 927856956253605048223129 695892717190203786167347)
                  ·
                    refine ⟨1043839075785305679251021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 695892717190203786167347 1043839075785305679251021)
                    ·
                      refine ⟨391439653419489629719133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1043839075785305679251021 391439653419489629719133)
                      ·
                        rfl

theorem cell23_762326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_762326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762326 prefixEnd_762326 := by exact prefixLift 762326
  have htrace : WordTrace (prefixWord ++ tailWord_762326) baseStart_762326 baseEnd_762326 := by
    simpa [prefixWord, tailWord_762326, baseEnd_762326] using wordTrace_append hprefix tailTrace_762326
  have hstable : (prefixWord ++ tailWord_762326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762326).length < 2 ^ (prefixWord ++ tailWord_762326).sum := by decide
  have hdescent : baseEnd_762326 < baseStart_762326 := by decide
  rcases family_descends (prefixWord ++ tailWord_762326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762328 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_762328 : Nat := 118140960795 + 762328 * 2 ^ 59
def prefixEnd_762328 : Nat := 4983230072969 + 3 ^ 40 * 762328 * 2
def baseEnd_762328 : Nat := 391440680380798621894123

theorem tailTrace_762328 : CollatzResearch.WordTrace tailWord_762328 prefixEnd_762328 391440680380798621894123 := by
  unfold tailWord_762328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13902193191111663051067819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18536257588148884068090425 13902193191111663051067819)
  ·
    refine ⟨20853289786667494576601729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13902193191111663051067819 20853289786667494576601729)
    ·
      refine ⟨15639967340000620932451297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20853289786667494576601729 15639967340000620932451297)
      ·
        refine ⟨11729975505000465699338473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15639967340000620932451297 11729975505000465699338473)
        ·
          refine ⟨8797481628750349274503855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11729975505000465699338473 8797481628750349274503855)
          ·
            refine ⟨13196222443125523911755783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8797481628750349274503855 13196222443125523911755783)
            ·
              refine ⟨19794333664688285867633675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13196222443125523911755783 19794333664688285867633675)
              ·
                refine ⟨29691500497032428801450513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19794333664688285867633675 29691500497032428801450513)
                ·
                  refine ⟨22268625372774321601087885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29691500497032428801450513 22268625372774321601087885)
                  ·
                    refine ⟨8350734514790370600407957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22268625372774321601087885 8350734514790370600407957)
                    ·
                      refine ⟨391440680380798621894123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8350734514790370600407957 391440680380798621894123)
                      ·
                        rfl

theorem cell23_762328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_762328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762328 prefixEnd_762328 := by exact prefixLift 762328
  have htrace : WordTrace (prefixWord ++ tailWord_762328) baseStart_762328 baseEnd_762328 := by
    simpa [prefixWord, tailWord_762328, baseEnd_762328] using wordTrace_append hprefix tailTrace_762328
  have hstable : (prefixWord ++ tailWord_762328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762328).length < 2 ^ (prefixWord ++ tailWord_762328).sum := by decide
  have hdescent : baseEnd_762328 < baseStart_762328 := by decide
  rcases family_descends (prefixWord ++ tailWord_762328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762335 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 3]
def baseStart_762335 : Nat := 118140960795 + 762335 * 2 ^ 59
def prefixEnd_762335 : Nat := 4983230072969 + 3 ^ 40 * 762335 * 2
def baseEnd_762335 : Nat := 391444274745380094506591

theorem tailTrace_762335 : CollatzResearch.WordTrace tailWord_762335 prefixEnd_762335 391444274745380094506591 := by
  unfold tailWord_762335
  simp only [CollatzResearch.WordTrace]
  refine ⟨27804641693197966297640459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18536427795465310865093639 27804641693197966297640459)
  ·
    refine ⟨41706962539796949446460689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27804641693197966297640459 41706962539796949446460689)
    ·
      refine ⟨31280221904847712084845517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41706962539796949446460689 31280221904847712084845517)
      ·
        refine ⟨11730083214317892031817069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31280221904847712084845517 11730083214317892031817069)
        ·
          refine ⟨4398781205369209511931401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11730083214317892031817069 4398781205369209511931401)
          ·
            refine ⟨3299085904026907133948551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4398781205369209511931401 3299085904026907133948551)
            ·
              refine ⟨4948628856040360700922827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299085904026907133948551 4948628856040360700922827)
              ·
                refine ⟨7422943284060541051384241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948628856040360700922827 7422943284060541051384241)
                ·
                  refine ⟨5567207463045405788538181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7422943284060541051384241 5567207463045405788538181)
                  ·
                    refine ⟨1043851399321013585350909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567207463045405788538181 1043851399321013585350909)
                    ·
                      refine ⟨391444274745380094506591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1043851399321013585350909 391444274745380094506591)
                      ·
                        rfl

theorem cell23_762335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_762335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762335 prefixEnd_762335 := by exact prefixLift 762335
  have htrace : WordTrace (prefixWord ++ tailWord_762335) baseStart_762335 baseEnd_762335 := by
    simpa [prefixWord, tailWord_762335, baseEnd_762335] using wordTrace_append hprefix tailTrace_762335
  have hstable : (prefixWord ++ tailWord_762335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762335).length < 2 ^ (prefixWord ++ tailWord_762335).sum := by decide
  have hdescent : baseEnd_762335 < baseStart_762335 := by decide
  rcases family_descends (prefixWord ++ tailWord_762335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762349 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_762349 : Nat := 118140960795 + 762349 * 2 ^ 59
def prefixEnd_762349 : Nat := 4983230072969 + 3 ^ 40 * 762349 * 2
def baseEnd_762349 : Nat := 391451463474543039731527

theorem tailTrace_762349 : CollatzResearch.WordTrace tailWord_762349 prefixEnd_762349 391451463474543039731527 := by
  unfold tailWord_762349
  simp only [CollatzResearch.WordTrace]
  refine ⟨27805152315147246688650101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18536768210098164459100067 27805152315147246688650101)
  ·
    refine ⟨2606733029545054377060947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27805152315147246688650101 2606733029545054377060947)
    ·
      refine ⟨3910099544317581565591421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606733029545054377060947 3910099544317581565591421)
      ·
        refine ⟨1466287329119093087096783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3910099544317581565591421 1466287329119093087096783)
        ·
          refine ⟨2199430993678639630645175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1466287329119093087096783 2199430993678639630645175)
          ·
            refine ⟨3299146490517959445967763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199430993678639630645175 3299146490517959445967763)
            ·
              refine ⟨4948719735776939168951645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299146490517959445967763 4948719735776939168951645)
              ·
                refine ⟨1855769900916352188356867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4948719735776939168951645 1855769900916352188356867)
                ·
                  refine ⟨2783654851374528282535301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855769900916352188356867 2783654851374528282535301)
                  ·
                    refine ⟨521935284632724052975369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2783654851374528282535301 521935284632724052975369)
                    ·
                      refine ⟨391451463474543039731527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521935284632724052975369 391451463474543039731527)
                      ·
                        rfl

theorem cell23_762349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_762349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762349 prefixEnd_762349 := by exact prefixLift 762349
  have htrace : WordTrace (prefixWord ++ tailWord_762349) baseStart_762349 baseEnd_762349 := by
    simpa [prefixWord, tailWord_762349, baseEnd_762349] using wordTrace_append hprefix tailTrace_762349
  have hstable : (prefixWord ++ tailWord_762349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762349).length < 2 ^ (prefixWord ++ tailWord_762349).sum := by decide
  have hdescent : baseEnd_762349 < baseStart_762349 := by decide
  rcases family_descends (prefixWord ++ tailWord_762349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762365 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_762365 : Nat := 118140960795 + 762365 * 2 ^ 59
def prefixEnd_762365 : Nat := 4983230072969 + 3 ^ 40 * 762365 * 2
def baseEnd_762365 : Nat := 391459679165014977131453

theorem tailTrace_762365 : CollatzResearch.WordTrace tailWord_762365 prefixEnd_762365 391459679165014977131453 := by
  unfold tailWord_762365
  simp only [CollatzResearch.WordTrace]
  refine ⟨27805735883089281421232549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18537157255392854280821699 27805735883089281421232549)
  ·
    refine ⟨5213575478079240266481103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27805735883089281421232549 5213575478079240266481103)
    ·
      refine ⟨7820363217118860399721655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213575478079240266481103 7820363217118860399721655)
      ·
        refine ⟨11730544825678290599582483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7820363217118860399721655 11730544825678290599582483)
        ·
          refine ⟨17595817238517435899373725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11730544825678290599582483 17595817238517435899373725)
          ·
            refine ⟨6598431464444038462265147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17595817238517435899373725 6598431464444038462265147)
            ·
              refine ⟨9897647196666057693397721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6598431464444038462265147 9897647196666057693397721)
              ·
                refine ⟨7423235397499543270048291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9897647196666057693397721 7423235397499543270048291)
                ·
                  refine ⟨11134853096249314905072437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7423235397499543270048291 11134853096249314905072437)
                  ·
                    refine ⟨1043892477773373272350541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11134853096249314905072437 1043892477773373272350541)
                    ·
                      refine ⟨391459679165014977131453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1043892477773373272350541 391459679165014977131453)
                      ·
                        rfl

theorem cell23_762365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_762365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762365 prefixEnd_762365 := by exact prefixLift 762365
  have htrace : WordTrace (prefixWord ++ tailWord_762365) baseStart_762365 baseEnd_762365 := by
    simpa [prefixWord, tailWord_762365, baseEnd_762365] using wordTrace_append hprefix tailTrace_762365
  have hstable : (prefixWord ++ tailWord_762365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762365).length < 2 ^ (prefixWord ++ tailWord_762365).sum := by decide
  have hdescent : baseEnd_762365 < baseStart_762365 := by decide
  rcases family_descends (prefixWord ++ tailWord_762365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762370 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_762370 : Nat := 118140960795 + 762370 * 2 ^ 59
def prefixEnd_762370 : Nat := 4983230072969 + 3 ^ 40 * 762370 * 2
def baseEnd_762370 : Nat := 391462246568287457568931

theorem tailTrace_762370 : CollatzResearch.WordTrace tailWord_762370 prefixEnd_762370 391462246568287457568931 := by
  unfold tailWord_762370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6951479562017791818791141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18537278832047444850109709 6951479562017791818791141)
  ·
    refine ⟨1303402417878335966023339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6951479562017791818791141 1303402417878335966023339)
    ·
      refine ⟨1955103626817503949035009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303402417878335966023339 1955103626817503949035009)
      ·
        refine ⟨1466327720113127961776257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1955103626817503949035009 1466327720113127961776257)
        ·
          refine ⟨1099745790084845971332193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1466327720113127961776257 1099745790084845971332193)
          ·
            refine ⟨824809342563634478499145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1099745790084845971332193 824809342563634478499145)
            ·
              refine ⟨618607006922725858874359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824809342563634478499145 618607006922725858874359)
              ·
                refine ⟨927910510384088788311539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618607006922725858874359 927910510384088788311539)
                ·
                  refine ⟨1391865765576133182467309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927910510384088788311539 1391865765576133182467309)
                  ·
                    refine ⟨521949662091049943425241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391865765576133182467309 521949662091049943425241)
                    ·
                      refine ⟨391462246568287457568931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 521949662091049943425241 391462246568287457568931)
                      ·
                        rfl

theorem cell23_762370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_762370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762370 prefixEnd_762370 := by exact prefixLift 762370
  have htrace : WordTrace (prefixWord ++ tailWord_762370) baseStart_762370 baseEnd_762370 := by
    simpa [prefixWord, tailWord_762370, baseEnd_762370] using wordTrace_append hprefix tailTrace_762370
  have hstable : (prefixWord ++ tailWord_762370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762370).length < 2 ^ (prefixWord ++ tailWord_762370).sum := by decide
  have hdescent : baseEnd_762370 < baseStart_762370 := by decide
  rcases family_descends (prefixWord ++ tailWord_762370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762382 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_762382 : Nat := 118140960795 + 762382 * 2 ^ 59
def prefixEnd_762382 : Nat := 4983230072969 + 3 ^ 40 * 762382 * 2
def baseEnd_762382 : Nat := 391468408336141410618875

theorem tailTrace_762382 : CollatzResearch.WordTrace tailWord_762382 prefixEnd_762382 391468408336141410618875 := by
  unfold tailWord_762382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3475794490503461665575175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18537570616018462216400933 3475794490503461665575175)
  ·
    refine ⟨5213691735755192498362763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3475794490503461665575175 5213691735755192498362763)
    ·
      refine ⟨7820537603632788747544145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213691735755192498362763 7820537603632788747544145)
      ·
        refine ⟨5865403202724591560658109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7820537603632788747544145 5865403202724591560658109)
        ·
          refine ⟨2199526201021721835246791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5865403202724591560658109 2199526201021721835246791)
          ·
            refine ⟨3299289301532582752870187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199526201021721835246791 3299289301532582752870187)
            ·
              refine ⟨4948933952298874129305281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299289301532582752870187 4948933952298874129305281)
              ·
                refine ⟨3711700464224155596978961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4948933952298874129305281 3711700464224155596978961)
                ·
                  refine ⟨2783775348168116697734221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3711700464224155596978961 2783775348168116697734221)
                  ·
                    refine ⟨1043915755563043761650333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2783775348168116697734221 1043915755563043761650333)
                    ·
                      refine ⟨391468408336141410618875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1043915755563043761650333 391468408336141410618875)
                      ·
                        rfl

theorem cell23_762382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_762382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762382 prefixEnd_762382 := by exact prefixLift 762382
  have htrace : WordTrace (prefixWord ++ tailWord_762382) baseStart_762382 baseEnd_762382 := by
    simpa [prefixWord, tailWord_762382, baseEnd_762382] using wordTrace_append hprefix tailTrace_762382
  have hstable : (prefixWord ++ tailWord_762382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762382).length < 2 ^ (prefixWord ++ tailWord_762382).sum := by decide
  have hdescent : baseEnd_762382 < baseStart_762382 := by decide
  rcases family_descends (prefixWord ++ tailWord_762382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762405 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_762405 : Nat := 118140960795 + 762405 * 2 ^ 59
def prefixEnd_762405 : Nat := 4983230072969 + 3 ^ 40 * 762405 * 2
def baseEnd_762405 : Nat := 391480218391194820631269

theorem tailTrace_762405 : CollatzResearch.WordTrace tailWord_762405 prefixEnd_762405 391480218391194820631269 := by
  unfold tailWord_762405
  simp only [CollatzResearch.WordTrace]
  refine ⟨27807194802944368252688669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18538129868629578835125779 27807194802944368252688669)
  ·
    refine ⟨10427698051104138094758251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27807194802944368252688669 10427698051104138094758251)
    ·
      refine ⟨15641547076656207142137377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10427698051104138094758251 15641547076656207142137377)
      ·
        refine ⟨11731160307492155356603033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15641547076656207142137377 11731160307492155356603033)
        ·
          refine ⟨8798370230619116517452275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11731160307492155356603033 8798370230619116517452275)
          ·
            refine ⟨13197555345928674776178413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8798370230619116517452275 13197555345928674776178413)
            ·
              refine ⟨4949083254723253041066905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13197555345928674776178413 4949083254723253041066905)
              ·
                refine ⟨3711812441042439780800179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4949083254723253041066905 3711812441042439780800179)
                ·
                  refine ⟨5567718661563659671200269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711812441042439780800179 5567718661563659671200269)
                  ·
                    refine ⟨2087894498086372376700101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5567718661563659671200269 2087894498086372376700101)
                    ·
                      refine ⟨391480218391194820631269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2087894498086372376700101 391480218391194820631269)
                      ·
                        rfl

theorem cell23_762405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_762405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762405 prefixEnd_762405 := by exact prefixLift 762405
  have htrace : WordTrace (prefixWord ++ tailWord_762405) baseStart_762405 baseEnd_762405 := by
    simpa [prefixWord, tailWord_762405, baseEnd_762405] using wordTrace_append hprefix tailTrace_762405
  have hstable : (prefixWord ++ tailWord_762405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762405).length < 2 ^ (prefixWord ++ tailWord_762405).sum := by decide
  have hdescent : baseEnd_762405 < baseStart_762405 := by decide
  rcases family_descends (prefixWord ++ tailWord_762405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762442 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_762442 : Nat := 118140960795 + 762442 * 2 ^ 59
def prefixEnd_762442 : Nat := 4983230072969 + 3 ^ 40 * 762442 * 2
def baseEnd_762442 : Nat := 391499217175411175868599

theorem tailTrace_762442 : CollatzResearch.WordTrace tailWord_762442 prefixEnd_762442 391499217175411175868599 := by
  unfold tailWord_762442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6952136075952580892946395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18539029535873549047857053 6952136075952580892946395)
  ·
    refine ⟨10428204113928871339419593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6952136075952580892946395 10428204113928871339419593)
    ·
      refine ⟨7821153085446653504564695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10428204113928871339419593 7821153085446653504564695)
      ·
        refine ⟨11731729628169980256847043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7821153085446653504564695 11731729628169980256847043)
        ·
          refine ⟨17597594442254970385270565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11731729628169980256847043 17597594442254970385270565)
          ·
            refine ⟨3299548957922806947238231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17597594442254970385270565 3299548957922806947238231)
            ·
              refine ⟨4949323436884210420857347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299548957922806947238231 4949323436884210420857347)
              ·
                refine ⟨7423985155326315631286021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4949323436884210420857347 7423985155326315631286021)
                ·
                  refine ⟨1391997216623684180866129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7423985155326315631286021 1391997216623684180866129)
                  ·
                    refine ⟨1043997912467763135649597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1391997216623684180866129 1043997912467763135649597)
                    ·
                      refine ⟨391499217175411175868599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1043997912467763135649597 391499217175411175868599)
                      ·
                        rfl

theorem cell23_762442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_762442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762442 prefixEnd_762442 := by exact prefixLift 762442
  have htrace : WordTrace (prefixWord ++ tailWord_762442) baseStart_762442 baseEnd_762442 := by
    simpa [prefixWord, tailWord_762442, baseEnd_762442] using wordTrace_append hprefix tailTrace_762442
  have hstable : (prefixWord ++ tailWord_762442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762442).length < 2 ^ (prefixWord ++ tailWord_762442).sum := by decide
  have hdescent : baseEnd_762442 < baseStart_762442 := by decide
  rcases family_descends (prefixWord ++ tailWord_762442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762449 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 3, 4]
def baseStart_762449 : Nat := 118140960795 + 762449 * 2 ^ 59
def prefixEnd_762449 : Nat := 4983230072969 + 3 ^ 40 * 762449 * 2
def baseEnd_762449 : Nat := 130500937179997549493689

theorem tailTrace_762449 : CollatzResearch.WordTrace tailWord_762449 prefixEnd_762449 130500937179997549493689 := by
  unfold tailWord_762449
  simp only [CollatzResearch.WordTrace]
  refine ⟨27808799614784963767290401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18539199743189975844860267 27808799614784963767290401)
  ·
    refine ⟨20856599711088722825467801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27808799614784963767290401 20856599711088722825467801)
    ·
      refine ⟨15642449783316542119100851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20856599711088722825467801 15642449783316542119100851)
      ·
        refine ⟨23463674674974813178651277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15642449783316542119100851 23463674674974813178651277)
        ·
          refine ⟨8798878003115554941994229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23463674674974813178651277 8798878003115554941994229)
          ·
            refine ⟨824894812792083275811959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8798878003115554941994229 824894812792083275811959)
            ·
              refine ⟨1237342219188124913717939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824894812792083275811959 1237342219188124913717939)
              ·
                refine ⟨1856013328782187370576909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237342219188124913717939 1856013328782187370576909)
                ·
                  refine ⟨696004998293320263966341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1856013328782187370576909 696004998293320263966341)
                  ·
                    refine ⟨130500937179997549493689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696004998293320263966341 130500937179997549493689)
                    ·
                      rfl

theorem cell23_762449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_762449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762449 prefixEnd_762449 := by exact prefixLift 762449
  have htrace : WordTrace (prefixWord ++ tailWord_762449) baseStart_762449 baseEnd_762449 := by
    simpa [prefixWord, tailWord_762449, baseEnd_762449] using wordTrace_append hprefix tailTrace_762449
  have hstable : (prefixWord ++ tailWord_762449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762449).length < 2 ^ (prefixWord ++ tailWord_762449).sum := by decide
  have hdescent : baseEnd_762449 < baseStart_762449 := by decide
  rcases family_descends (prefixWord ++ tailWord_762449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762492 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_762492 : Nat := 118140960795 + 762492 * 2 ^ 59
def prefixEnd_762492 : Nat := 4983230072969 + 3 ^ 40 * 762492 * 2
def baseEnd_762492 : Nat := 130508297069378660081123

theorem tailTrace_762492 : CollatzResearch.WordTrace tailWord_762492 prefixEnd_762492 130508297069378660081123 := by
  unfold tailWord_762492
  simp only [CollatzResearch.WordTrace]
  refine ⟨13905183976814591055552865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18540245302419454740737153 13905183976814591055552865)
  ·
    refine ⟨10428887982610943291664649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13905183976814591055552865 10428887982610943291664649)
    ·
      refine ⟨7821665986958207468748487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10428887982610943291664649 7821665986958207468748487)
      ·
        refine ⟨11732498980437311203122731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7821665986958207468748487 11732498980437311203122731)
        ·
          refine ⟨17598748470655966804684097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11732498980437311203122731 17598748470655966804684097)
          ·
            refine ⟨13199061352991975103513073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17598748470655966804684097 13199061352991975103513073)
            ·
              refine ⟨9899296014743981327634805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13199061352991975103513073 9899296014743981327634805)
              ·
                refine ⟨928059001382248249465763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9899296014743981327634805 928059001382248249465763)
                ·
                  refine ⟨1392088502073372374198645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928059001382248249465763 1392088502073372374198645)
                  ·
                    refine ⟨130508297069378660081123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1392088502073372374198645 130508297069378660081123)
                    ·
                      rfl

theorem cell23_762492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_762492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762492 prefixEnd_762492 := by exact prefixLift 762492
  have htrace : WordTrace (prefixWord ++ tailWord_762492) baseStart_762492 baseEnd_762492 := by
    simpa [prefixWord, tailWord_762492, baseEnd_762492] using wordTrace_append hprefix tailTrace_762492
  have hstable : (prefixWord ++ tailWord_762492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762492).length < 2 ^ (prefixWord ++ tailWord_762492).sum := by decide
  have hdescent : baseEnd_762492 < baseStart_762492 := by decide
  rcases family_descends (prefixWord ++ tailWord_762492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762499 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 2, 3, 2]
def baseStart_762499 : Nat := 118140960795 + 762499 * 2 ^ 59
def prefixEnd_762499 : Nat := 4983230072969 + 3 ^ 40 * 762499 * 2
def baseEnd_762499 : Nat := 391528485572717452855837

theorem tailTrace_762499 : CollatzResearch.WordTrace tailWord_762499 prefixEnd_762499 391528485572717452855837 := by
  unfold tailWord_762499
  simp only [CollatzResearch.WordTrace]
  refine ⟨27810623264603822306610551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18540415509735881537740367 27810623264603822306610551)
  ·
    refine ⟨41715934896905733459915827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27810623264603822306610551 41715934896905733459915827)
    ·
      refine ⟨62573902345358600189873741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41715934896905733459915827 62573902345358600189873741)
      ·
        refine ⟨23465213379509475071202653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62573902345358600189873741 23465213379509475071202653)
        ·
          refine ⟨8799455017316053151700995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23465213379509475071202653 8799455017316053151700995)
          ·
            refine ⟨13199182525974079727551493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8799455017316053151700995 13199182525974079727551493)
            ·
              refine ⟨2474846723620139948915905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13199182525974079727551493 2474846723620139948915905)
              ·
                refine ⟨1856135042715104961686929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2474846723620139948915905 1856135042715104961686929)
                ·
                  refine ⟨1392101282036328721265197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1856135042715104961686929 1392101282036328721265197)
                  ·
                    refine ⟨522037980763623270474449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1392101282036328721265197 522037980763623270474449)
                    ·
                      refine ⟨391528485572717452855837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522037980763623270474449 391528485572717452855837)
                      ·
                        rfl

theorem cell23_762499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_762499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762499 prefixEnd_762499 := by exact prefixLift 762499
  have htrace : WordTrace (prefixWord ++ tailWord_762499) baseStart_762499 baseEnd_762499 := by
    simpa [prefixWord, tailWord_762499, baseEnd_762499] using wordTrace_append hprefix tailTrace_762499
  have hstable : (prefixWord ++ tailWord_762499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762499).length < 2 ^ (prefixWord ++ tailWord_762499).sum := by decide
  have hdescent : baseEnd_762499 < baseStart_762499 := by decide
  rcases family_descends (prefixWord ++ tailWord_762499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762505 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 5, 6]
def baseStart_762505 : Nat := 118140960795 + 762505 * 2 ^ 59
def prefixEnd_762505 : Nat := 4983230072969 + 3 ^ 40 * 762505 * 2
def baseEnd_762505 : Nat := 130510522152214809793603

theorem tailTrace_762505 : CollatzResearch.WordTrace tailWord_762505 prefixEnd_762505 130510522152214809793603 := by
  unfold tailWord_762505
  simp only [CollatzResearch.WordTrace]
  refine ⟨27810842102582085331328969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18540561401721390220885979 27810842102582085331328969)
  ·
    refine ⟨20858131576936563998496727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27810842102582085331328969 20858131576936563998496727)
    ·
      refine ⟨31287197365404845997745091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20858131576936563998496727 31287197365404845997745091)
      ·
        refine ⟨46930796048107268996617637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31287197365404845997745091 46930796048107268996617637)
        ·
          refine ⟨8799524259020112936865807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46930796048107268996617637 8799524259020112936865807)
          ·
            refine ⟨13199286388530169405298711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8799524259020112936865807 13199286388530169405298711)
            ·
              refine ⟨19798929582795254107948067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13199286388530169405298711 19798929582795254107948067)
              ·
                refine ⟨29698394374192881161922101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19798929582795254107948067 29698394374192881161922101)
                ·
                  refine ⟨2784224472580582608930197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29698394374192881161922101 2784224472580582608930197)
                  ·
                    refine ⟨130510522152214809793603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2784224472580582608930197 130510522152214809793603)
                    ·
                      rfl

theorem cell23_762505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_762505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762505 prefixEnd_762505 := by exact prefixLift 762505
  have htrace : WordTrace (prefixWord ++ tailWord_762505) baseStart_762505 baseEnd_762505 := by
    simpa [prefixWord, tailWord_762505, baseEnd_762505] using wordTrace_append hprefix tailTrace_762505
  have hstable : (prefixWord ++ tailWord_762505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762505).length < 2 ^ (prefixWord ++ tailWord_762505).sum := by decide
  have hdescent : baseEnd_762505 < baseStart_762505 := by decide
  rcases family_descends (prefixWord ++ tailWord_762505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762512 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 4, 6, 2]
def baseStart_762512 : Nat := 118140960795 + 762512 * 2 ^ 59
def prefixEnd_762512 : Nat := 4983230072969 + 3 ^ 40 * 762512 * 2
def baseEnd_762512 : Nat := 391535160821225901993277

theorem tailTrace_762512 : CollatzResearch.WordTrace tailWord_762512 prefixEnd_762512 391535160821225901993277 := by
  unfold tailWord_762512
  simp only [CollatzResearch.WordTrace]
  refine ⟨13905548706778362763416895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18540731609037817017889193 13905548706778362763416895)
  ·
    refine ⟨20858323060167544145125343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13905548706778362763416895 20858323060167544145125343)
    ·
      refine ⟨31287484590251316217688015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20858323060167544145125343 31287484590251316217688015)
      ·
        refine ⟨46931226885376974326532023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31287484590251316217688015 46931226885376974326532023)
        ·
          refine ⟨70396840328065461489798035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46931226885376974326532023 70396840328065461489798035)
          ·
            refine ⟨105595260492098192234697053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70396840328065461489798035 105595260492098192234697053)
            ·
              refine ⟨39598222684536822088011395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105595260492098192234697053 39598222684536822088011395)
              ·
                refine ⟨59397334026805233132017093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39598222684536822088011395 59397334026805233132017093)
                ·
                  refine ⟨11137000130025981212253205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59397334026805233132017093 11137000130025981212253205)
                  ·
                    refine ⟨522046881094967869324369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11137000130025981212253205 522046881094967869324369)
                    ·
                      refine ⟨391535160821225901993277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522046881094967869324369 391535160821225901993277)
                      ·
                        rfl

theorem cell23_762512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 6, 2].length) (baseStart_762512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762512 prefixEnd_762512 := by exact prefixLift 762512
  have htrace : WordTrace (prefixWord ++ tailWord_762512) baseStart_762512 baseEnd_762512 := by
    simpa [prefixWord, tailWord_762512, baseEnd_762512] using wordTrace_append hprefix tailTrace_762512
  have hstable : (prefixWord ++ tailWord_762512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762512).length < 2 ^ (prefixWord ++ tailWord_762512).sum := by decide
  have hdescent : baseEnd_762512 < baseStart_762512 := by decide
  rcases family_descends (prefixWord ++ tailWord_762512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762555 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 6]
def baseStart_762555 : Nat := 118140960795 + 762555 * 2 ^ 59
def prefixEnd_762555 : Nat := 4983230072969 + 3 ^ 40 * 762555 * 2
def baseEnd_762555 : Nat := 391557240489369233755579

theorem tailTrace_762555 : CollatzResearch.WordTrace tailWord_762555 prefixEnd_762555 391557240489369233755579 := by
  unfold tailWord_762555
  simp only [CollatzResearch.WordTrace]
  refine ⟨27812665752400943870649119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18541777168267295913766079 27812665752400943870649119)
  ·
    refine ⟨41718998628601415805973679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27812665752400943870649119 41718998628601415805973679)
    ·
      refine ⟨62578497942902123708960519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41718998628601415805973679 62578497942902123708960519)
      ·
        refine ⟨93867746914353185563440779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62578497942902123708960519 93867746914353185563440779)
        ·
          refine ⟨140801620371529778345161169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93867746914353185563440779 140801620371529778345161169)
          ·
            refine ⟨105601215278647333758870877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140801620371529778345161169 105601215278647333758870877)
            ·
              refine ⟨39600455729492750159576579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105601215278647333758870877 39600455729492750159576579)
              ·
                refine ⟨59400683594239125239364869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39600455729492750159576579 59400683594239125239364869)
                ·
                  refine ⟨11137628173919835982380913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59400683594239125239364869 11137628173919835982380913)
                  ·
                    refine ⟨8353221130439876986785685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11137628173919835982380913 8353221130439876986785685)
                    ·
                      refine ⟨391557240489369233755579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8353221130439876986785685 391557240489369233755579)
                      ·
                        rfl

theorem cell23_762555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_762555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762555 prefixEnd_762555 := by exact prefixLift 762555
  have htrace : WordTrace (prefixWord ++ tailWord_762555) baseStart_762555 baseEnd_762555 := by
    simpa [prefixWord, tailWord_762555, baseEnd_762555] using wordTrace_append hprefix tailTrace_762555
  have hstable : (prefixWord ++ tailWord_762555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762555).length < 2 ^ (prefixWord ++ tailWord_762555).sum := by decide
  have hdescent : baseEnd_762555 < baseStart_762555 := by decide
  rcases family_descends (prefixWord ++ tailWord_762555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762573 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_762573 : Nat := 118140960795 + 762573 * 2 ^ 59
def prefixEnd_762573 : Nat := 4983230072969 + 3 ^ 40 * 762573 * 2
def baseEnd_762573 : Nat := 130522161047050054443499

theorem tailTrace_762573 : CollatzResearch.WordTrace tailWord_762573 prefixEnd_762573 130522161047050054443499 := by
  unfold tailWord_762573
  simp only [CollatzResearch.WordTrace]
  refine ⟨27813322266335732944804373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18542214844223821963202915 27813322266335732944804373)
  ·
    refine ⟨1303749481234487481787705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27813322266335732944804373 1303749481234487481787705)
    ·
      refine ⟨977812110925865611340779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1303749481234487481787705 977812110925865611340779)
      ·
        refine ⟨1466718166388798417011169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977812110925865611340779 1466718166388798417011169)
        ·
          refine ⟨1100038624791598812758377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1466718166388798417011169 1100038624791598812758377)
          ·
            refine ⟨825028968593699109568783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100038624791598812758377 825028968593699109568783)
            ·
              refine ⟨1237543452890548664353175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825028968593699109568783 1237543452890548664353175)
              ·
                refine ⟨1856315179335822996529763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237543452890548664353175 1856315179335822996529763)
                ·
                  refine ⟨2784472769003734494794645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856315179335822996529763 2784472769003734494794645)
                  ·
                    refine ⟨130522161047050054443499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2784472769003734494794645 130522161047050054443499)
                    ·
                      rfl

theorem cell23_762573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_762573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762573 prefixEnd_762573 := by exact prefixLift 762573
  have htrace : WordTrace (prefixWord ++ tailWord_762573) baseStart_762573 baseEnd_762573 := by
    simpa [prefixWord, tailWord_762573, baseEnd_762573] using wordTrace_append hprefix tailTrace_762573
  have hstable : (prefixWord ++ tailWord_762573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762573).length < 2 ^ (prefixWord ++ tailWord_762573).sum := by decide
  have hdescent : baseEnd_762573 < baseStart_762573 := by decide
  rcases family_descends (prefixWord ++ tailWord_762573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762602 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_762602 : Nat := 118140960795 + 762602 * 2 ^ 59
def prefixEnd_762602 : Nat := 4983230072969 + 3 ^ 40 * 762602 * 2
def baseEnd_762602 : Nat := 391581374080130549867863

theorem tailTrace_762602 : CollatzResearch.WordTrace tailWord_762602 prefixEnd_762602 391581374080130549867863 := by
  unfold tailWord_762602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953594995807667724402515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18542919988820447265073373 6953594995807667724402515)
  ·
    refine ⟨10430392493711501586603773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6953594995807667724402515 10430392493711501586603773)
    ·
      refine ⟨3911397185141813094976415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10430392493711501586603773 3911397185141813094976415)
      ·
        refine ⟨5867095777712719642464623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911397185141813094976415 5867095777712719642464623)
        ·
          refine ⟨8800643666569079463696935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867095777712719642464623 8800643666569079463696935)
          ·
            refine ⟨13200965499853619195545403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8800643666569079463696935 13200965499853619195545403)
            ·
              refine ⟨19801448249780428793318105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13200965499853619195545403 19801448249780428793318105)
              ·
                refine ⟨14851086187335321594988579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19801448249780428793318105 14851086187335321594988579)
                ·
                  refine ⟨22276629281002982392482869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14851086187335321594988579 22276629281002982392482869)
                  ·
                    refine ⟨2088433995094029599295269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22276629281002982392482869 2088433995094029599295269)
                    ·
                      refine ⟨391581374080130549867863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2088433995094029599295269 391581374080130549867863)
                      ·
                        rfl

theorem cell23_762602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_762602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762602 prefixEnd_762602 := by exact prefixLift 762602
  have htrace : WordTrace (prefixWord ++ tailWord_762602) baseStart_762602 baseEnd_762602 := by
    simpa [prefixWord, tailWord_762602, baseEnd_762602] using wordTrace_append hprefix tailTrace_762602
  have hstable : (prefixWord ++ tailWord_762602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762602).length < 2 ^ (prefixWord ++ tailWord_762602).sum := by decide
  have hdescent : baseEnd_762602 < baseStart_762602 := by decide
  rcases family_descends (prefixWord ++ tailWord_762602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762659 : List Nat := [1, 1, 1, 4, 2, 1, 1, 7, 5]
def baseStart_762659 : Nat := 118140960795 + 762659 * 2 ^ 59
def prefixEnd_762659 : Nat := 4983230072969 + 3 ^ 40 * 762659 * 2
def baseEnd_762659 : Nat := 43512293608604091872789

theorem tailTrace_762659 : CollatzResearch.WordTrace tailWord_762659 prefixEnd_762659 43512293608604091872789 := by
  unfold tailWord_762659
  simp only [CollatzResearch.WordTrace]
  refine ⟨27816458944024169632435031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18544305962682779754956687 27816458944024169632435031)
  ·
    refine ⟨41724688416036254448652547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27816458944024169632435031 41724688416036254448652547)
    ·
      refine ⟨62587032624054381672978821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41724688416036254448652547 62587032624054381672978821)
      ·
        refine ⟨11735068617010196563683529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62587032624054381672978821 11735068617010196563683529)
        ·
          refine ⟨8801301462757647422762647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11735068617010196563683529 8801301462757647422762647)
          ·
            refine ⟨13201952194136471134143971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8801301462757647422762647 13201952194136471134143971)
            ·
              refine ⟨19802928291204706701215957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13201952194136471134143971 19802928291204706701215957)
              ·
                refine ⟨464131131825110313309749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19802928291204706701215957 464131131825110313309749)
                ·
                  refine ⟨43512293608604091872789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 464131131825110313309749 43512293608604091872789)
                  ·
                    rfl

theorem cell23_762659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 5].length) (baseStart_762659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762659 prefixEnd_762659 := by exact prefixLift 762659
  have htrace : WordTrace (prefixWord ++ tailWord_762659) baseStart_762659 baseEnd_762659 := by
    simpa [prefixWord, tailWord_762659, baseEnd_762659] using wordTrace_append hprefix tailTrace_762659
  have hstable : (prefixWord ++ tailWord_762659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762659).length < 2 ^ (prefixWord ++ tailWord_762659).sum := by decide
  have hdescent : baseEnd_762659 < baseStart_762659 := by decide
  rcases family_descends (prefixWord ++ tailWord_762659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762670 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_762670 : Nat := 118140960795 + 762670 * 2 ^ 59
def prefixEnd_762670 : Nat := 4983230072969 + 3 ^ 40 * 762670 * 2
def baseEnd_762670 : Nat := 391616290764636283817551

theorem tailTrace_762670 : CollatzResearch.WordTrace tailWord_762670 prefixEnd_762670 391616290764636283817551 := by
  unfold tailWord_762670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477107518373039813885683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18544573431322879007390309 3477107518373039813885683)
  ·
    refine ⟨5215661277559559720828525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3477107518373039813885683 5215661277559559720828525)
    ·
      refine ⟨1955872979084834895310697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5215661277559559720828525 1955872979084834895310697)
      ·
        refine ⟨1466904734313626171483023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1955872979084834895310697 1466904734313626171483023)
        ·
          refine ⟨2200357101470439257224535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1466904734313626171483023 2200357101470439257224535)
          ·
            refine ⟨3300535652205658885836803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2200357101470439257224535 3300535652205658885836803)
            ·
              refine ⟨4950803478308488328755205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300535652205658885836803 4950803478308488328755205)
              ·
                refine ⟨928275652182841561641601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4950803478308488328755205 928275652182841561641601)
                ·
                  refine ⟨696206739137131171231201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928275652182841561641601 696206739137131171231201)
                  ·
                    refine ⟨522155054352848378423401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 696206739137131171231201 522155054352848378423401)
                    ·
                      refine ⟨391616290764636283817551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522155054352848378423401 391616290764636283817551)
                      ·
                        rfl

theorem cell23_762670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_762670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762670 prefixEnd_762670 := by exact prefixLift 762670
  have htrace : WordTrace (prefixWord ++ tailWord_762670) baseStart_762670 baseEnd_762670 := by
    simpa [prefixWord, tailWord_762670, baseEnd_762670] using wordTrace_append hprefix tailTrace_762670
  have hstable : (prefixWord ++ tailWord_762670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762670).length < 2 ^ (prefixWord ++ tailWord_762670).sum := by decide
  have hdescent : baseEnd_762670 < baseStart_762670 := by decide
  rcases family_descends (prefixWord ++ tailWord_762670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762679 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 1, 7, 2]
def baseStart_762679 : Nat := 118140960795 + 762679 * 2 ^ 59
def prefixEnd_762679 : Nat := 4983230072969 + 3 ^ 40 * 762679 * 2
def baseEnd_762679 : Nat := 391620912090526748605009

theorem tailTrace_762679 : CollatzResearch.WordTrace tailWord_762679 prefixEnd_762679 391620912090526748605009 := by
  unfold tailWord_762679
  simp only [CollatzResearch.WordTrace]
  refine ⟨27817188403951713048163091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18544792269301142032108727 27817188403951713048163091)
  ·
    refine ⟨41725782605927569572244637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27817188403951713048163091 41725782605927569572244637)
    ·
      refine ⟨15647168477222838589591739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41725782605927569572244637 15647168477222838589591739)
      ·
        refine ⟨23470752715834257884387609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15647168477222838589591739 23470752715834257884387609)
        ·
          refine ⟨17603064536875693413290707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23470752715834257884387609 17603064536875693413290707)
          ·
            refine ⟨26404596805313540119936061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17603064536875693413290707 26404596805313540119936061)
            ·
              refine ⟨9901723801992577544976023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26404596805313540119936061 9901723801992577544976023)
              ·
                refine ⟨14852585702988866317464035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9901723801992577544976023 14852585702988866317464035)
                ·
                  refine ⟨22278878554483299476196053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14852585702988866317464035 22278878554483299476196053)
                  ·
                    refine ⟨522161216120702331473345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22278878554483299476196053 522161216120702331473345)
                    ·
                      refine ⟨391620912090526748605009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522161216120702331473345 391620912090526748605009)
                      ·
                        rfl

theorem cell23_762679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_762679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762679 prefixEnd_762679 := by exact prefixLift 762679
  have htrace : WordTrace (prefixWord ++ tailWord_762679) baseStart_762679 baseEnd_762679 := by
    simpa [prefixWord, tailWord_762679, baseEnd_762679] using wordTrace_append hprefix tailTrace_762679
  have hstable : (prefixWord ++ tailWord_762679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762679).length < 2 ^ (prefixWord ++ tailWord_762679).sum := by decide
  have hdescent : baseEnd_762679 < baseStart_762679 := by decide
  rcases family_descends (prefixWord ++ tailWord_762679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762709 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_762709 : Nat := 118140960795 + 762709 * 2 ^ 59
def prefixEnd_762709 : Nat := 4983230072969 + 3 ^ 40 * 762709 * 2
def baseEnd_762709 : Nat := 391636316510161631229871

theorem tailTrace_762709 : CollatzResearch.WordTrace tailWord_762709 prefixEnd_762709 391636316510161631229871 := by
  unfold tailWord_762709
  simp only [CollatzResearch.WordTrace]
  refine ⟨27818282593843028171755181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18545521729228685447836787 27818282593843028171755181)
  ·
    refine ⟨10431855972691135564408193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27818282593843028171755181 10431855972691135564408193)
    ·
      refine ⟨7823891979518351673306145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10431855972691135564408193 7823891979518351673306145)
      ·
        refine ⟨5867918984638763754979609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7823891979518351673306145 5867918984638763754979609)
        ·
          refine ⟨4400939238479072816234707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5867918984638763754979609 4400939238479072816234707)
          ·
            refine ⟨6601408857718609224352061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4400939238479072816234707 6601408857718609224352061)
            ·
              refine ⟨2475528321644478459132023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6601408857718609224352061 2475528321644478459132023)
              ·
                refine ⟨3713292482466717688698035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475528321644478459132023 3713292482466717688698035)
                ·
                  refine ⟨5569938723700076533047053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713292482466717688698035 5569938723700076533047053)
                  ·
                    refine ⟨2088727021387528699892645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5569938723700076533047053 2088727021387528699892645)
                    ·
                      refine ⟨391636316510161631229871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2088727021387528699892645 391636316510161631229871)
                      ·
                        rfl

theorem cell23_762709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_762709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762709 prefixEnd_762709 := by exact prefixLift 762709
  have htrace : WordTrace (prefixWord ++ tailWord_762709) baseStart_762709 baseEnd_762709 := by
    simpa [prefixWord, tailWord_762709, baseEnd_762709] using wordTrace_append hprefix tailTrace_762709
  have hstable : (prefixWord ++ tailWord_762709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762709).length < 2 ^ (prefixWord ++ tailWord_762709).sum := by decide
  have hdescent : baseEnd_762709 < baseStart_762709 := by decide
  rcases family_descends (prefixWord ++ tailWord_762709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762719 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 5, 4]
def baseStart_762719 : Nat := 118140960795 + 762719 * 2 ^ 59
def prefixEnd_762719 : Nat := 4983230072969 + 3 ^ 40 * 762719 * 2
def baseEnd_762719 : Nat := 130547150438902197368275

theorem tailTrace_762719 : CollatzResearch.WordTrace tailWord_762719 prefixEnd_762719 130547150438902197368275 := by
  unfold tailWord_762719
  simp only [CollatzResearch.WordTrace]
  refine ⟨27818647323806799879619211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18545764882537866586412807 27818647323806799879619211)
  ·
    refine ⟨41727970985710199819428817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27818647323806799879619211 41727970985710199819428817)
    ·
      refine ⟨31295978239282649864571613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41727970985710199819428817 31295978239282649864571613)
      ·
        refine ⟨11735991839730993699214355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31295978239282649864571613 11735991839730993699214355)
        ·
          refine ⟨17603987759596490548821533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11735991839730993699214355 17603987759596490548821533)
          ·
            refine ⟨6601495409848683955808075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17603987759596490548821533 6601495409848683955808075)
            ·
              refine ⟨9902243114773025933712113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6601495409848683955808075 9902243114773025933712113)
              ·
                refine ⟨7426682336079769450284085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9902243114773025933712113 7426682336079769450284085)
                ·
                  refine ⟨696251469007478385964133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7426682336079769450284085 696251469007478385964133)
                  ·
                    refine ⟨130547150438902197368275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696251469007478385964133 130547150438902197368275)
                    ·
                      rfl

theorem cell23_762719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 4].length) (baseStart_762719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762719 prefixEnd_762719 := by exact prefixLift 762719
  have htrace : WordTrace (prefixWord ++ tailWord_762719) baseStart_762719 baseEnd_762719 := by
    simpa [prefixWord, tailWord_762719, baseEnd_762719] using wordTrace_append hprefix tailTrace_762719
  have hstable : (prefixWord ++ tailWord_762719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762719).length < 2 ^ (prefixWord ++ tailWord_762719).sum := by decide
  have hdescent : baseEnd_762719 < baseStart_762719 := by decide
  rcases family_descends (prefixWord ++ tailWord_762719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762749 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 6]
def baseStart_762749 : Nat := 118140960795 + 762749 * 2 ^ 59
def prefixEnd_762749 : Nat := 4983230072969 + 3 ^ 40 * 762749 * 2
def baseEnd_762749 : Nat := 43517428415149052747743

theorem tailTrace_762749 : CollatzResearch.WordTrace tailWord_762749 prefixEnd_762749 43517428415149052747743 := by
  unfold tailWord_762749
  simp only [CollatzResearch.WordTrace]
  refine ⟨27819741513698115003211301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18546494342465410002140867 27819741513698115003211301)
  ·
    refine ⟨5216201533818396563102119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27819741513698115003211301 5216201533818396563102119)
    ·
      refine ⟨7824302300727594844653179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5216201533818396563102119 7824302300727594844653179)
      ·
        refine ⟨11736453451091392266979769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7824302300727594844653179 11736453451091392266979769)
        ·
          refine ⟨8802340088318544200234827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11736453451091392266979769 8802340088318544200234827)
          ·
            refine ⟨13203510132477816300352241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802340088318544200234827 13203510132477816300352241)
            ·
              refine ⟨9902632599358362225264181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13203510132477816300352241 9902632599358362225264181)
              ·
                refine ⟨928371806189846458618517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9902632599358362225264181 928371806189846458618517)
                ·
                  refine ⟨43517428415149052747743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 928371806189846458618517 43517428415149052747743)
                  ·
                    rfl

theorem cell23_762749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_762749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762749 prefixEnd_762749 := by exact prefixLift 762749
  have htrace : WordTrace (prefixWord ++ tailWord_762749) baseStart_762749 baseEnd_762749 := by
    simpa [prefixWord, tailWord_762749, baseEnd_762749] using wordTrace_append hprefix tailTrace_762749
  have hstable : (prefixWord ++ tailWord_762749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762749).length < 2 ^ (prefixWord ++ tailWord_762749).sum := by decide
  have hdescent : baseEnd_762749 < baseStart_762749 := by decide
  rcases family_descends (prefixWord ++ tailWord_762749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762816 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_762816 : Nat := 118140960795 + 762816 * 2 ^ 59
def prefixEnd_762816 : Nat := 4983230072969 + 3 ^ 40 * 762816 * 2
def baseEnd_762816 : Nat := 391691258940192712591879

theorem tailTrace_762816 : CollatzResearch.WordTrace tailWord_762816 prefixEnd_762816 391691258940192712591879 := by
  unfold tailWord_762816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13911092602227692722950151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18548123469636923630600201 13911092602227692722950151)
  ·
    refine ⟨20866638903341539084425227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13911092602227692722950151 20866638903341539084425227)
    ·
      refine ⟨31299958355012308626637841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20866638903341539084425227 31299958355012308626637841)
      ·
        refine ⟨23474968766259231469978381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31299958355012308626637841 23474968766259231469978381)
        ·
          refine ⟨8803113287347211801241893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23474968766259231469978381 8803113287347211801241893)
          ·
            refine ⟨1650583741377602212732855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8803113287347211801241893 1650583741377602212732855)
            ·
              refine ⟨2475875612066403319099283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650583741377602212732855 2475875612066403319099283)
              ·
                refine ⟨3713813418099604978648925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475875612066403319099283 3713813418099604978648925)
                ·
                  refine ⟨1392680031787351866993347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3713813418099604978648925 1392680031787351866993347)
                  ·
                    refine ⟨2089020047681027800490021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1392680031787351866993347 2089020047681027800490021)
                    ·
                      refine ⟨391691258940192712591879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2089020047681027800490021 391691258940192712591879)
                      ·
                        rfl

theorem cell23_762816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_762816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762816 prefixEnd_762816 := by exact prefixLift 762816
  have htrace : WordTrace (prefixWord ++ tailWord_762816) baseStart_762816 baseEnd_762816 := by
    simpa [prefixWord, tailWord_762816, baseEnd_762816] using wordTrace_append hprefix tailTrace_762816
  have hstable : (prefixWord ++ tailWord_762816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762816).length < 2 ^ (prefixWord ++ tailWord_762816).sum := by decide
  have hdescent : baseEnd_762816 < baseStart_762816 := by decide
  rcases family_descends (prefixWord ++ tailWord_762816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762819 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 3]
def baseStart_762819 : Nat := 118140960795 + 762819 * 2 ^ 59
def prefixEnd_762819 : Nat := 4983230072969 + 3 ^ 40 * 762819 * 2
def baseEnd_762819 : Nat := 391692799382156200854365

theorem tailTrace_762819 : CollatzResearch.WordTrace tailWord_762819 prefixEnd_762819 391692799382156200854365 := by
  unfold tailWord_762819
  simp only [CollatzResearch.WordTrace]
  refine ⟨27822294623444516958259511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18548196415629677972173007 27822294623444516958259511)
  ·
    refine ⟨41733441935166775437389267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27822294623444516958259511 41733441935166775437389267)
    ·
      refine ⟨62600162902750163156083901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41733441935166775437389267 62600162902750163156083901)
      ·
        refine ⟨23475061088531311183531463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62600162902750163156083901 23475061088531311183531463)
        ·
          refine ⟨35212591632796966775297195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23475061088531311183531463 35212591632796966775297195)
          ·
            refine ⟨52818887449195450162945793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35212591632796966775297195 52818887449195450162945793)
            ·
              refine ⟨39614165586896587622209345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52818887449195450162945793 39614165586896587622209345)
              ·
                refine ⟨29710624190172440716657009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39614165586896587622209345 29710624190172440716657009)
                ·
                  refine ⟨22282968142629330537492757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29710624190172440716657009 22282968142629330537492757)
                  ·
                    refine ⟨1044514131685749868944973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22282968142629330537492757 1044514131685749868944973)
                    ·
                      refine ⟨391692799382156200854365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1044514131685749868944973 391692799382156200854365)
                      ·
                        rfl

theorem cell23_762819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_762819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762819 prefixEnd_762819 := by exact prefixLift 762819
  have htrace : WordTrace (prefixWord ++ tailWord_762819) baseStart_762819 baseEnd_762819 := by
    simpa [prefixWord, tailWord_762819, baseEnd_762819] using wordTrace_append hprefix tailTrace_762819
  have hstable : (prefixWord ++ tailWord_762819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762819).length < 2 ^ (prefixWord ++ tailWord_762819).sum := by decide
  have hdescent : baseEnd_762819 < baseStart_762819 := by decide
  rcases family_descends (prefixWord ++ tailWord_762819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762833 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 1, 1, 4]
def baseStart_762833 : Nat := 118140960795 + 762833 * 2 ^ 59
def prefixEnd_762833 : Nat := 4983230072969 + 3 ^ 40 * 762833 * 2
def baseEnd_762833 : Nat := 391699988111319146079301

theorem tailTrace_762833 : CollatzResearch.WordTrace tailWord_762833 prefixEnd_762833 391699988111319146079301 := by
  unfold tailWord_762833
  simp only [CollatzResearch.WordTrace]
  refine ⟨27822805245393797349269153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18548536830262531566179435 27822805245393797349269153)
  ·
    refine ⟨20867103934045348011951865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27822805245393797349269153 20867103934045348011951865)
    ·
      refine ⟨15650327950534011008963899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20867103934045348011951865 15650327950534011008963899)
      ·
        refine ⟨23475491925801016513445849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15650327950534011008963899 23475491925801016513445849)
        ·
          refine ⟨17606618944350762385084387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23475491925801016513445849 17606618944350762385084387)
          ·
            refine ⟨26409928416526143577626581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17606618944350762385084387 26409928416526143577626581)
            ·
              refine ⟨618982697262331490100623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26409928416526143577626581 618982697262331490100623)
              ·
                refine ⟨928474045893497235150935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618982697262331490100623 928474045893497235150935)
                ·
                  refine ⟨1392711068840245852726403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928474045893497235150935 1392711068840245852726403)
                  ·
                    refine ⟨2089066603260368779089605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1392711068840245852726403 2089066603260368779089605)
                    ·
                      refine ⟨391699988111319146079301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2089066603260368779089605 391699988111319146079301)
                      ·
                        rfl

theorem cell23_762833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_762833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762833 prefixEnd_762833 := by exact prefixLift 762833
  have htrace : WordTrace (prefixWord ++ tailWord_762833) baseStart_762833 baseEnd_762833 := by
    simpa [prefixWord, tailWord_762833, baseEnd_762833] using wordTrace_append hprefix tailTrace_762833
  have hstable : (prefixWord ++ tailWord_762833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762833).length < 2 ^ (prefixWord ++ tailWord_762833).sum := by decide
  have hdescent : baseEnd_762833 < baseStart_762833 := by decide
  rcases family_descends (prefixWord ++ tailWord_762833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762939 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 7]
def baseStart_762939 : Nat := 118140960795 + 762939 * 2 ^ 59
def prefixEnd_762939 : Nat := 4983230072969 + 3 ^ 40 * 762939 * 2
def baseEnd_762939 : Nat := 391754417060695731353813

theorem tailTrace_762939 : CollatzResearch.WordTrace tailWord_762939 prefixEnd_762939 391754417060695731353813 := by
  unfold tailWord_762939
  simp only [CollatzResearch.WordTrace]
  refine ⟨27826671383009777452627871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18551114255339851635085247 27826671383009777452627871)
  ·
    refine ⟨41740007074514666178941807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27826671383009777452627871 41740007074514666178941807)
    ·
      refine ⟨62610010611771999268412711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41740007074514666178941807 62610010611771999268412711)
      ·
        refine ⟨93915015917657998902619067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62610010611771999268412711 93915015917657998902619067)
        ·
          refine ⟨140872523876486998353928601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93915015917657998902619067 140872523876486998353928601)
          ·
            refine ⟨105654392907365248765446451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140872523876486998353928601 105654392907365248765446451)
            ·
              refine ⟨158481589361047873148169677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105654392907365248765446451 158481589361047873148169677)
              ·
                refine ⟨59430596010392952430563629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158481589361047873148169677 59430596010392952430563629)
                ·
                  refine ⟨22286473503897357161461361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59430596010392952430563629 22286473503897357161461361)
                  ·
                    refine ⟨16714855127923017871096021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22286473503897357161461361 16714855127923017871096021)
                    ·
                      refine ⟨391754417060695731353813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16714855127923017871096021 391754417060695731353813)
                      ·
                        rfl

theorem cell23_762939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_762939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762939 prefixEnd_762939 := by exact prefixLift 762939
  have htrace : WordTrace (prefixWord ++ tailWord_762939) baseStart_762939 baseEnd_762939 := by
    simpa [prefixWord, tailWord_762939, baseEnd_762939] using wordTrace_append hprefix tailTrace_762939
  have hstable : (prefixWord ++ tailWord_762939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762939).length < 2 ^ (prefixWord ++ tailWord_762939).sum := by decide
  have hdescent : baseEnd_762939 < baseStart_762939 := by decide
  rcases family_descends (prefixWord ++ tailWord_762939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762940 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_762940 : Nat := 118140960795 + 762940 * 2 ^ 59
def prefixEnd_762940 : Nat := 4983230072969 + 3 ^ 40 * 762940 * 2
def baseEnd_762940 : Nat := 391754930541350227441309

theorem tailTrace_762940 : CollatzResearch.WordTrace tailWord_762940 prefixEnd_762940 391754930541350227441309 := by
  unfold tailWord_762940
  simp only [CollatzResearch.WordTrace]
  refine ⟨13913353928003077311707137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18551138570670769748942849 13913353928003077311707137)
  ·
    refine ⟨10435015446002307983780353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13913353928003077311707137 10435015446002307983780353)
    ·
      refine ⟨7826261584501730987835265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10435015446002307983780353 7826261584501730987835265)
      ·
        refine ⟨5869696188376298240876449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7826261584501730987835265 5869696188376298240876449)
        ·
          refine ⟨4402272141282223680657337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5869696188376298240876449 4402272141282223680657337)
          ·
            refine ⟨3301704105961667760493003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4402272141282223680657337 3301704105961667760493003)
            ·
              refine ⟨4952556158942501640739505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3301704105961667760493003 4952556158942501640739505)
              ·
                refine ⟨3714417119206876230554629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4952556158942501640739505 3714417119206876230554629)
                ·
                  refine ⟨696453209851289293228993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3714417119206876230554629 696453209851289293228993)
                  ·
                    refine ⟨522339907388466969921745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 696453209851289293228993 522339907388466969921745)
                    ·
                      refine ⟨391754930541350227441309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522339907388466969921745 391754930541350227441309)
                      ·
                        rfl

theorem cell23_762940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_762940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762940 prefixEnd_762940 := by exact prefixLift 762940
  have htrace : WordTrace (prefixWord ++ tailWord_762940) baseStart_762940 baseEnd_762940 := by
    simpa [prefixWord, tailWord_762940, baseEnd_762940] using wordTrace_append hprefix tailTrace_762940
  have hstable : (prefixWord ++ tailWord_762940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762940).length < 2 ^ (prefixWord ++ tailWord_762940).sum := by decide
  have hdescent : baseEnd_762940 < baseStart_762940 := by decide
  rcases family_descends (prefixWord ++ tailWord_762940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762957 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_762957 : Nat := 118140960795 + 762957 * 2 ^ 59
def prefixEnd_762957 : Nat := 4983230072969 + 3 ^ 40 * 762957 * 2
def baseEnd_762957 : Nat := 391763659712476660928731

theorem tailTrace_762957 : CollatzResearch.WordTrace tailWord_762957 prefixEnd_762957 391763659712476660928731 := by
  unfold tailWord_762957
  simp only [CollatzResearch.WordTrace]
  refine ⟨27827327896944566526783125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18551551931296377684522083 27827327896944566526783125)
  ·
    refine ⟨1304405995169276555942959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27827327896944566526783125 1304405995169276555942959)
    ·
      refine ⟨1956608992753914833914439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1304405995169276555942959 1956608992753914833914439)
      ·
        refine ⟨2934913489130872250871659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1956608992753914833914439 2934913489130872250871659)
        ·
          refine ⟨4402370233696308376307489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934913489130872250871659 4402370233696308376307489)
          ·
            refine ⟨3301777675272231282230617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4402370233696308376307489 3301777675272231282230617)
            ·
              refine ⟨2476333256454173461672963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3301777675272231282230617 2476333256454173461672963)
              ·
                refine ⟨3714499884681260192509445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476333256454173461672963 3714499884681260192509445)
                ·
                  refine ⟨696468728377736286095521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3714499884681260192509445 696468728377736286095521)
                  ·
                    refine ⟨522351546283302214571641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 696468728377736286095521 522351546283302214571641)
                    ·
                      refine ⟨391763659712476660928731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522351546283302214571641 391763659712476660928731)
                      ·
                        rfl

theorem cell23_762957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_762957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762957 prefixEnd_762957 := by exact prefixLift 762957
  have htrace : WordTrace (prefixWord ++ tailWord_762957) baseStart_762957 baseEnd_762957 := by
    simpa [prefixWord, tailWord_762957, baseEnd_762957] using wordTrace_append hprefix tailTrace_762957
  have hstable : (prefixWord ++ tailWord_762957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762957).length < 2 ^ (prefixWord ++ tailWord_762957).sum := by decide
  have hdescent : baseEnd_762957 < baseStart_762957 := by decide
  rcases family_descends (prefixWord ++ tailWord_762957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762976 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 4, 5]
def baseStart_762976 : Nat := 118140960795 + 762976 * 2 ^ 59
def prefixEnd_762976 : Nat := 4983230072969 + 3 ^ 40 * 762976 * 2
def baseEnd_762976 : Nat := 130591138614970695530381

theorem tailTrace_762976 : CollatzResearch.WordTrace tailWord_762976 prefixEnd_762976 130591138614970695530381 := by
  unfold tailWord_762976
  simp only [CollatzResearch.WordTrace]
  refine ⟨13914010441937866385862391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18552013922583821847816521 13914010441937866385862391)
  ·
    refine ⟨20871015662906799578793587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13914010441937866385862391 20871015662906799578793587)
    ·
      refine ⟨31306523494360199368190381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20871015662906799578793587 31306523494360199368190381)
      ·
        refine ⟨11739946310385074763071393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31306523494360199368190381 11739946310385074763071393)
        ·
          refine ⟨8804959732788806072303545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11739946310385074763071393 8804959732788806072303545)
          ·
            refine ⟨6603719799591604554227659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8804959732788806072303545 6603719799591604554227659)
            ·
              refine ⟨9905579699387406831341489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603719799591604554227659 9905579699387406831341489)
              ·
                refine ⟨7429184774540555123506117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9905579699387406831341489 7429184774540555123506117)
                ·
                  refine ⟨1392972145226354085657397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7429184774540555123506117 1392972145226354085657397)
                  ·
                    refine ⟨130591138614970695530381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1392972145226354085657397 130591138614970695530381)
                    ·
                      rfl

theorem cell23_762976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_762976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_762976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_762976 prefixEnd_762976 := by exact prefixLift 762976
  have htrace : WordTrace (prefixWord ++ tailWord_762976) baseStart_762976 baseEnd_762976 := by
    simpa [prefixWord, tailWord_762976, baseEnd_762976] using wordTrace_append hprefix tailTrace_762976
  have hstable : (prefixWord ++ tailWord_762976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762976).length < 2 ^ (prefixWord ++ tailWord_762976).sum := by decide
  have hdescent : baseEnd_762976 < baseStart_762976 := by decide
  rcases family_descends (prefixWord ++ tailWord_762976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763047 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_763047 : Nat := 118140960795 + 763047 * 2 ^ 59
def prefixEnd_763047 : Nat := 4983230072969 + 3 ^ 40 * 763047 * 2
def baseEnd_763047 : Nat := 391809872971381308803317

theorem tailTrace_763047 : CollatzResearch.WordTrace tailWord_763047 prefixEnd_763047 391809872971381308803317 := by
  unfold tailWord_763047
  simp only [CollatzResearch.WordTrace]
  refine ⟨27830610466618511897559395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18553740311079007931706263 27830610466618511897559395)
  ·
    refine ⟨41745915699927767846339093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27830610466618511897559395 41745915699927767846339093)
    ·
      refine ⟨1956839798434114117797145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41745915699927767846339093 1956839798434114117797145)
      ·
        refine ⟨1467629848825585588347859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1956839798434114117797145 1467629848825585588347859)
        ·
          refine ⟨2201444773238378382521789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467629848825585588347859 2201444773238378382521789)
          ·
            refine ⟨825541789964391893445671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2201444773238378382521789 825541789964391893445671)
            ·
              refine ⟨1238312684946587840168507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825541789964391893445671 1238312684946587840168507)
              ·
                refine ⟨1857469027419881760252761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238312684946587840168507 1857469027419881760252761)
                ·
                  refine ⟨1393101770564911320189571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1857469027419881760252761 1393101770564911320189571)
                  ·
                    refine ⟨2089652655847366980284357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1393101770564911320189571 2089652655847366980284357)
                    ·
                      refine ⟨391809872971381308803317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2089652655847366980284357 391809872971381308803317)
                      ·
                        rfl

theorem cell23_763047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_763047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763047 prefixEnd_763047 := by exact prefixLift 763047
  have htrace : WordTrace (prefixWord ++ tailWord_763047) baseStart_763047 baseEnd_763047 := by
    simpa [prefixWord, tailWord_763047, baseEnd_763047] using wordTrace_append hprefix tailTrace_763047
  have hstable : (prefixWord ++ tailWord_763047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763047).length < 2 ^ (prefixWord ++ tailWord_763047).sum := by decide
  have hdescent : baseEnd_763047 < baseStart_763047 := by decide
  rcases family_descends (prefixWord ++ tailWord_763047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763057 : List Nat := [1, 2, 2, 5, 1, 1, 1, 5, 1, 4]
def baseStart_763057 : Nat := 118140960795 + 763057 * 2 ^ 59
def prefixEnd_763057 : Nat := 4983230072969 + 3 ^ 40 * 763057 * 2
def baseEnd_763057 : Nat := 130605002592642089892757

theorem tailTrace_763057 : CollatzResearch.WordTrace tailWord_763057 prefixEnd_763057 130605002592642089892757 := by
  unfold tailWord_763057
  simp only [CollatzResearch.WordTrace]
  refine ⟨27830975196582283605423425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18553983464388189070282283 27830975196582283605423425)
  ·
    refine ⟨20873231397436712704067569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27830975196582283605423425 20873231397436712704067569)
    ·
      refine ⟨15654923548077534528050677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20873231397436712704067569 15654923548077534528050677)
      ·
        refine ⟨1467649082632268862004751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15654923548077534528050677 1467649082632268862004751)
        ·
          refine ⟨2201473623948403293007127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467649082632268862004751 2201473623948403293007127)
          ·
            refine ⟨3302210435922604939510691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201473623948403293007127 3302210435922604939510691)
            ·
              refine ⟨4953315653883907409266037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302210435922604939510691 4953315653883907409266037)
              ·
                refine ⟨464373342551616319618691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4953315653883907409266037 464373342551616319618691)
                ·
                  refine ⟨696560013827424479428037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464373342551616319618691 696560013827424479428037)
                  ·
                    refine ⟨130605002592642089892757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696560013827424479428037 130605002592642089892757)
                    ·
                      rfl

theorem cell23_763057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_763057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763057 prefixEnd_763057 := by exact prefixLift 763057
  have htrace : WordTrace (prefixWord ++ tailWord_763057) baseStart_763057 baseEnd_763057 := by
    simpa [prefixWord, tailWord_763057, baseEnd_763057] using wordTrace_append hprefix tailTrace_763057
  have hstable : (prefixWord ++ tailWord_763057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763057).length < 2 ^ (prefixWord ++ tailWord_763057).sum := by decide
  have hdescent : baseEnd_763057 < baseStart_763057 := by decide
  rcases family_descends (prefixWord ++ tailWord_763057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763070 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_763070 : Nat := 118140960795 + 763070 * 2 ^ 59
def prefixEnd_763070 : Nat := 4983230072969 + 3 ^ 40 * 763070 * 2
def baseEnd_763070 : Nat := 43535742558492746535079

theorem tailTrace_763070 : CollatzResearch.WordTrace tailWord_763070 prefixEnd_763070 43535742558492746535079 := by
  unfold tailWord_763070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478931168191898353205833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18554299563690124550431109 3478931168191898353205833)
  ·
    refine ⟨2609198376143923764904375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3478931168191898353205833 2609198376143923764904375)
    ·
      refine ⟨3913797564215885647356563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2609198376143923764904375 3913797564215885647356563)
      ·
        refine ⟨5870696346323828471034845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3913797564215885647356563 5870696346323828471034845)
        ·
          refine ⟨2201511129871435676638067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5870696346323828471034845 2201511129871435676638067)
          ·
            refine ⟨3302266694807153514957101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201511129871435676638067 3302266694807153514957101)
            ·
              refine ⟨1238350010552682568108913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3302266694807153514957101 1238350010552682568108913)
              ·
                refine ⟨928762507914511926081685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238350010552682568108913 928762507914511926081685)
                ·
                  refine ⟨43535742558492746535079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 928762507914511926081685 43535742558492746535079)
                  ·
                    rfl

theorem cell23_763070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_763070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763070 prefixEnd_763070 := by exact prefixLift 763070
  have htrace : WordTrace (prefixWord ++ tailWord_763070) baseStart_763070 baseEnd_763070 := by
    simpa [prefixWord, tailWord_763070, baseEnd_763070] using wordTrace_append hprefix tailTrace_763070
  have hstable : (prefixWord ++ tailWord_763070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763070).length < 2 ^ (prefixWord ++ tailWord_763070).sum := by decide
  have hdescent : baseEnd_763070 < baseStart_763070 := by decide
  rcases family_descends (prefixWord ++ tailWord_763070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763080 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_763080 : Nat := 118140960795 + 763080 * 2 ^ 59
def prefixEnd_763080 : Nat := 4983230072969 + 3 ^ 40 * 763080 * 2
def baseEnd_763080 : Nat := 391826817832979679690665

theorem tailTrace_763080 : CollatzResearch.WordTrace tailWord_763080 prefixEnd_763080 391826817832979679690665 := by
  unfold tailWord_763080
  simp only [CollatzResearch.WordTrace]
  refine ⟨13915907037749479266755347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18554542716999305689007129 13915907037749479266755347)
  ·
    refine ⟨20873860556624218900133021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13915907037749479266755347 20873860556624218900133021)
    ·
      refine ⟨7827697708734082087549883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20873860556624218900133021 7827697708734082087549883)
      ·
        refine ⟨11741546563101123131324825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7827697708734082087549883 11741546563101123131324825)
        ·
          refine ⟨8806159922325842348493619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11741546563101123131324825 8806159922325842348493619)
          ·
            refine ⟨13209239883488763522740429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8806159922325842348493619 13209239883488763522740429)
            ·
              refine ⟨4953464956308286321027661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13209239883488763522740429 4953464956308286321027661)
              ·
                refine ⟨1857549358615607370385373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4953464956308286321027661 1857549358615607370385373)
                ·
                  refine ⟨696581009480852763894515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1857549358615607370385373 696581009480852763894515)
                  ·
                    refine ⟨1044871514221279145841773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 696581009480852763894515 1044871514221279145841773)
                    ·
                      refine ⟨391826817832979679690665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1044871514221279145841773 391826817832979679690665)
                      ·
                        rfl

theorem cell23_763080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_763080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763080 prefixEnd_763080 := by exact prefixLift 763080
  have htrace : WordTrace (prefixWord ++ tailWord_763080) baseStart_763080 baseEnd_763080 := by
    simpa [prefixWord, tailWord_763080, baseEnd_763080] using wordTrace_append hprefix tailTrace_763080
  have hstable : (prefixWord ++ tailWord_763080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763080).length < 2 ^ (prefixWord ++ tailWord_763080).sum := by decide
  have hdescent : baseEnd_763080 < baseStart_763080 := by decide
  rcases family_descends (prefixWord ++ tailWord_763080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763090 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_763090 : Nat := 118140960795 + 763090 * 2 ^ 59
def prefixEnd_763090 : Nat := 4983230072969 + 3 ^ 40 * 763090 * 2
def baseEnd_763090 : Nat := 391831952639524640565619

theorem tailTrace_763090 : CollatzResearch.WordTrace tailWord_763090 prefixEnd_763090 391831952639524640565619 := by
  unfold tailWord_763090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958044701365682560343681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18554785870308486827583149 6958044701365682560343681)
  ·
    refine ⟨5218533526024261920257761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6958044701365682560343681 5218533526024261920257761)
    ·
      refine ⟨3913900144518196440193321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5218533526024261920257761 3913900144518196440193321)
      ·
        refine ⟨2935425108388647330144991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3913900144518196440193321 2935425108388647330144991)
        ·
          refine ⟨4403137662582970995217487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935425108388647330144991 4403137662582970995217487)
          ·
            refine ⟨6604706493874456492826231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403137662582970995217487 6604706493874456492826231)
            ·
              refine ⟨9907059740811684739239347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6604706493874456492826231 9907059740811684739239347)
              ·
                refine ⟨14860589611217527108859021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9907059740811684739239347 14860589611217527108859021)
                ·
                  refine ⟨5572721104206572665822133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14860589611217527108859021 5572721104206572665822133)
                  ·
                    refine ⟨522442603519366187420825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5572721104206572665822133 522442603519366187420825)
                    ·
                      refine ⟨391831952639524640565619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522442603519366187420825 391831952639524640565619)
                      ·
                        rfl

theorem cell23_763090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_763090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763090 prefixEnd_763090 := by exact prefixLift 763090
  have htrace : WordTrace (prefixWord ++ tailWord_763090) baseStart_763090 baseEnd_763090 := by
    simpa [prefixWord, tailWord_763090, baseEnd_763090] using wordTrace_append hprefix tailTrace_763090
  have hstable : (prefixWord ++ tailWord_763090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763090).length < 2 ^ (prefixWord ++ tailWord_763090).sum := by decide
  have hdescent : baseEnd_763090 < baseStart_763090 := by decide
  rcases family_descends (prefixWord ++ tailWord_763090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763103 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_763103 : Nat := 118140960795 + 763103 * 2 ^ 59
def prefixEnd_763103 : Nat := 4983230072969 + 3 ^ 40 * 763103 * 2
def baseEnd_763103 : Nat := 391838627888033089703059

theorem tailTrace_763103 : CollatzResearch.WordTrace tailWord_763103 prefixEnd_763103 391838627888033089703059 := by
  unfold tailWord_763103
  simp only [CollatzResearch.WordTrace]
  refine ⟨27832652954415633461597963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18555101969610422307731975 27832652954415633461597963)
  ·
    refine ⟨41748979431623450192396945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27832652954415633461597963 41748979431623450192396945)
    ·
      refine ⟨31311734573717587644297709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41748979431623450192396945 31311734573717587644297709)
      ·
        refine ⟨11741900465144095366611641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31311734573717587644297709 11741900465144095366611641)
        ·
          refine ⟨8806425348858071524958731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11741900465144095366611641 8806425348858071524958731)
          ·
            refine ⟨13209638023287107287438097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8806425348858071524958731 13209638023287107287438097)
            ·
              refine ⟨9907228517465330465578573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13209638023287107287438097 9907228517465330465578573)
              ·
                refine ⟨3715210694049498924591965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9907228517465330465578573 3715210694049498924591965)
                ·
                  refine ⟨1393204010268562096721987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3715210694049498924591965 1393204010268562096721987)
                  ·
                    refine ⟨2089806015402843145082981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1393204010268562096721987 2089806015402843145082981)
                    ·
                      refine ⟨391838627888033089703059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2089806015402843145082981 391838627888033089703059)
                      ·
                        rfl

theorem cell23_763103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_763103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763103 prefixEnd_763103 := by exact prefixLift 763103
  have htrace : WordTrace (prefixWord ++ tailWord_763103) baseStart_763103 baseEnd_763103 := by
    simpa [prefixWord, tailWord_763103, baseEnd_763103] using wordTrace_append hprefix tailTrace_763103
  have hstable : (prefixWord ++ tailWord_763103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763103).length < 2 ^ (prefixWord ++ tailWord_763103).sum := by decide
  have hdescent : baseEnd_763103 < baseStart_763103 := by decide
  rcases family_descends (prefixWord ++ tailWord_763103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763114 : List Nat := [3, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_763114 : Nat := 118140960795 + 763114 * 2 ^ 59
def prefixEnd_763114 : Nat := 4983230072969 + 3 ^ 40 * 763114 * 2
def baseEnd_763114 : Nat := 391844276175232546665509

theorem tailTrace_763114 : CollatzResearch.WordTrace tailWord_763114 prefixEnd_763114 391844276175232546665509 := by
  unfold tailWord_763114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958263539343945585062099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18555369438250521560165597 6958263539343945585062099)
  ·
    refine ⟨10437395309015918377593149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6958263539343945585062099 10437395309015918377593149)
    ·
      refine ⟨3914023240880969391597431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10437395309015918377593149 3914023240880969391597431)
      ·
        refine ⟨5871034861321454087396147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914023240880969391597431 5871034861321454087396147)
        ·
          refine ⟨8806552291982181131094221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871034861321454087396147 8806552291982181131094221)
          ·
            refine ⟨3302457109493317924160333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8806552291982181131094221 3302457109493317924160333)
            ·
              refine ⟨1238421416059994221560125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3302457109493317924160333 1238421416059994221560125)
              ·
                refine ⟨464408031022497833085047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1238421416059994221560125 464408031022497833085047)
                ·
                  refine ⟨696612046533746749627571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464408031022497833085047 696612046533746749627571)
                  ·
                    refine ⟨1044918069800620124441357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 696612046533746749627571 1044918069800620124441357)
                    ·
                      refine ⟨391844276175232546665509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1044918069800620124441357 391844276175232546665509)
                      ·
                        rfl

theorem cell23_763114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_763114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763114 prefixEnd_763114 := by exact prefixLift 763114
  have htrace : WordTrace (prefixWord ++ tailWord_763114) baseStart_763114 baseEnd_763114 := by
    simpa [prefixWord, tailWord_763114, baseEnd_763114] using wordTrace_append hprefix tailTrace_763114
  have hstable : (prefixWord ++ tailWord_763114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763114).length < 2 ^ (prefixWord ++ tailWord_763114).sum := by decide
  have hdescent : baseEnd_763114 < baseStart_763114 := by decide
  rcases family_descends (prefixWord ++ tailWord_763114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763123 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 5]
def baseStart_763123 : Nat := 118140960795 + 763123 * 2 ^ 59
def prefixEnd_763123 : Nat := 4983230072969 + 3 ^ 40 * 763123 * 2
def baseEnd_763123 : Nat := 391848897501123011452967

theorem tailTrace_763123 : CollatzResearch.WordTrace tailWord_763123 prefixEnd_763123 391848897501123011452967 := by
  unfold tailWord_763123
  simp only [CollatzResearch.WordTrace]
  refine ⟨27833382414343176877326023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18555588276228784584884015 27833382414343176877326023)
  ·
    refine ⟨41750073621514765315989035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27833382414343176877326023 41750073621514765315989035)
    ·
      refine ⟨62625110432272147973983553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41750073621514765315989035 62625110432272147973983553)
      ·
        refine ⟨46968832824204110980487665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62625110432272147973983553 46968832824204110980487665)
        ·
          refine ⟨35226624618153083235365749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46968832824204110980487665 35226624618153083235365749)
          ·
            refine ⟨3302496057951851553315539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35226624618153083235365749 3302496057951851553315539)
            ·
              refine ⟨4953744086927777329973309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302496057951851553315539 4953744086927777329973309)
              ·
                refine ⟨1857654032597916498739991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4953744086927777329973309 1857654032597916498739991)
                ·
                  refine ⟨2786481048896874748109987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857654032597916498739991 2786481048896874748109987)
                  ·
                    refine ⟨4179721573345312122164981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2786481048896874748109987 4179721573345312122164981)
                    ·
                      refine ⟨391848897501123011452967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4179721573345312122164981 391848897501123011452967)
                      ·
                        rfl

theorem cell23_763123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_763123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763123 prefixEnd_763123 := by exact prefixLift 763123
  have htrace : WordTrace (prefixWord ++ tailWord_763123) baseStart_763123 baseEnd_763123 := by
    simpa [prefixWord, tailWord_763123, baseEnd_763123] using wordTrace_append hprefix tailTrace_763123
  have hstable : (prefixWord ++ tailWord_763123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763123).length < 2 ^ (prefixWord ++ tailWord_763123).sum := by decide
  have hdescent : baseEnd_763123 < baseStart_763123 := by decide
  rcases family_descends (prefixWord ++ tailWord_763123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763130 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_763130 : Nat := 118140960795 + 763130 * 2 ^ 59
def prefixEnd_763130 : Nat := 4983230072969 + 3 ^ 40 * 763130 * 2
def baseEnd_763130 : Nat := 130617497288568161355145

theorem tailTrace_763130 : CollatzResearch.WordTrace tailWord_763130 prefixEnd_763130 130617497288568161355145 := by
  unfold tailWord_763130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958409431329454268207711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18555758483545211381887229 6958409431329454268207711)
  ·
    refine ⟨10437614146994181402311567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6958409431329454268207711 10437614146994181402311567)
    ·
      refine ⟨15656421220491272103467351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10437614146994181402311567 15656421220491272103467351)
      ·
        refine ⟨23484631830736908155201027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15656421220491272103467351 23484631830736908155201027)
        ·
          refine ⟨35226947746105362232801541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23484631830736908155201027 35226947746105362232801541)
          ·
            refine ⟨6605052702394755418650289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35226947746105362232801541 6605052702394755418650289)
            ·
              refine ⟨4953789526796066563987717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6605052702394755418650289 4953789526796066563987717)
              ·
                refine ⟨928835536274262480747697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4953789526796066563987717 928835536274262480747697)
                ·
                  refine ⟨696626652205696860560773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928835536274262480747697 696626652205696860560773)
                  ·
                    refine ⟨130617497288568161355145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696626652205696860560773 130617497288568161355145)
                    ·
                      rfl

theorem cell23_763130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_763130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763130 prefixEnd_763130 := by exact prefixLift 763130
  have htrace : WordTrace (prefixWord ++ tailWord_763130) baseStart_763130 baseEnd_763130 := by
    simpa [prefixWord, tailWord_763130, baseEnd_763130] using wordTrace_append hprefix tailTrace_763130
  have hstable : (prefixWord ++ tailWord_763130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763130).length < 2 ^ (prefixWord ++ tailWord_763130).sum := by decide
  have hdescent : baseEnd_763130 < baseStart_763130 := by decide
  rcases family_descends (prefixWord ++ tailWord_763130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763140 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_763140 : Nat := 118140960795 + 763140 * 2 ^ 59
def prefixEnd_763140 : Nat := 4983230072969 + 3 ^ 40 * 763140 * 2
def baseEnd_763140 : Nat := 391857626672249444940389

theorem tailTrace_763140 : CollatzResearch.WordTrace tailWord_763140 prefixEnd_763140 391857626672249444940389 := by
  unfold tailWord_763140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917001227640794390347437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18556001636854392520463249 13917001227640794390347437)
  ·
    refine ⟨5218875460365297896380289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13917001227640794390347437 5218875460365297896380289)
    ·
      refine ⟨3914156595273973422285217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5218875460365297896380289 3914156595273973422285217)
      ·
        refine ⟨2935617446455480066713913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3914156595273973422285217 2935617446455480066713913)
        ·
          refine ⟨2201713084841610050035435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2935617446455480066713913 2201713084841610050035435)
          ·
            refine ⟨3302569627262415075053153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201713084841610050035435 3302569627262415075053153)
            ·
              refine ⟨2476927220446811306289865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3302569627262415075053153 2476927220446811306289865)
              ·
                refine ⟨1857695415335108479717399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2476927220446811306289865 1857695415335108479717399)
                ·
                  refine ⟨2786543123002662719576099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857695415335108479717399 2786543123002662719576099)
                  ·
                    refine ⟨4179814684503994079364149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2786543123002662719576099 4179814684503994079364149)
                    ·
                      refine ⟨391857626672249444940389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4179814684503994079364149 391857626672249444940389)
                      ·
                        rfl

theorem cell23_763140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_763140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763140 prefixEnd_763140 := by exact prefixLift 763140
  have htrace : WordTrace (prefixWord ++ tailWord_763140) baseStart_763140 baseEnd_763140 := by
    simpa [prefixWord, tailWord_763140, baseEnd_763140] using wordTrace_append hprefix tailTrace_763140
  have hstable : (prefixWord ++ tailWord_763140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763140).length < 2 ^ (prefixWord ++ tailWord_763140).sum := by decide
  have hdescent : baseEnd_763140 < baseStart_763140 := by decide
  rcases family_descends (prefixWord ++ tailWord_763140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763147 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 2, 4]
def baseStart_763147 : Nat := 118140960795 + 763147 * 2 ^ 59
def prefixEnd_763147 : Nat := 4983230072969 + 3 ^ 40 * 763147 * 2
def baseEnd_763147 : Nat := 130620407012276972517619

theorem tailTrace_763147 : CollatzResearch.WordTrace tailWord_763147 prefixEnd_763147 130620407012276972517619 := by
  unfold tailWord_763147
  simp only [CollatzResearch.WordTrace]
  refine ⟨27834257766256228976199695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18556171844170819317466463 27834257766256228976199695)
  ·
    refine ⟨41751386649384343464299543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27834257766256228976199695 41751386649384343464299543)
    ·
      refine ⟨62627079974076515196449315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41751386649384343464299543 62627079974076515196449315)
      ·
        refine ⟨93940619961114772794673973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62627079974076515196449315 93940619961114772794673973)
        ·
          refine ⟨8806933121354509949500685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93940619961114772794673973 8806933121354509949500685)
          ·
            refine ⟨3302599920507941231062757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8806933121354509949500685 3302599920507941231062757)
            ·
              refine ⟨619237485095238980824267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3302599920507941231062757 619237485095238980824267)
              ·
                refine ⟨928856227642858471236401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619237485095238980824267 928856227642858471236401)
                ·
                  refine ⟨696642170732143853427301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928856227642858471236401 696642170732143853427301)
                  ·
                    refine ⟨130620407012276972517619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696642170732143853427301 130620407012276972517619)
                    ·
                      rfl

theorem cell23_763147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 4].length) (baseStart_763147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763147 prefixEnd_763147 := by exact prefixLift 763147
  have htrace : WordTrace (prefixWord ++ tailWord_763147) baseStart_763147 baseEnd_763147 := by
    simpa [prefixWord, tailWord_763147, baseEnd_763147] using wordTrace_append hprefix tailTrace_763147
  have hstable : (prefixWord ++ tailWord_763147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763147).length < 2 ^ (prefixWord ++ tailWord_763147).sum := by decide
  have hdescent : baseEnd_763147 < baseStart_763147 := by decide
  rcases family_descends (prefixWord ++ tailWord_763147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763154 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_763154 : Nat := 118140960795 + 763154 * 2 ^ 59
def prefixEnd_763154 : Nat := 4983230072969 + 3 ^ 40 * 763154 * 2
def baseEnd_763154 : Nat := 391864815401412390165325

theorem tailTrace_763154 : CollatzResearch.WordTrace tailWord_763154 prefixEnd_763154 391864815401412390165325 := by
  unfold tailWord_763154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958628269307717292926129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18556342051487246114469677 6958628269307717292926129)
  ·
    refine ⟨5218971201980787969694597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6958628269307717292926129 5218971201980787969694597)
    ·
      refine ⟨978557100371397744317737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5218971201980787969694597 978557100371397744317737)
      ·
        refine ⟨733917825278548308238303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 978557100371397744317737 733917825278548308238303)
        ·
          refine ⟨1100876737917822462357455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733917825278548308238303 1100876737917822462357455)
          ·
            refine ⟨1651315106876733693536183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100876737917822462357455 1651315106876733693536183)
            ·
              refine ⟨2476972660315100540304275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651315106876733693536183 2476972660315100540304275)
              ·
                refine ⟨3715458990472650810456413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476972660315100540304275 3715458990472650810456413)
                ·
                  refine ⟨1393297121427244053921155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3715458990472650810456413 1393297121427244053921155)
                  ·
                    refine ⟨2089945682140866080881733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1393297121427244053921155 2089945682140866080881733)
                    ·
                      refine ⟨391864815401412390165325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2089945682140866080881733 391864815401412390165325)
                      ·
                        rfl

theorem cell23_763154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_763154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763154 prefixEnd_763154 := by exact prefixLift 763154
  have htrace : WordTrace (prefixWord ++ tailWord_763154) baseStart_763154 baseEnd_763154 := by
    simpa [prefixWord, tailWord_763154, baseEnd_763154] using wordTrace_append hprefix tailTrace_763154
  have hstable : (prefixWord ++ tailWord_763154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763154).length < 2 ^ (prefixWord ++ tailWord_763154).sum := by decide
  have hdescent : baseEnd_763154 < baseStart_763154 := by decide
  rcases family_descends (prefixWord ++ tailWord_763154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763187 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 3]
def baseStart_763187 : Nat := 118140960795 + 763187 * 2 ^ 59
def prefixEnd_763187 : Nat := 4983230072969 + 3 ^ 40 * 763187 * 2
def baseEnd_763187 : Nat := 391881760263010761052673

theorem tailTrace_763187 : CollatzResearch.WordTrace tailWord_763187 prefixEnd_763187 391881760263010761052673 := by
  unfold tailWord_763187
  simp only [CollatzResearch.WordTrace]
  refine ⟨27835716686111315807655815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18557144457407543871770543 27835716686111315807655815)
  ·
    refine ⟨41753575029166973711483723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27835716686111315807655815 41753575029166973711483723)
    ·
      refine ⟨62630362543750460567225585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41753575029166973711483723 62630362543750460567225585)
      ·
        refine ⟨46972771907812845425419189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62630362543750460567225585 46972771907812845425419189)
        ·
          refine ⟨4403697366357454258633049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46972771907812845425419189 4403697366357454258633049)
          ·
            refine ⟨3302773024768090693974787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4403697366357454258633049 3302773024768090693974787)
            ·
              refine ⟨4954159537152136040962181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302773024768090693974787 4954159537152136040962181)
              ·
                refine ⟨928904913216025507680409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4954159537152136040962181 928904913216025507680409)
                ·
                  refine ⟨696678684912019130760307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928904913216025507680409 696678684912019130760307)
                  ·
                    refine ⟨1045018027368028696140461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 696678684912019130760307 1045018027368028696140461)
                    ·
                      refine ⟨391881760263010761052673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1045018027368028696140461 391881760263010761052673)
                      ·
                        rfl

theorem cell23_763187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 3].length) (baseStart_763187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763187 prefixEnd_763187 := by exact prefixLift 763187
  have htrace : WordTrace (prefixWord ++ tailWord_763187) baseStart_763187 baseEnd_763187 := by
    simpa [prefixWord, tailWord_763187, baseEnd_763187] using wordTrace_append hprefix tailTrace_763187
  have hstable : (prefixWord ++ tailWord_763187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763187).length < 2 ^ (prefixWord ++ tailWord_763187).sum := by decide
  have hdescent : baseEnd_763187 < baseStart_763187 := by decide
  rcases family_descends (prefixWord ++ tailWord_763187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763204 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_763204 : Nat := 118140960795 + 763204 * 2 ^ 59
def prefixEnd_763204 : Nat := 4983230072969 + 3 ^ 40 * 763204 * 2
def baseEnd_763204 : Nat := 391890489434137194540095

theorem tailTrace_763204 : CollatzResearch.WordTrace tailWord_763204 prefixEnd_763204 391890489434137194540095 := by
  unfold tailWord_763204
  simp only [CollatzResearch.WordTrace]
  refine ⟨13918168363524863855512333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18557557818033151807349777 13918168363524863855512333)
  ·
    refine ⟨5219313136321823945817125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13918168363524863855512333 5219313136321823945817125)
    ·
      refine ⟨978621213060341989840711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5219313136321823945817125 978621213060341989840711)
      ·
        refine ⟨1467931819590512984761067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978621213060341989840711 1467931819590512984761067)
        ·
          refine ⟨2201897729385769477141601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467931819590512984761067 2201897729385769477141601)
          ·
            refine ⟨1651423297039327107856201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2201897729385769477141601 1651423297039327107856201)
            ·
              refine ⟨1238567472779495330892151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1651423297039327107856201 1238567472779495330892151)
              ·
                refine ⟨1857851209169242996338227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238567472779495330892151 1857851209169242996338227)
                ·
                  refine ⟨2786776813753864494507341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857851209169242996338227 2786776813753864494507341)
                  ·
                    refine ⟨1045041305157699185440253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786776813753864494507341 1045041305157699185440253)
                    ·
                      refine ⟨391890489434137194540095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1045041305157699185440253 391890489434137194540095)
                      ·
                        rfl

theorem cell23_763204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_763204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763204 prefixEnd_763204 := by exact prefixLift 763204
  have htrace : WordTrace (prefixWord ++ tailWord_763204) baseStart_763204 baseEnd_763204 := by
    simpa [prefixWord, tailWord_763204, baseEnd_763204] using wordTrace_append hprefix tailTrace_763204
  have hstable : (prefixWord ++ tailWord_763204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763204).length < 2 ^ (prefixWord ++ tailWord_763204).sum := by decide
  have hdescent : baseEnd_763204 < baseStart_763204 := by decide
  rcases family_descends (prefixWord ++ tailWord_763204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763222 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_763222 : Nat := 118140960795 + 763222 * 2 ^ 59
def prefixEnd_763222 : Nat := 4983230072969 + 3 ^ 40 * 763222 * 2
def baseEnd_763222 : Nat := 391899732085918124115013

theorem tailTrace_763222 : CollatzResearch.WordTrace tailWord_763222 prefixEnd_763222 391899732085918124115013 := by
  unfold tailWord_763222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739812077561532299073745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18557995493989677856786613 1739812077561532299073745)
  ·
    refine ⟨1304859058171149224305309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1739812077561532299073745 1304859058171149224305309)
    ·
      refine ⟨489322146814180959114491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1304859058171149224305309 489322146814180959114491)
      ·
        refine ⟨733983220221271438671737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489322146814180959114491 733983220221271438671737)
        ·
          refine ⟨550487415165953579003803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733983220221271438671737 550487415165953579003803)
          ·
            refine ⟨825731122748930368505705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550487415165953579003803 825731122748930368505705)
            ·
              refine ⟨619298342061697776379279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825731122748930368505705 619298342061697776379279)
              ·
                refine ⟨928947513092546664568919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619298342061697776379279 928947513092546664568919)
                ·
                  refine ⟨1393421269638819996853379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928947513092546664568919 1393421269638819996853379)
                  ·
                    refine ⟨2090131904458229995280069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1393421269638819996853379 2090131904458229995280069)
                    ·
                      refine ⟨391899732085918124115013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2090131904458229995280069 391899732085918124115013)
                      ·
                        rfl

theorem cell23_763222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_763222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763222 prefixEnd_763222 := by exact prefixLift 763222
  have htrace : WordTrace (prefixWord ++ tailWord_763222) baseStart_763222 baseEnd_763222 := by
    simpa [prefixWord, tailWord_763222, baseEnd_763222] using wordTrace_append hprefix tailTrace_763222
  have hstable : (prefixWord ++ tailWord_763222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763222).length < 2 ^ (prefixWord ++ tailWord_763222).sum := by decide
  have hdescent : baseEnd_763222 < baseStart_763222 := by decide
  rcases family_descends (prefixWord ++ tailWord_763222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763244 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 4, 2, 2]
def baseStart_763244 : Nat := 118140960795 + 763244 * 2 ^ 59
def prefixEnd_763244 : Nat := 4983230072969 + 3 ^ 40 * 763244 * 2
def baseEnd_763244 : Nat := 391911028660317038039911

theorem tailTrace_763244 : CollatzResearch.WordTrace tailWord_763244 prefixEnd_763244 391911028660317038039911 := by
  unfold tailWord_763244
  simp only [CollatzResearch.WordTrace]
  refine ⟨13918897823452407271240393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18558530431269876361653857 13918897823452407271240393)
  ·
    refine ⟨10439173367589305453430295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13918897823452407271240393 10439173367589305453430295)
    ·
      refine ⟨15658760051383958180145443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10439173367589305453430295 15658760051383958180145443)
      ·
        refine ⟨23488140077075937270218165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15658760051383958180145443 23488140077075937270218165)
        ·
          refine ⟨2202013132225869119082953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23488140077075937270218165 2202013132225869119082953)
          ·
            refine ⟨1651509849169401839312215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202013132225869119082953 1651509849169401839312215)
            ·
              refine ⟨2477264773754102758968323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651509849169401839312215 2477264773754102758968323)
              ·
                refine ⟨3715897160631154138452485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477264773754102758968323 3715897160631154138452485)
                ·
                  refine ⟨696730717618341400959841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3715897160631154138452485 696730717618341400959841)
                  ·
                    refine ⟨522548038213756050719881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 696730717618341400959841 522548038213756050719881)
                    ·
                      refine ⟨391911028660317038039911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522548038213756050719881 391911028660317038039911)
                      ·
                        rfl

theorem cell23_763244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_763244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763244 prefixEnd_763244 := by exact prefixLift 763244
  have htrace : WordTrace (prefixWord ++ tailWord_763244) baseStart_763244 baseEnd_763244 := by
    simpa [prefixWord, tailWord_763244, baseEnd_763244] using wordTrace_append hprefix tailTrace_763244
  have hstable : (prefixWord ++ tailWord_763244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763244).length < 2 ^ (prefixWord ++ tailWord_763244).sum := by decide
  have hdescent : baseEnd_763244 < baseStart_763244 := by decide
  rcases family_descends (prefixWord ++ tailWord_763244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763250 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 7]
def baseStart_763250 : Nat := 118140960795 + 763250 * 2 ^ 59
def prefixEnd_763250 : Nat := 4983230072969 + 3 ^ 40 * 763250 * 2
def baseEnd_763250 : Nat := 43546012171582668284987

theorem tailTrace_763250 : CollatzResearch.WordTrace tailWord_763250 prefixEnd_763250 43546012171582668284987 := by
  unfold tailWord_763250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6959503621220769391799801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18558676323255385044799469 6959503621220769391799801)
  ·
    refine ⟨5219627715915577043849851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6959503621220769391799801 5219627715915577043849851)
    ·
      refine ⟨7829441573873365565774777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219627715915577043849851 7829441573873365565774777)
      ·
        refine ⟨5872081180405024174331083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7829441573873365565774777 5872081180405024174331083)
        ·
          refine ⟨8808121770607536261496625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5872081180405024174331083 8808121770607536261496625)
          ·
            refine ⟨6606091327955652196122469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8808121770607536261496625 6606091327955652196122469)
            ·
              refine ⟨1238642123991684786772963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6606091327955652196122469 1238642123991684786772963)
              ·
                refine ⟨1857963185987527180159445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238642123991684786772963 1857963185987527180159445)
                ·
                  refine ⟨43546012171582668284987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1857963185987527180159445 43546012171582668284987)
                  ·
                    rfl

theorem cell23_763250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_763250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763250 prefixEnd_763250 := by exact prefixLift 763250
  have htrace : WordTrace (prefixWord ++ tailWord_763250) baseStart_763250 baseEnd_763250 := by
    simpa [prefixWord, tailWord_763250, baseEnd_763250] using wordTrace_append hprefix tailTrace_763250
  have hstable : (prefixWord ++ tailWord_763250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763250).length < 2 ^ (prefixWord ++ tailWord_763250).sum := by decide
  have hdescent : baseEnd_763250 < baseStart_763250 := by decide
  rcases family_descends (prefixWord ++ tailWord_763250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763260 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_763260 : Nat := 118140960795 + 763260 * 2 ^ 59
def prefixEnd_763260 : Nat := 4983230072969 + 3 ^ 40 * 763260 * 2
def baseEnd_763260 : Nat := 391919244350788975439837

theorem tailTrace_763260 : CollatzResearch.WordTrace tailWord_763260 prefixEnd_763260 391919244350788975439837 := by
  unfold tailWord_763260
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919189607423424637531617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18558919476564566183375489 13919189607423424637531617)
  ·
    refine ⟨10439392205567568478148713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13919189607423424637531617 10439392205567568478148713)
    ·
      refine ⟨7829544154175676358611535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10439392205567568478148713 7829544154175676358611535)
      ·
        refine ⟨11744316231263514537917303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7829544154175676358611535 11744316231263514537917303)
        ·
          refine ⟨17616474346895271806875955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11744316231263514537917303 17616474346895271806875955)
          ·
            refine ⟨26424711520342907710313933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17616474346895271806875955 26424711520342907710313933)
            ·
              refine ⟨9909266820128590391367725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26424711520342907710313933 9909266820128590391367725)
              ·
                refine ⟨3715975057548221396762897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9909266820128590391367725 3715975057548221396762897)
                ·
                  refine ⟨2786981293161166047572173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3715975057548221396762897 2786981293161166047572173)
                  ·
                    refine ⟨1045117984935437267839565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786981293161166047572173 1045117984935437267839565)
                    ·
                      refine ⟨391919244350788975439837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1045117984935437267839565 391919244350788975439837)
                      ·
                        rfl

theorem cell23_763260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_763260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763260 prefixEnd_763260 := by exact prefixLift 763260
  have htrace : WordTrace (prefixWord ++ tailWord_763260) baseStart_763260 baseEnd_763260 := by
    simpa [prefixWord, tailWord_763260, baseEnd_763260] using wordTrace_append hprefix tailTrace_763260
  have hstable : (prefixWord ++ tailWord_763260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763260).length < 2 ^ (prefixWord ++ tailWord_763260).sum := by decide
  have hdescent : baseEnd_763260 < baseStart_763260 := by decide
  rcases family_descends (prefixWord ++ tailWord_763260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763261 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_763261 : Nat := 118140960795 + 763261 * 2 ^ 59
def prefixEnd_763261 : Nat := 4983230072969 + 3 ^ 40 * 763261 * 2
def baseEnd_763261 : Nat := 391919757831443471527333

theorem tailTrace_763261 : CollatzResearch.WordTrace tailWord_763261 prefixEnd_763261 391919757831443471527333 := by
  unfold tailWord_763261
  simp only [CollatzResearch.WordTrace]
  refine ⟨27838415687843226445849637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18558943791895484297233091 27838415687843226445849637)
  ·
    refine ⟨5219702941470604958596807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27838415687843226445849637 5219702941470604958596807)
    ·
      refine ⟨7829554412205907437895211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219702941470604958596807 7829554412205907437895211)
      ·
        refine ⟨11744331618308861156842817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7829554412205907437895211 11744331618308861156842817)
        ·
          refine ⟨8808248713731645867632113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11744331618308861156842817 8808248713731645867632113)
          ·
            refine ⟨6606186535298734400724085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8808248713731645867632113 6606186535298734400724085)
            ·
              refine ⟨619329987684256350067883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6606186535298734400724085 619329987684256350067883)
              ·
                refine ⟨928994981526384525101825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619329987684256350067883 928994981526384525101825)
                ·
                  refine ⟨696746236144788393826369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928994981526384525101825 696746236144788393826369)
                  ·
                    refine ⟨522559677108591295369777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 696746236144788393826369 522559677108591295369777)
                    ·
                      refine ⟨391919757831443471527333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522559677108591295369777 391919757831443471527333)
                      ·
                        rfl

theorem cell23_763261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_763261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763261 prefixEnd_763261 := by exact prefixLift 763261
  have htrace : WordTrace (prefixWord ++ tailWord_763261) baseStart_763261 baseEnd_763261 := by
    simpa [prefixWord, tailWord_763261, baseEnd_763261] using wordTrace_append hprefix tailTrace_763261
  have hstable : (prefixWord ++ tailWord_763261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763261).length < 2 ^ (prefixWord ++ tailWord_763261).sum := by decide
  have hdescent : baseEnd_763261 < baseStart_763261 := by decide
  rcases family_descends (prefixWord ++ tailWord_763261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763284 : List Nat := [2, 4, 2, 1, 2, 1, 3, 3, 5]
def baseStart_763284 : Nat := 118140960795 + 763284 * 2 ^ 59
def prefixEnd_763284 : Nat := 4983230072969 + 3 ^ 40 * 763284 * 2
def baseEnd_763284 : Nat := 43547951987388542393303

theorem tailTrace_763284 : CollatzResearch.WordTrace tailWord_763284 prefixEnd_763284 43547951987388542393303 := by
  unfold tailWord_763284
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919627283379950686968453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18559503044506600915957937 13919627283379950686968453)
  ·
    refine ⟨2609930115633740753806585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13919627283379950686968453 2609930115633740753806585)
    ·
      refine ⟨1957447586725305565354939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2609930115633740753806585 1957447586725305565354939)
      ·
        refine ⟨2936171380087958348032409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957447586725305565354939 2936171380087958348032409)
        ·
          refine ⟨2202128535065968761024307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2936171380087958348032409 2202128535065968761024307)
          ·
            refine ⟨3303192802598953141536461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202128535065968761024307 3303192802598953141536461)
            ·
              refine ⟨1238697300974607428076173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3303192802598953141536461 1238697300974607428076173)
              ·
                refine ⟨464511487865477785528565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1238697300974607428076173 464511487865477785528565)
                ·
                  refine ⟨43547951987388542393303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 464511487865477785528565 43547951987388542393303)
                  ·
                    rfl

theorem cell23_763284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_763284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763284 prefixEnd_763284 := by exact prefixLift 763284
  have htrace : WordTrace (prefixWord ++ tailWord_763284) baseStart_763284 baseEnd_763284 := by
    simpa [prefixWord, tailWord_763284, baseEnd_763284] using wordTrace_append hprefix tailTrace_763284
  have hstable : (prefixWord ++ tailWord_763284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763284).length < 2 ^ (prefixWord ++ tailWord_763284).sum := by decide
  have hdescent : baseEnd_763284 < baseStart_763284 := by decide
  rcases family_descends (prefixWord ++ tailWord_763284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763290 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_763290 : Nat := 118140960795 + 763290 * 2 ^ 59
def prefixEnd_763290 : Nat := 4983230072969 + 3 ^ 40 * 763290 * 2
def baseEnd_763290 : Nat := 391934648770423858064699

theorem tailTrace_763290 : CollatzResearch.WordTrace tailWord_763290 prefixEnd_763290 391934648770423858064699 := by
  unfold tailWord_763290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6959868351184541099663831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18559648936492109599103549 6959868351184541099663831)
  ·
    refine ⟨10439802526776811649495747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6959868351184541099663831 10439802526776811649495747)
    ·
      refine ⟨15659703790165217474243621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10439802526776811649495747 15659703790165217474243621)
      ·
        refine ⟨2936194460655978276420679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15659703790165217474243621 2936194460655978276420679)
        ·
          refine ⟨4404291690983967414631019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936194460655978276420679 4404291690983967414631019)
          ·
            refine ⟨6606437536475951121946529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404291690983967414631019 6606437536475951121946529)
            ·
              refine ⟨4954828152356963341459897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6606437536475951121946529 4954828152356963341459897)
              ·
                refine ⟨3716121114267722506094923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4954828152356963341459897 3716121114267722506094923)
                ·
                  refine ⟨5574181671401583759142385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716121114267722506094923 5574181671401583759142385)
                  ·
                    refine ⟨4180636253551187819356789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5574181671401583759142385 4180636253551187819356789)
                    ·
                      refine ⟨391934648770423858064699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4180636253551187819356789 391934648770423858064699)
                      ·
                        rfl

theorem cell23_763290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_763290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763290 prefixEnd_763290 := by exact prefixLift 763290
  have htrace : WordTrace (prefixWord ++ tailWord_763290) baseStart_763290 baseEnd_763290 := by
    simpa [prefixWord, tailWord_763290, baseEnd_763290] using wordTrace_append hprefix tailTrace_763290
  have hstable : (prefixWord ++ tailWord_763290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763290).length < 2 ^ (prefixWord ++ tailWord_763290).sum := by decide
  have hdescent : baseEnd_763290 < baseStart_763290 := by decide
  rcases family_descends (prefixWord ++ tailWord_763290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763320 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_763320 : Nat := 118140960795 + 763320 * 2 ^ 59
def prefixEnd_763320 : Nat := 4983230072969 + 3 ^ 40 * 763320 * 2
def baseEnd_763320 : Nat := 391950053190058740689561

theorem tailTrace_763320 : CollatzResearch.WordTrace tailWord_763320 prefixEnd_763320 391950053190058740689561 := by
  unfold tailWord_763320
  simp only [CollatzResearch.WordTrace]
  refine ⟨13920283797314739761123707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18560378396419653014831609 13920283797314739761123707)
  ·
    refine ⟨20880425695972109641685561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13920283797314739761123707 20880425695972109641685561)
    ·
      refine ⟨15660319271979082231264171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20880425695972109641685561 15660319271979082231264171)
      ·
        refine ⟨23490478907968623346896257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15660319271979082231264171 23490478907968623346896257)
        ·
          refine ⟨17617859180976467510172193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23490478907968623346896257 17617859180976467510172193)
          ·
            refine ⟨13213394385732350632629145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17617859180976467510172193 13213394385732350632629145)
            ·
              refine ⟨9910045789299262974471859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13213394385732350632629145 9910045789299262974471859)
              ·
                refine ⟨14865068683948894461707789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9910045789299262974471859 14865068683948894461707789)
                ·
                  refine ⟨5574400756480835423140421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14865068683948894461707789 5574400756480835423140421)
                  ·
                    refine ⟨1045200141840156641838829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5574400756480835423140421 1045200141840156641838829)
                    ·
                      refine ⟨391950053190058740689561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1045200141840156641838829 391950053190058740689561)
                      ·
                        rfl

theorem cell23_763320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_763320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763320 prefixEnd_763320 := by exact prefixLift 763320
  have htrace : WordTrace (prefixWord ++ tailWord_763320) baseStart_763320 baseEnd_763320 := by
    simpa [prefixWord, tailWord_763320, baseEnd_763320] using wordTrace_append hprefix tailTrace_763320
  have hstable : (prefixWord ++ tailWord_763320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763320).length < 2 ^ (prefixWord ++ tailWord_763320).sum := by decide
  have hdescent : baseEnd_763320 < baseStart_763320 := by decide
  rcases family_descends (prefixWord ++ tailWord_763320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763357 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 6]
def baseStart_763357 : Nat := 118140960795 + 763357 * 2 ^ 59
def prefixEnd_763357 : Nat := 4983230072969 + 3 ^ 40 * 763357 * 2
def baseEnd_763357 : Nat := 43552116886030566214099

theorem tailTrace_763357 : CollatzResearch.WordTrace tailWord_763357 prefixEnd_763357 43552116886030566214099 := by
  unfold tailWord_763357
  simp only [CollatzResearch.WordTrace]
  refine ⟨27841917095495434841344325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18561278063663623227562883 27841917095495434841344325)
  ·
    refine ⟨5220359455405394032752061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27841917095495434841344325 5220359455405394032752061)
    ·
      refine ⟨1957634795777022762282023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5220359455405394032752061 1957634795777022762282023)
      ·
        refine ⟨2936452193665534143423035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957634795777022762282023 2936452193665534143423035)
        ·
          refine ⟨4404678290498301215134553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936452193665534143423035 4404678290498301215134553)
          ·
            refine ⟨3303508717873725911350915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4404678290498301215134553 3303508717873725911350915)
            ·
              refine ⟨4955263076810588867026373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303508717873725911350915 4955263076810588867026373)
              ·
                refine ⟨929111826901985412567445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4955263076810588867026373 929111826901985412567445)
                ·
                  refine ⟨43552116886030566214099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 929111826901985412567445 43552116886030566214099)
                  ·
                    rfl

theorem cell23_763357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_763357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763357 prefixEnd_763357 := by exact prefixLift 763357
  have htrace : WordTrace (prefixWord ++ tailWord_763357) baseStart_763357 baseEnd_763357 := by
    simpa [prefixWord, tailWord_763357, baseEnd_763357] using wordTrace_append hprefix tailTrace_763357
  have hstable : (prefixWord ++ tailWord_763357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763357).length < 2 ^ (prefixWord ++ tailWord_763357).sum := by decide
  have hdescent : baseEnd_763357 < baseStart_763357 := by decide
  rcases family_descends (prefixWord ++ tailWord_763357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763361 : List Nat := [1, 2, 3, 1, 2, 3, 4, 2, 1, 4]
def baseStart_763361 : Nat := 118140960795 + 763361 * 2 ^ 59
def prefixEnd_763361 : Nat := 4983230072969 + 3 ^ 40 * 763361 * 2
def baseEnd_763361 : Nat := 130657035298964360092291

theorem tailTrace_763361 : CollatzResearch.WordTrace tailWord_763361 prefixEnd_763361 130657035298964360092291 := by
  unfold tailWord_763361
  simp only [CollatzResearch.WordTrace]
  refine ⟨27842062987480943524489937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18561375324987295682993291 27842062987480943524489937)
  ·
    refine ⟨20881547240610707643367453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27842062987480943524489937 20881547240610707643367453)
    ·
      refine ⟨7830580215229015366262795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20881547240610707643367453 7830580215229015366262795)
      ·
        refine ⟨11745870322843523049394193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7830580215229015366262795 11745870322843523049394193)
        ·
          refine ⟨8809402742132642287045645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11745870322843523049394193 8809402742132642287045645)
          ·
            refine ⟨3303526028299740857642117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8809402742132642287045645 3303526028299740857642117)
            ·
              refine ⟨619411130306201410807897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3303526028299740857642117 619411130306201410807897)
              ·
                refine ⟨464558347729651058105923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619411130306201410807897 464558347729651058105923)
                ·
                  refine ⟨696837521594476587158885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464558347729651058105923 696837521594476587158885)
                  ·
                    refine ⟨130657035298964360092291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696837521594476587158885 130657035298964360092291)
                    ·
                      rfl

theorem cell23_763361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_763361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763361 prefixEnd_763361 := by exact prefixLift 763361
  have htrace : WordTrace (prefixWord ++ tailWord_763361) baseStart_763361 baseEnd_763361 := by
    simpa [prefixWord, tailWord_763361, baseEnd_763361] using wordTrace_append hprefix tailTrace_763361
  have hstable : (prefixWord ++ tailWord_763361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763361).length < 2 ^ (prefixWord ++ tailWord_763361).sum := by decide
  have hdescent : baseEnd_763361 < baseStart_763361 := by decide
  rcases family_descends (prefixWord ++ tailWord_763361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763384 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 3, 1, 3]
def baseStart_763384 : Nat := 118140960795 + 763384 * 2 ^ 59
def prefixEnd_763384 : Nat := 4983230072969 + 3 ^ 40 * 763384 * 2
def baseEnd_763384 : Nat := 391982915951946490289267

theorem tailTrace_763384 : CollatzResearch.WordTrace tailWord_763384 prefixEnd_763384 391982915951946490289267 := by
  unfold tailWord_763384
  simp only [CollatzResearch.WordTrace]
  refine ⟨13921450933198809226288603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18561934577598412301718137 13921450933198809226288603)
  ·
    refine ⟨20882176399798213839432905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13921450933198809226288603 20882176399798213839432905)
    ·
      refine ⟨15661632299848660379574679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20882176399798213839432905 15661632299848660379574679)
      ·
        refine ⟨23492448449772990569362019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15661632299848660379574679 23492448449772990569362019)
        ·
          refine ⟨35238672674659485854043029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23492448449772990569362019 35238672674659485854043029)
          ·
            refine ⟨1651812781624663399408267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35238672674659485854043029 1651812781624663399408267)
            ·
              refine ⟨2477719172436995099112401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651812781624663399408267 2477719172436995099112401)
              ·
                refine ⟨1858289379327746324334301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477719172436995099112401 1858289379327746324334301)
                ·
                  refine ⟨696858517247904871625363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1858289379327746324334301 696858517247904871625363)
                  ·
                    refine ⟨1045287775871857307438045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 696858517247904871625363 1045287775871857307438045)
                    ·
                      refine ⟨391982915951946490289267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1045287775871857307438045 391982915951946490289267)
                      ·
                        rfl

theorem cell23_763384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_763384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763384 prefixEnd_763384 := by exact prefixLift 763384
  have htrace : WordTrace (prefixWord ++ tailWord_763384) baseStart_763384 baseEnd_763384 := by
    simpa [prefixWord, tailWord_763384, baseEnd_763384] using wordTrace_append hprefix tailTrace_763384
  have hstable : (prefixWord ++ tailWord_763384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763384).length < 2 ^ (prefixWord ++ tailWord_763384).sum := by decide
  have hdescent : baseEnd_763384 < baseStart_763384 := by decide
  rcases family_descends (prefixWord ++ tailWord_763384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763401 : List Nat := [1, 2, 1, 1, 3, 1, 6, 3, 1, 1, 3]
def baseStart_763401 : Nat := 118140960795 + 763401 * 2 ^ 59
def prefixEnd_763401 : Nat := 4983230072969 + 3 ^ 40 * 763401 * 2
def baseEnd_763401 : Nat := 391991645123072923776689

theorem tailTrace_763401 : CollatzResearch.WordTrace tailWord_763401 prefixEnd_763401 391991645123072923776689 := by
  unfold tailWord_763401
  simp only [CollatzResearch.WordTrace]
  refine ⟨27843521907336030355946057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18562347938224020237297371 27843521907336030355946057)
  ·
    refine ⟨20882641430502022766959543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27843521907336030355946057 20882641430502022766959543)
    ·
      refine ⟨31323962145753034150439315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20882641430502022766959543 31323962145753034150439315)
      ·
        refine ⟨46985943218629551225658973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31323962145753034150439315 46985943218629551225658973)
        ·
          refine ⟨17619728706986081709622115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46985943218629551225658973 17619728706986081709622115)
          ·
            refine ⟨26429593060479122564433173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17619728706986081709622115 26429593060479122564433173)
            ·
              refine ⟨1238887174709958870207805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26429593060479122564433173 1238887174709958870207805)
              ·
                refine ⟨464582690516234576327927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1238887174709958870207805 464582690516234576327927)
                ·
                  refine ⟨696874035774351864491891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464582690516234576327927 696874035774351864491891)
                  ·
                    refine ⟨1045311053661527796737837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 696874035774351864491891 1045311053661527796737837)
                    ·
                      refine ⟨391991645123072923776689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1045311053661527796737837 391991645123072923776689)
                      ·
                        rfl

theorem cell23_763401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 1, 3].length) (baseStart_763401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763401 prefixEnd_763401 := by exact prefixLift 763401
  have htrace : WordTrace (prefixWord ++ tailWord_763401) baseStart_763401 baseEnd_763401 := by
    simpa [prefixWord, tailWord_763401, baseEnd_763401] using wordTrace_append hprefix tailTrace_763401
  have hstable : (prefixWord ++ tailWord_763401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763401).length < 2 ^ (prefixWord ++ tailWord_763401).sum := by decide
  have hdescent : baseEnd_763401 < baseStart_763401 := by decide
  rcases family_descends (prefixWord ++ tailWord_763401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763404 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_763404 : Nat := 118140960795 + 763404 * 2 ^ 59
def prefixEnd_763404 : Nat := 4983230072969 + 3 ^ 40 * 763404 * 2
def baseEnd_763404 : Nat := 130664395188345470679725

theorem tailTrace_763404 : CollatzResearch.WordTrace tailWord_763404 prefixEnd_763404 130664395188345470679725 := by
  unfold tailWord_763404
  simp only [CollatzResearch.WordTrace]
  refine ⟨13921815663162580934152633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18562420884216774578870177 13921815663162580934152633)
  ·
    refine ⟨10441361747371935700614475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13921815663162580934152633 10441361747371935700614475)
    ·
      refine ⟨15662042621057903550921713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10441361747371935700614475 15662042621057903550921713)
      ·
        refine ⟨11746531965793427663191285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15662042621057903550921713 11746531965793427663191285)
        ·
          refine ⟨1101237371793133843424183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11746531965793427663191285 1101237371793133843424183)
          ·
            refine ⟨1651856057689700765136275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101237371793133843424183 1651856057689700765136275)
            ·
              refine ⟨2477784086534551147704413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651856057689700765136275 2477784086534551147704413)
              ·
                refine ⟨929169032450456680389155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2477784086534551147704413 929169032450456680389155)
                ·
                  refine ⟨1393753548675685020583733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929169032450456680389155 1393753548675685020583733)
                  ·
                    refine ⟨130664395188345470679725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1393753548675685020583733 130664395188345470679725)
                    ·
                      rfl

theorem cell23_763404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_763404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763404 prefixEnd_763404 := by exact prefixLift 763404
  have htrace : WordTrace (prefixWord ++ tailWord_763404) baseStart_763404 baseEnd_763404 := by
    simpa [prefixWord, tailWord_763404, baseEnd_763404] using wordTrace_append hprefix tailTrace_763404
  have hstable : (prefixWord ++ tailWord_763404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763404).length < 2 ^ (prefixWord ++ tailWord_763404).sum := by decide
  have hdescent : baseEnd_763404 < baseStart_763404 := by decide
  rcases family_descends (prefixWord ++ tailWord_763404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763447 : List Nat := [1, 1, 3, 1, 2, 4, 4, 7]
def baseStart_763447 : Nat := 118140960795 + 763447 * 2 ^ 59
def prefixEnd_763447 : Nat := 4983230072969 + 3 ^ 40 * 763447 * 2
def baseEnd_763447 : Nat := 14519083897525175696351

theorem tailTrace_763447 : CollatzResearch.WordTrace tailWord_763447 prefixEnd_763447 14519083897525175696351 := by
  unfold tailWord_763447
  simp only [CollatzResearch.WordTrace]
  refine ⟨27845199665169380212120595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18563466443446253474747063 27845199665169380212120595)
  ·
    refine ⟨41767799497754070318180893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27845199665169380212120595 41767799497754070318180893)
    ·
      refine ⟨15662924811657776369317835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41767799497754070318180893 15662924811657776369317835)
      ·
        refine ⟨23494387217486664553976753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15662924811657776369317835 23494387217486664553976753)
        ·
          refine ⟨17620790413114998415482565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23494387217486664553976753 17620790413114998415482565)
          ·
            refine ⟨3303898202459062202902981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17620790413114998415482565 3303898202459062202902981)
            ·
              refine ⟨619480912961074163044309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3303898202459062202902981 619480912961074163044309)
              ·
                refine ⟨14519083897525175696351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 619480912961074163044309 14519083897525175696351)
                ·
                  rfl

theorem cell23_763447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 7].length) (baseStart_763447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763447 prefixEnd_763447 := by exact prefixLift 763447
  have htrace : WordTrace (prefixWord ++ tailWord_763447) baseStart_763447 baseEnd_763447 := by
    simpa [prefixWord, tailWord_763447, baseEnd_763447] using wordTrace_append hprefix tailTrace_763447
  have hstable : (prefixWord ++ tailWord_763447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763447).length < 2 ^ (prefixWord ++ tailWord_763447).sum := by decide
  have hdescent : baseEnd_763447 < baseStart_763447 := by decide
  rcases family_descends (prefixWord ++ tailWord_763447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763491 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 3]
def baseStart_763491 : Nat := 118140960795 + 763491 * 2 ^ 59
def prefixEnd_763491 : Nat := 4983230072969 + 3 ^ 40 * 763491 * 2
def baseEnd_763491 : Nat := 392037858381977571651275

theorem tailTrace_763491 : CollatzResearch.WordTrace tailWord_763491 prefixEnd_763491 392037858381977571651275 := by
  unfold tailWord_763491
  simp only [CollatzResearch.WordTrace]
  refine ⟨27846804477009975726722327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18564536318006650484481551 27846804477009975726722327)
  ·
    refine ⟨41770206715514963590083491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27846804477009975726722327 41770206715514963590083491)
    ·
      refine ⟨62655310073272445385125237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41770206715514963590083491 62655310073272445385125237)
      ·
        refine ⟨5873935319369291754855491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62655310073272445385125237 5873935319369291754855491)
        ·
          refine ⟨8810902979053937632283237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5873935319369291754855491 8810902979053937632283237)
          ·
            refine ⟨1652044308572613306053107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8810902979053937632283237 1652044308572613306053107)
            ·
              refine ⟨2478066462858919959079661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652044308572613306053107 2478066462858919959079661)
              ·
                refine ⟨929274923572094984654873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2478066462858919959079661 929274923572094984654873)
                ·
                  refine ⟨696956192679071238491155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 929274923572094984654873 696956192679071238491155)
                  ·
                    refine ⟨1045434289018606857736733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 696956192679071238491155 1045434289018606857736733)
                    ·
                      refine ⟨392037858381977571651275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1045434289018606857736733 392037858381977571651275)
                      ·
                        rfl

theorem cell23_763491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_763491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763491 prefixEnd_763491 := by exact prefixLift 763491
  have htrace : WordTrace (prefixWord ++ tailWord_763491) baseStart_763491 baseEnd_763491 := by
    simpa [prefixWord, tailWord_763491, baseEnd_763491] using wordTrace_append hprefix tailTrace_763491
  have hstable : (prefixWord ++ tailWord_763491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763491).length < 2 ^ (prefixWord ++ tailWord_763491).sum := by decide
  have hdescent : baseEnd_763491 < baseStart_763491 := by decide
  rcases family_descends (prefixWord ++ tailWord_763491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763534 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_763534 : Nat := 118140960795 + 763534 * 2 ^ 59
def prefixEnd_763534 : Nat := 4983230072969 + 3 ^ 40 * 763534 * 2
def baseEnd_763534 : Nat := 392059938050120903413577

theorem tailTrace_763534 : CollatzResearch.WordTrace tailWord_763534 prefixEnd_763534 392059938050120903413577 := by
  unfold tailWord_763534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481046601981774258817207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18565581877236129380358437 3481046601981774258817207)
  ·
    refine ⟨5221569902972661388225811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3481046601981774258817207 5221569902972661388225811)
    ·
      refine ⟨7832354854458992082338717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5221569902972661388225811 7832354854458992082338717)
      ·
        refine ⟨2937133070422122030877019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7832354854458992082338717 2937133070422122030877019)
        ·
          refine ⟨4405699605633183046315529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2937133070422122030877019 4405699605633183046315529)
          ·
            refine ⟨3304274704224887284736647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4405699605633183046315529 3304274704224887284736647)
            ·
              refine ⟨4956412056337330927104971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304274704224887284736647 4956412056337330927104971)
              ·
                refine ⟨7434618084505996390657457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956412056337330927104971 7434618084505996390657457)
                ·
                  refine ⟨5575963563379497292993093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7434618084505996390657457 5575963563379497292993093)
                  ·
                    refine ⟨1045493168133655742436205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5575963563379497292993093 1045493168133655742436205)
                    ·
                      refine ⟨392059938050120903413577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1045493168133655742436205 392059938050120903413577)
                      ·
                        rfl

theorem cell23_763534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_763534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763534 prefixEnd_763534 := by exact prefixLift 763534
  have htrace : WordTrace (prefixWord ++ tailWord_763534) baseStart_763534 baseEnd_763534 := by
    simpa [prefixWord, tailWord_763534, baseEnd_763534] using wordTrace_append hprefix tailTrace_763534
  have hstable : (prefixWord ++ tailWord_763534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763534).length < 2 ^ (prefixWord ++ tailWord_763534).sum := by decide
  have hdescent : baseEnd_763534 < baseStart_763534 := by decide
  rcases family_descends (prefixWord ++ tailWord_763534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763544 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_763544 : Nat := 118140960795 + 763544 * 2 ^ 59
def prefixEnd_763544 : Nat := 4983230072969 + 3 ^ 40 * 763544 * 2
def baseEnd_763544 : Nat := 392065072856665864288531

theorem tailTrace_763544 : CollatzResearch.WordTrace tailWord_763544 prefixEnd_763544 392065072856665864288531 := by
  unfold tailWord_763544
  simp only [CollatzResearch.WordTrace]
  refine ⟨13924368772908982889200843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18565825030545310518934457 13924368772908982889200843)
  ·
    refine ⟨20886553159363474333801265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13924368772908982889200843 20886553159363474333801265)
    ·
      refine ⟨15664914869522605750350949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20886553159363474333801265 15664914869522605750350949)
      ·
        refine ⟨2937171538035488578190803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15664914869522605750350949 2937171538035488578190803)
        ·
          refine ⟨4405757307053232867286205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2937171538035488578190803 4405757307053232867286205)
          ·
            refine ⟨1652158990144962325232327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4405757307053232867286205 1652158990144962325232327)
            ·
              refine ⟨2478238485217443487848491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652158990144962325232327 2478238485217443487848491)
              ·
                refine ⟨3717357727826165231772737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2478238485217443487848491 3717357727826165231772737)
                ·
                  refine ⟨2788018295869623923829553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3717357727826165231772737 2788018295869623923829553)
                  ·
                    refine ⟨2091013721902217942872165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2788018295869623923829553 2091013721902217942872165)
                    ·
                      refine ⟨392065072856665864288531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2091013721902217942872165 392065072856665864288531)
                      ·
                        rfl

theorem cell23_763544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_763544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763544 prefixEnd_763544 := by exact prefixLift 763544
  have htrace : WordTrace (prefixWord ++ tailWord_763544) baseStart_763544 baseEnd_763544 := by
    simpa [prefixWord, tailWord_763544, baseEnd_763544] using wordTrace_append hprefix tailTrace_763544
  have hstable : (prefixWord ++ tailWord_763544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763544).length < 2 ^ (prefixWord ++ tailWord_763544).sum := by decide
  have hdescent : baseEnd_763544 < baseStart_763544 := by decide
  rcases family_descends (prefixWord ++ tailWord_763544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763548 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_763548 : Nat := 118140960795 + 763548 * 2 ^ 59
def prefixEnd_763548 : Nat := 4983230072969 + 3 ^ 40 * 763548 * 2
def baseEnd_763548 : Nat := 392067126779283848638513

theorem tailTrace_763548 : CollatzResearch.WordTrace tailWord_763548 prefixEnd_763548 392067126779283848638513 := by
  unfold tailWord_763548
  simp only [CollatzResearch.WordTrace]
  refine ⟨13924441718901737230773649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18565922291868982974364865 13924441718901737230773649)
  ·
    refine ⟨10443331289176302923080237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13924441718901737230773649 10443331289176302923080237)
    ·
      refine ⟨3916249233441113596155089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10443331289176302923080237 3916249233441113596155089)
      ·
        refine ⟨2937186925080835197116317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3916249233441113596155089 2937186925080835197116317)
        ·
          refine ⟨1101445096905313198918619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2937186925080835197116317 1101445096905313198918619)
          ·
            refine ⟨1652167645357969798377929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101445096905313198918619 1652167645357969798377929)
            ·
              refine ⟨1239125734018477348783447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652167645357969798377929 1239125734018477348783447)
              ·
                refine ⟨1858688601027716023175171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239125734018477348783447 1858688601027716023175171)
                ·
                  refine ⟨2788032901541574034762757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858688601027716023175171 2788032901541574034762757)
                  ·
                    refine ⟨522756169039045131518017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2788032901541574034762757 522756169039045131518017)
                    ·
                      refine ⟨392067126779283848638513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522756169039045131518017 392067126779283848638513)
                      ·
                        rfl

theorem cell23_763548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_763548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763548 prefixEnd_763548 := by exact prefixLift 763548
  have htrace : WordTrace (prefixWord ++ tailWord_763548) baseStart_763548 baseEnd_763548 := by
    simpa [prefixWord, tailWord_763548, baseEnd_763548] using wordTrace_append hprefix tailTrace_763548
  have hstable : (prefixWord ++ tailWord_763548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763548).length < 2 ^ (prefixWord ++ tailWord_763548).sum := by decide
  have hdescent : baseEnd_763548 < baseStart_763548 := by decide
  rcases family_descends (prefixWord ++ tailWord_763548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763567 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 1, 7]
def baseStart_763567 : Nat := 118140960795 + 763567 * 2 ^ 59
def prefixEnd_763567 : Nat := 4983230072969 + 3 ^ 40 * 763567 * 2
def baseEnd_763567 : Nat := 130692294303906424766975

theorem tailTrace_763567 : CollatzResearch.WordTrace tailWord_763567 prefixEnd_763567 130692294303906424766975 := by
  unfold tailWord_763567
  simp only [CollatzResearch.WordTrace]
  refine ⟨27849576424734640706488955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18566384283156427137659303 27849576424734640706488955)
  ·
    refine ⟨41774364637101961059733433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27849576424734640706488955 41774364637101961059733433)
    ·
      refine ⟨31330773477826470794800075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41774364637101961059733433 31330773477826470794800075)
      ·
        refine ⟨46996160216739706192200113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31330773477826470794800075 46996160216739706192200113)
        ·
          refine ⟨35247120162554779644150085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46996160216739706192200113 35247120162554779644150085)
          ·
            refine ⟨6608835030479021183278141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35247120162554779644150085 6608835030479021183278141)
            ·
              refine ⟨2478313136429632943729303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6608835030479021183278141 2478313136429632943729303)
              ·
                refine ⟨3717469704644449415593955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2478313136429632943729303 3717469704644449415593955)
                ·
                  refine ⟨5576204556966674123390933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717469704644449415593955 5576204556966674123390933)
                  ·
                    refine ⟨130692294303906424766975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5576204556966674123390933 130692294303906424766975)
                    ·
                      rfl

theorem cell23_763567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_763567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763567 prefixEnd_763567 := by exact prefixLift 763567
  have htrace : WordTrace (prefixWord ++ tailWord_763567) baseStart_763567 baseEnd_763567 := by
    simpa [prefixWord, tailWord_763567, baseEnd_763567] using wordTrace_append hprefix tailTrace_763567
  have hstable : (prefixWord ++ tailWord_763567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763567).length < 2 ^ (prefixWord ++ tailWord_763567).sum := by decide
  have hdescent : baseEnd_763567 < baseStart_763567 := by decide
  rcases family_descends (prefixWord ++ tailWord_763567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763577 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_763577 : Nat := 118140960795 + 763577 * 2 ^ 59
def prefixEnd_763577 : Nat := 4983230072969 + 3 ^ 40 * 763577 * 2
def baseEnd_763577 : Nat := 392082017718264235175879

theorem tailTrace_763577 : CollatzResearch.WordTrace tailWord_763577 prefixEnd_763577 392082017718264235175879 := by
  unfold tailWord_763577
  simp only [CollatzResearch.WordTrace]
  refine ⟨27849941154698412414352985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18566627436465608276235323 27849941154698412414352985)
  ·
    refine ⟨20887455866023809310764739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27849941154698412414352985 20887455866023809310764739)
    ·
      refine ⟨31331183799035713966147109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20887455866023809310764739 31331183799035713966147109)
      ·
        refine ⟨5874596962319196368652583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31331183799035713966147109 5874596962319196368652583)
        ·
          refine ⟨8811895443478794552978875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5874596962319196368652583 8811895443478794552978875)
          ·
            refine ⟨13217843165218191829468313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8811895443478794552978875 13217843165218191829468313)
            ·
              refine ⟨9913382373913643872101235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13217843165218191829468313 9913382373913643872101235)
              ·
                refine ⟨14870073560870465808151853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9913382373913643872101235 14870073560870465808151853)
                ·
                  refine ⟨5576277585326424678056945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14870073560870465808151853 5576277585326424678056945)
                  ·
                    refine ⟨4182208188994818508542709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5576277585326424678056945 4182208188994818508542709)
                    ·
                      refine ⟨392082017718264235175879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4182208188994818508542709 392082017718264235175879)
                      ·
                        rfl

theorem cell23_763577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_763577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763577 prefixEnd_763577 := by exact prefixLift 763577
  have htrace : WordTrace (prefixWord ++ tailWord_763577) baseStart_763577 baseEnd_763577 := by
    simpa [prefixWord, tailWord_763577, baseEnd_763577] using wordTrace_append hprefix tailTrace_763577
  have hstable : (prefixWord ++ tailWord_763577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763577).length < 2 ^ (prefixWord ++ tailWord_763577).sum := by decide
  have hdescent : baseEnd_763577 < baseStart_763577 := by decide
  rcases family_descends (prefixWord ++ tailWord_763577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763627 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 8]
def baseStart_763627 : Nat := 118140960795 + 763627 * 2 ^ 59
def prefixEnd_763627 : Nat := 4983230072969 + 3 ^ 40 * 763627 * 2
def baseEnd_763627 : Nat := 43567521305665448838961

theorem tailTrace_763627 : CollatzResearch.WordTrace tailWord_763627 prefixEnd_763627 43567521305665448838961 := by
  unfold tailWord_763627
  simp only [CollatzResearch.WordTrace]
  refine ⟨27851764804517270953673135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18567843203011513969115423 27851764804517270953673135)
  ·
    refine ⟨41777647206775906430509703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27851764804517270953673135 41777647206775906430509703)
    ·
      refine ⟨62666470810163859645764555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41777647206775906430509703 62666470810163859645764555)
      ·
        refine ⟨93999706215245789468646833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62666470810163859645764555 93999706215245789468646833)
        ·
          refine ⟨70499779661434342101485125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93999706215245789468646833 70499779661434342101485125)
          ·
            refine ⟨13218708686518939144028461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70499779661434342101485125 13218708686518939144028461)
            ·
              refine ⟨4957015757444602179010673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13218708686518939144028461 4957015757444602179010673)
              ·
                refine ⟨3717761818083451634258005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4957015757444602179010673 3717761818083451634258005)
                ·
                  refine ⟨43567521305665448838961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3717761818083451634258005 43567521305665448838961)
                  ·
                    rfl

theorem cell23_763627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 8].length) (baseStart_763627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763627 prefixEnd_763627 := by exact prefixLift 763627
  have htrace : WordTrace (prefixWord ++ tailWord_763627) baseStart_763627 baseEnd_763627 := by
    simpa [prefixWord, tailWord_763627, baseEnd_763627] using wordTrace_append hprefix tailTrace_763627
  have hstable : (prefixWord ++ tailWord_763627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763627).length < 2 ^ (prefixWord ++ tailWord_763627).sum := by decide
  have hdescent : baseEnd_763627 < baseStart_763627 := by decide
  rcases family_descends (prefixWord ++ tailWord_763627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763644 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 6]
def baseStart_763644 : Nat := 118140960795 + 763644 * 2 ^ 59
def prefixEnd_763644 : Nat := 4983230072969 + 3 ^ 40 * 763644 * 2
def baseEnd_763644 : Nat := 43568491213568385893119

theorem tailTrace_763644 : CollatzResearch.WordTrace tailWord_763644 prefixEnd_763644 43568491213568385893119 := by
  unfold tailWord_763644
  simp only [CollatzResearch.WordTrace]
  refine ⟨13926192422727841428520993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18568256563637121904694657 13926192422727841428520993)
  ·
    refine ⟨10444644317045881071390745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13926192422727841428520993 10444644317045881071390745)
    ·
      refine ⟨7833483237784410803543059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10444644317045881071390745 7833483237784410803543059)
      ·
        refine ⟨11750224856676616205314589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7833483237784410803543059 11750224856676616205314589)
        ·
          refine ⟨4406334321253731076992971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11750224856676616205314589 4406334321253731076992971)
          ·
            refine ⟨6609501481880596615489457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4406334321253731076992971 6609501481880596615489457)
            ·
              refine ⟨4957126111410447461617093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6609501481880596615489457 4957126111410447461617093)
              ·
                refine ⟨929461145889458899053205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4957126111410447461617093 929461145889458899053205)
                ·
                  refine ⟨43568491213568385893119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 929461145889458899053205 43568491213568385893119)
                  ·
                    rfl

theorem cell23_763644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_763644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763644 prefixEnd_763644 := by exact prefixLift 763644
  have htrace : WordTrace (prefixWord ++ tailWord_763644) baseStart_763644 baseEnd_763644 := by
    simpa [prefixWord, tailWord_763644, baseEnd_763644] using wordTrace_append hprefix tailTrace_763644
  have hstable : (prefixWord ++ tailWord_763644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763644).length < 2 ^ (prefixWord ++ tailWord_763644).sum := by decide
  have hdescent : baseEnd_763644 < baseStart_763644 := by decide
  rcases family_descends (prefixWord ++ tailWord_763644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763647 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_763647 : Nat := 118140960795 + 763647 * 2 ^ 59
def prefixEnd_763647 : Nat := 4983230072969 + 3 ^ 40 * 763647 * 2
def baseEnd_763647 : Nat := 392117961364078961300557

theorem tailTrace_763647 : CollatzResearch.WordTrace tailWord_763647 prefixEnd_763647 392117961364078961300557 := by
  unfold tailWord_763647
  simp only [CollatzResearch.WordTrace]
  refine ⟨27852494264444814369401195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18568329509629876246267463 27852494264444814369401195)
  ·
    refine ⟨41778741396667221554101793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27852494264444814369401195 41778741396667221554101793)
    ·
      refine ⟨31334056047500416165576345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41778741396667221554101793 31334056047500416165576345)
      ·
        refine ⟨23500542035625312124182259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31334056047500416165576345 23500542035625312124182259)
        ·
          refine ⟨35250813053437968186273389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23500542035625312124182259 35250813053437968186273389)
          ·
            refine ⟨13219054895039238069852521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35250813053437968186273389 13219054895039238069852521)
            ·
              refine ⟨9914291171279428552389391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13219054895039238069852521 9914291171279428552389391)
              ·
                refine ⟨14871436756919142828584087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9914291171279428552389391 14871436756919142828584087)
                ·
                  refine ⟨22307155135378714242876131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14871436756919142828584087 22307155135378714242876131)
                  ·
                    refine ⟨33460732703068071364314197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22307155135378714242876131 33460732703068071364314197)
                    ·
                      refine ⟨392117961364078961300557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 33460732703068071364314197 392117961364078961300557)
                      ·
                        rfl

theorem cell23_763647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_763647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763647 prefixEnd_763647 := by exact prefixLift 763647
  have htrace : WordTrace (prefixWord ++ tailWord_763647) baseStart_763647 baseEnd_763647 := by
    simpa [prefixWord, tailWord_763647, baseEnd_763647] using wordTrace_append hprefix tailTrace_763647
  have hstable : (prefixWord ++ tailWord_763647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763647).length < 2 ^ (prefixWord ++ tailWord_763647).sum := by decide
  have hdescent : baseEnd_763647 < baseStart_763647 := by decide
  rcases family_descends (prefixWord ++ tailWord_763647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763657 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 2, 9]
def baseStart_763657 : Nat := 118140960795 + 763657 * 2 ^ 59
def prefixEnd_763657 : Nat := 4983230072969 + 3 ^ 40 * 763657 * 2
def baseEnd_763657 : Nat := 130707698723541307391837

theorem tailTrace_763657 : CollatzResearch.WordTrace tailWord_763657 prefixEnd_763657 130707698723541307391837 := by
  unfold tailWord_763657
  simp only [CollatzResearch.WordTrace]
  refine ⟨27852858994408586077265225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18568572662939057384843483 27852858994408586077265225)
  ·
    refine ⟨20889644245806439557948919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27852858994408586077265225 20889644245806439557948919)
    ·
      refine ⟨31334466368709659336923379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20889644245806439557948919 31334466368709659336923379)
      ·
        refine ⟨47001699553064489005385069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31334466368709659336923379 47001699553064489005385069)
        ·
          refine ⟨17625637332399183377019401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47001699553064489005385069 17625637332399183377019401)
          ·
            refine ⟨13219227999299387532764551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17625637332399183377019401 13219227999299387532764551)
            ·
              refine ⟨19828841998949081299146827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13219227999299387532764551 19828841998949081299146827)
              ·
                refine ⟨29743262998423621948720241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19828841998949081299146827 29743262998423621948720241)
                ·
                  refine ⟨22307447248817716461540181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29743262998423621948720241 22307447248817716461540181)
                  ·
                    refine ⟨130707698723541307391837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 22307447248817716461540181 130707698723541307391837)
                    ·
                      rfl

theorem cell23_763657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_763657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763657 prefixEnd_763657 := by exact prefixLift 763657
  have htrace : WordTrace (prefixWord ++ tailWord_763657) baseStart_763657 baseEnd_763657 := by
    simpa [prefixWord, tailWord_763657, baseEnd_763657] using wordTrace_append hprefix tailTrace_763657
  have hstable : (prefixWord ++ tailWord_763657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763657).length < 2 ^ (prefixWord ++ tailWord_763657).sum := by decide
  have hdescent : baseEnd_763657 < baseStart_763657 := by decide
  rcases family_descends (prefixWord ++ tailWord_763657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
