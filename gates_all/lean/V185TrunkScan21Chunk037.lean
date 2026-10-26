import V185TrunkScan21Chunk036

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_447388 : List Nat := [2, 2, 3, 3, 3, 1, 1, 6]
def baseStart_447388 : Nat := 118140960795 + 447388 * 2 ^ 59
def prefixEnd_447388 : Nat := 4983230072969 + 3 ^ 40 * 447388 * 2
def baseEnd_447388 : Nat := 34033345637600122384075

theorem tailTrace_447388 : CollatzResearch.WordTrace tailWord_447388 prefixEnd_447388 34033345637600122384075 := by
  unfold tailWord_447388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8158790451598579316187409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10878387268798105754916545 8158790451598579316187409)
  ·
    refine ⟨6119092838698934487140557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8158790451598579316187409 6119092838698934487140557)
    ·
      refine ⟨2294659814512100432677709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6119092838698934487140557 2294659814512100432677709)
      ·
        refine ⟨860497430442037662254141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2294659814512100432677709 860497430442037662254141)
        ·
          refine ⟨322686536415764123345303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 860497430442037662254141 322686536415764123345303)
          ·
            refine ⟨484029804623646185017955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322686536415764123345303 484029804623646185017955)
            ·
              refine ⟨726044706935469277526933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484029804623646185017955 726044706935469277526933)
              ·
                refine ⟨34033345637600122384075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 726044706935469277526933 34033345637600122384075)
                ·
                  rfl

theorem cell21_447388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_447388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447388 prefixEnd_447388 := by exact prefixLift 447388
  have htrace : WordTrace (prefixWord ++ tailWord_447388) baseStart_447388 baseEnd_447388 := by
    simpa [prefixWord, tailWord_447388, baseEnd_447388] using wordTrace_append hprefix tailTrace_447388
  have hstable : (prefixWord ++ tailWord_447388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447388).length < 2 ^ (prefixWord ++ tailWord_447388).sum := by decide
  have hdescent : baseEnd_447388 < baseStart_447388 := by decide
  rcases family_descends (prefixWord ++ tailWord_447388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447489 : List Nat := [1, 2, 4, 1, 2, 2, 9]
def baseStart_447489 : Nat := 118140960795 + 447489 * 2 ^ 59
def prefixEnd_447489 : Nat := 4983230072969 + 3 ^ 40 * 447489 * 2
def baseEnd_447489 : Nat := 11347009609871848440965

theorem tailTrace_447489 : CollatzResearch.WordTrace tailWord_447489 prefixEnd_447489 11347009609871848440965 := by
  unfold tailWord_447489
  simp only [CollatzResearch.WordTrace]
  refine ⟨16321264675831252881801521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10880843117220835254534347 16321264675831252881801521)
  ·
    refine ⟨12240948506873439661351141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16321264675831252881801521 12240948506873439661351141)
    ·
      refine ⟨2295177845038769936503339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12240948506873439661351141 2295177845038769936503339)
      ·
        refine ⟨3442766767558154904755009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295177845038769936503339 3442766767558154904755009)
        ·
          refine ⟨2582075075668616178566257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442766767558154904755009 2582075075668616178566257)
          ·
            refine ⟨1936556306751462133924693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582075075668616178566257 1936556306751462133924693)
            ·
              refine ⟨11347009609871848440965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1936556306751462133924693 11347009609871848440965)
              ·
                rfl

theorem cell21_447489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 9].length) (baseStart_447489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447489 prefixEnd_447489 := by exact prefixLift 447489
  have htrace : WordTrace (prefixWord ++ tailWord_447489) baseStart_447489 baseEnd_447489 := by
    simpa [prefixWord, tailWord_447489, baseEnd_447489] using wordTrace_append hprefix tailTrace_447489
  have hstable : (prefixWord ++ tailWord_447489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447489).length < 2 ^ (prefixWord ++ tailWord_447489).sum := by decide
  have hdescent : baseEnd_447489 < baseStart_447489 := by decide
  rcases family_descends (prefixWord ++ tailWord_447489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447503 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 11]
def baseStart_447503 : Nat := 118140960795 + 447503 * 2 ^ 59
def prefixEnd_447503 : Nat := 4983230072969 + 3 ^ 40 * 447503 * 2
def baseEnd_447503 : Nat := 102126281479585722735323

theorem tailTrace_447503 : CollatzResearch.WordTrace tailWord_447503 prefixEnd_447503 102126281479585722735323 := by
  unfold tailWord_447503
  simp only [CollatzResearch.WordTrace]
  refine ⟨16321775297780533272811163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10881183531853688848540775 16321775297780533272811163)
  ·
    refine ⟨24482662946670799909216745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16321775297780533272811163 24482662946670799909216745)
    ·
      refine ⟨18361997210003099931912559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24482662946670799909216745 18361997210003099931912559)
      ·
        refine ⟨27542995815004649897868839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18361997210003099931912559 27542995815004649897868839)
        ·
          refine ⟨41314493722506974846803259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27542995815004649897868839 41314493722506974846803259)
          ·
            refine ⟨61971740583760462270204889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41314493722506974846803259 61971740583760462270204889)
            ·
              refine ⟨46478805437820346702653667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61971740583760462270204889 46478805437820346702653667)
              ·
                refine ⟨69718208156730520053980501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46478805437820346702653667 69718208156730520053980501)
                ·
                  refine ⟨102126281479585722735323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 69718208156730520053980501 102126281479585722735323)
                  ·
                    rfl

theorem cell21_447503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_447503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447503 prefixEnd_447503 := by exact prefixLift 447503
  have htrace : WordTrace (prefixWord ++ tailWord_447503) baseStart_447503 baseEnd_447503 := by
    simpa [prefixWord, tailWord_447503, baseEnd_447503] using wordTrace_append hprefix tailTrace_447503
  have hstable : (prefixWord ++ tailWord_447503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447503).length < 2 ^ (prefixWord ++ tailWord_447503).sum := by decide
  have hdescent : baseEnd_447503 < baseStart_447503 := by decide
  rcases family_descends (prefixWord ++ tailWord_447503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447509 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 4]
def baseStart_447509 : Nat := 118140960795 + 447509 * 2 ^ 59
def prefixEnd_447509 : Nat := 4983230072969 + 3 ^ 40 * 447509 * 2
def baseEnd_447509 : Nat := 102127650761331045635311

theorem tailTrace_447509 : CollatzResearch.WordTrace tailWord_447509 prefixEnd_447509 102127650761331045635311 := by
  unfold tailWord_447509
  simp only [CollatzResearch.WordTrace]
  refine ⟨16321994135758796297529581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10881329423839197531686387 16321994135758796297529581)
  ·
    refine ⟨6120747800909548611573593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16321994135758796297529581 6120747800909548611573593)
    ·
      refine ⟨4590560850682161458680195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6120747800909548611573593 4590560850682161458680195)
      ·
        refine ⟨6885841276023242188020293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590560850682161458680195 6885841276023242188020293)
        ·
          refine ⟨1291095239254357910253805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6885841276023242188020293 1291095239254357910253805)
          ·
            refine ⟨484160714720384216345177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1291095239254357910253805 484160714720384216345177)
            ·
              refine ⟨363120536040288162258883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484160714720384216345177 363120536040288162258883)
              ·
                refine ⟨544680804060432243388325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363120536040288162258883 544680804060432243388325)
                ·
                  refine ⟨102127650761331045635311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544680804060432243388325 102127650761331045635311)
                  ·
                    rfl

theorem cell21_447509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_447509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447509 prefixEnd_447509 := by exact prefixLift 447509
  have htrace : WordTrace (prefixWord ++ tailWord_447509) baseStart_447509 baseEnd_447509 := by
    simpa [prefixWord, tailWord_447509, baseEnd_447509] using wordTrace_append hprefix tailTrace_447509
  have hstable : (prefixWord ++ tailWord_447509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447509).length < 2 ^ (prefixWord ++ tailWord_447509).sum := by decide
  have hdescent : baseEnd_447509 < baseStart_447509 := by decide
  rcases family_descends (prefixWord ++ tailWord_447509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447537 : List Nat := [1, 2, 2, 3, 1, 2, 2, 5, 3]
def baseStart_447537 : Nat := 118140960795 + 447537 * 2 ^ 59
def prefixEnd_447537 : Nat := 4983230072969 + 3 ^ 40 * 447537 * 2
def baseEnd_447537 : Nat := 102134040742809219168587

theorem tailTrace_447537 : CollatzResearch.WordTrace tailWord_447537 prefixEnd_447537 102134040742809219168587 := by
  unfold tailWord_447537
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323015379657357079548865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10882010253104904719699243 16323015379657357079548865)
  ·
    refine ⟨12242261534743017809661649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16323015379657357079548865 12242261534743017809661649)
    ·
      refine ⟨9181696151057263357246237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12242261534743017809661649 9181696151057263357246237)
      ·
        refine ⟨3443136056646473758967339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9181696151057263357246237 3443136056646473758967339)
        ·
          refine ⟨5164704084969710638451009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443136056646473758967339 5164704084969710638451009)
          ·
            refine ⟨3873528063727282978838257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5164704084969710638451009 3873528063727282978838257)
            ·
              refine ⟨2905146047795462234128693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873528063727282978838257 2905146047795462234128693)
              ·
                refine ⟨272357441980824584449565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2905146047795462234128693 272357441980824584449565)
                ·
                  refine ⟨102134040742809219168587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272357441980824584449565 102134040742809219168587)
                  ·
                    rfl

theorem cell21_447537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_447537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447537 prefixEnd_447537 := by exact prefixLift 447537
  have htrace : WordTrace (prefixWord ++ tailWord_447537) baseStart_447537 baseEnd_447537 := by
    simpa [prefixWord, tailWord_447537, baseEnd_447537] using wordTrace_append hprefix tailTrace_447537
  have hstable : (prefixWord ++ tailWord_447537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447537).length < 2 ^ (prefixWord ++ tailWord_447537).sum := by decide
  have hdescent : baseEnd_447537 < baseStart_447537 := by decide
  rcases family_descends (prefixWord ++ tailWord_447537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447613 : List Nat := [1, 4, 1, 1, 3, 1, 1, 6, 3]
def baseStart_447613 : Nat := 118140960795 + 447613 * 2 ^ 59
def prefixEnd_447613 : Nat := 4983230072969 + 3 ^ 40 * 447613 * 2
def baseEnd_447613 : Nat := 102151384978249975901765

theorem tailTrace_447613 : CollatzResearch.WordTrace tailWord_447613 prefixEnd_447613 102151384978249975901765 := by
  unfold tailWord_447613
  simp only [CollatzResearch.WordTrace]
  refine ⟨16325787327382022059315493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10883858218254681372876995 16325787327382022059315493)
  ·
    refine ⟨3061085123884129136121655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16325787327382022059315493 3061085123884129136121655)
    ·
      refine ⟨4591627685826193704182483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3061085123884129136121655 4591627685826193704182483)
      ·
        refine ⟨6887441528739290556273725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591627685826193704182483 6887441528739290556273725)
        ·
          refine ⟨2582790573277233958602647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6887441528739290556273725 2582790573277233958602647)
          ·
            refine ⟨3874185859915850937903971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582790573277233958602647 3874185859915850937903971)
            ·
              refine ⟨5811278789873776406855957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874185859915850937903971 5811278789873776406855957)
              ·
                refine ⟨272403693275333269071373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5811278789873776406855957 272403693275333269071373)
                ·
                  refine ⟨102151384978249975901765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272403693275333269071373 102151384978249975901765)
                  ·
                    rfl

theorem cell21_447613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_447613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447613 prefixEnd_447613 := by exact prefixLift 447613
  have htrace : WordTrace (prefixWord ++ tailWord_447613) baseStart_447613 baseEnd_447613 := by
    simpa [prefixWord, tailWord_447613, baseEnd_447613] using wordTrace_append hprefix tailTrace_447613
  have hstable : (prefixWord ++ tailWord_447613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447613).length < 2 ^ (prefixWord ++ tailWord_447613).sum := by decide
  have hdescent : baseEnd_447613 < baseStart_447613 := by decide
  rcases family_descends (prefixWord ++ tailWord_447613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447647 : List Nat := [1, 1, 2, 6, 2, 2, 1, 3, 3]
def baseStart_447647 : Nat := 118140960795 + 447647 * 2 ^ 59
def prefixEnd_447647 : Nat := 4983230072969 + 3 ^ 40 * 447647 * 2
def baseEnd_447647 : Nat := 102159144241473472335029

theorem tailTrace_447647 : CollatzResearch.WordTrace tailWord_447647 prefixEnd_447647 102159144241473472335029 := by
  unfold tailWord_447647
  simp only [CollatzResearch.WordTrace]
  refine ⟨16327027409258845866053195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10884684939505897244035463 16327027409258845866053195)
  ·
    refine ⟨24490541113888268799079793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16327027409258845866053195 24490541113888268799079793)
    ·
      refine ⟨18367905835416201599309845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24490541113888268799079793 18367905835416201599309845)
      ·
        refine ⟨860995586035134449967649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18367905835416201599309845 860995586035134449967649)
        ·
          refine ⟨645746689526350837475737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 860995586035134449967649 645746689526350837475737)
          ·
            refine ⟨484310017144763128106803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645746689526350837475737 484310017144763128106803)
            ·
              refine ⟨726465025717144692160205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484310017144763128106803 726465025717144692160205)
              ·
                refine ⟨272424384643929259560077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726465025717144692160205 272424384643929259560077)
                ·
                  refine ⟨102159144241473472335029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272424384643929259560077 102159144241473472335029)
                  ·
                    rfl

theorem cell21_447647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 3].length) (baseStart_447647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447647 prefixEnd_447647 := by exact prefixLift 447647
  have htrace : WordTrace (prefixWord ++ tailWord_447647) baseStart_447647 baseEnd_447647 := by
    simpa [prefixWord, tailWord_447647, baseEnd_447647] using wordTrace_append hprefix tailTrace_447647
  have hstable : (prefixWord ++ tailWord_447647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447647).length < 2 ^ (prefixWord ++ tailWord_447647).sum := by decide
  have hdescent : baseEnd_447647 < baseStart_447647 := by decide
  rcases family_descends (prefixWord ++ tailWord_447647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447658 : List Nat := [3, 1, 5, 1, 1, 1, 9]
def baseStart_447658 : Nat := 118140960795 + 447658 * 2 ^ 59
def prefixEnd_447658 : Nat := 4983230072969 + 3 ^ 40 * 447658 * 2
def baseEnd_447658 : Nat := 11351294954593321961297

theorem tailTrace_447658 : CollatzResearch.WordTrace tailWord_447658 prefixEnd_447658 11351294954593321961297 := by
  unfold tailWord_447658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4081857153054748686175907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10884952408145996496469085 4081857153054748686175907)
  ·
    refine ⟨6122785729582123029263861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4081857153054748686175907 6122785729582123029263861)
    ·
      refine ⟨574011162148324033993487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6122785729582123029263861 574011162148324033993487)
      ·
        refine ⟨861016743222486050990231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574011162148324033993487 861016743222486050990231)
        ·
          refine ⟨1291525114833729076485347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861016743222486050990231 1291525114833729076485347)
          ·
            refine ⟨1937287672250593614728021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291525114833729076485347 1937287672250593614728021)
            ·
              refine ⟨11351294954593321961297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1937287672250593614728021 11351294954593321961297)
              ·
                rfl

theorem cell21_447658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 9].length) (baseStart_447658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447658 prefixEnd_447658 := by exact prefixLift 447658
  have htrace : WordTrace (prefixWord ++ tailWord_447658) baseStart_447658 baseEnd_447658 := by
    simpa [prefixWord, tailWord_447658, baseEnd_447658] using wordTrace_append hprefix tailTrace_447658
  have hstable : (prefixWord ++ tailWord_447658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447658).length < 2 ^ (prefixWord ++ tailWord_447658).sum := by decide
  have hdescent : baseEnd_447658 < baseStart_447658 := by decide
  rcases family_descends (prefixWord ++ tailWord_447658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447717 : List Nat := [1, 3, 1, 4, 3, 9]
def baseStart_447717 : Nat := 118140960795 + 447717 * 2 ^ 59
def prefixEnd_447717 : Nat := 4983230072969 + 3 ^ 40 * 447717 * 2
def baseEnd_447717 : Nat := 3784263673895144672897

theorem tailTrace_447717 : CollatzResearch.WordTrace tailWord_447717 prefixEnd_447717 3784263673895144672897 := by
  unfold tailWord_447717
  simp only [CollatzResearch.WordTrace]
  refine ⟨16329580519005247821101405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10886387012670165214067603 16329580519005247821101405)
  ·
    refine ⟨6123592694626967932913027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16329580519005247821101405 6123592694626967932913027)
    ·
      refine ⟨9185389041940451899369541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6123592694626967932913027 9185389041940451899369541)
      ·
        refine ⟨1722260445363834731131789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9185389041940451899369541 1722260445363834731131789)
        ·
          refine ⟨645847667011438024174421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1722260445363834731131789 645847667011438024174421)
          ·
            refine ⟨3784263673895144672897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 645847667011438024174421 3784263673895144672897)
            ·
              rfl

theorem cell21_447717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 9].length) (baseStart_447717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447717 prefixEnd_447717 := by exact prefixLift 447717
  have htrace : WordTrace (prefixWord ++ tailWord_447717) baseStart_447717 baseEnd_447717 := by
    simpa [prefixWord, tailWord_447717, baseEnd_447717] using wordTrace_append hprefix tailTrace_447717
  have hstable : (prefixWord ++ tailWord_447717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447717).length < 2 ^ (prefixWord ++ tailWord_447717).sum := by decide
  have hdescent : baseEnd_447717 < baseStart_447717 := by decide
  rcases family_descends (prefixWord ++ tailWord_447717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447748 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_447748 : Nat := 118140960795 + 447748 * 2 ^ 59
def prefixEnd_447748 : Nat := 4983230072969 + 3 ^ 40 * 447748 * 2
def baseEnd_447748 : Nat := 102182193817519741151489

theorem tailTrace_447748 : CollatzResearch.WordTrace tailWord_447748 prefixEnd_447748 102182193817519741151489 := by
  unfold tailWord_447748
  simp only [CollatzResearch.WordTrace]
  refine ⟨8165355590946470057739949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10887140787928626743653265 8165355590946470057739949)
  ·
    refine ⟨3062008346604926271652481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8165355590946470057739949 3062008346604926271652481)
    ·
      refine ⟨2296506259953694703739361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3062008346604926271652481 2296506259953694703739361)
      ·
        refine ⟨1722379694965271027804521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2296506259953694703739361 1722379694965271027804521)
        ·
          refine ⟨1291784771223953270853391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1722379694965271027804521 1291784771223953270853391)
          ·
            refine ⟨1937677156835929906280087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291784771223953270853391 1937677156835929906280087)
            ·
              refine ⟨2906515735253894859420131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937677156835929906280087 2906515735253894859420131)
              ·
                refine ⟨4359773602880842289130197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906515735253894859420131 4359773602880842289130197)
                ·
                  refine ⟨102182193817519741151489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4359773602880842289130197 102182193817519741151489)
                  ·
                    rfl

theorem cell21_447748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_447748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447748 prefixEnd_447748 := by exact prefixLift 447748
  have htrace : WordTrace (prefixWord ++ tailWord_447748) baseStart_447748 baseEnd_447748 := by
    simpa [prefixWord, tailWord_447748, baseEnd_447748] using wordTrace_append hprefix tailTrace_447748
  have hstable : (prefixWord ++ tailWord_447748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447748).length < 2 ^ (prefixWord ++ tailWord_447748).sum := by decide
  have hdescent : baseEnd_447748 < baseStart_447748 := by decide
  rcases family_descends (prefixWord ++ tailWord_447748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447779 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 4]
def baseStart_447779 : Nat := 118140960795 + 447779 * 2 ^ 59
def prefixEnd_447779 : Nat := 4983230072969 + 3 ^ 40 * 447779 * 2
def baseEnd_447779 : Nat := 102189268439870576134759

theorem tailTrace_447779 : CollatzResearch.WordTrace tailWord_447779 prefixEnd_447779 102189268439870576134759 := by
  unfold tailWord_447779
  simp only [CollatzResearch.WordTrace]
  refine ⟨16331841844780632409858391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10887894563187088273238927 16331841844780632409858391)
  ·
    refine ⟨24497762767170948614787587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16331841844780632409858391 24497762767170948614787587)
    ·
      refine ⟨36746644150756422922181381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24497762767170948614787587 36746644150756422922181381)
      ·
        refine ⟨6889995778266829297909009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36746644150756422922181381 6889995778266829297909009)
        ·
          refine ⟨5167496833700121973431757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6889995778266829297909009 5167496833700121973431757)
          ·
            refine ⟨1937811312637545740036909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5167496833700121973431757 1937811312637545740036909)
            ·
              refine ⟨726679242239079652513841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1937811312637545740036909 726679242239079652513841)
              ·
                refine ⟨545009431679309739385381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726679242239079652513841 545009431679309739385381)
                ·
                  refine ⟨102189268439870576134759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545009431679309739385381 102189268439870576134759)
                  ·
                    rfl

theorem cell21_447779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 4].length) (baseStart_447779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447779 prefixEnd_447779 := by exact prefixLift 447779
  have htrace : WordTrace (prefixWord ++ tailWord_447779) baseStart_447779 baseEnd_447779 := by
    simpa [prefixWord, tailWord_447779, baseEnd_447779] using wordTrace_append hprefix tailTrace_447779
  have hstable : (prefixWord ++ tailWord_447779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447779).length < 2 ^ (prefixWord ++ tailWord_447779).sum := by decide
  have hdescent : baseEnd_447779 < baseStart_447779 := by decide
  rcases family_descends (prefixWord ++ tailWord_447779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447886 : List Nat := [4, 1, 1, 4, 3, 8]
def baseStart_447886 : Nat := 118140960795 + 447886 * 2 ^ 59
def prefixEnd_447886 : Nat := 4983230072969 + 3 ^ 40 * 447886 * 2
def baseEnd_447886 : Nat := 3785692122135635846341

theorem tailTrace_447886 : CollatzResearch.WordTrace tailWord_447886 prefixEnd_447886 3785692122135635846341 := by
  unfold tailWord_447886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041968056924123710500439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10890496303595326456002341 2041968056924123710500439)
  ·
    refine ⟨3062952085386185565750659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2041968056924123710500439 3062952085386185565750659)
    ·
      refine ⟨4594428128079278348625989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3062952085386185565750659 4594428128079278348625989)
      ·
        refine ⟨861455274014864690367373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4594428128079278348625989 861455274014864690367373)
        ·
          refine ⟨323045727755574258887765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 861455274014864690367373 323045727755574258887765)
          ·
            refine ⟨3785692122135635846341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 323045727755574258887765 3785692122135635846341)
            ·
              rfl

theorem cell21_447886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 8].length) (baseStart_447886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447886 prefixEnd_447886 := by exact prefixLift 447886
  have htrace : WordTrace (prefixWord ++ tailWord_447886) baseStart_447886 baseEnd_447886 := by
    simpa [prefixWord, tailWord_447886, baseEnd_447886] using wordTrace_append hprefix tailTrace_447886
  have hstable : (prefixWord ++ tailWord_447886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447886).length < 2 ^ (prefixWord ++ tailWord_447886).sum := by decide
  have hdescent : baseEnd_447886 < baseStart_447886 := by decide
  rcases family_descends (prefixWord ++ tailWord_447886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447917 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 5]
def baseStart_447917 : Nat := 118140960795 + 447917 * 2 ^ 59
def prefixEnd_447917 : Nat := 4983230072969 + 3 ^ 40 * 447917 * 2
def baseEnd_447917 : Nat := 102220761920013002834477

theorem tailTrace_447917 : CollatzResearch.WordTrace tailWord_447917 prefixEnd_447917 102220761920013002834477 := by
  unfold tailWord_447917
  simp only [CollatzResearch.WordTrace]
  refine ⟨16336875118280681978382005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10891250078853787985588003 16336875118280681978382005)
  ·
    refine ⟨1531582042338813935473313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16336875118280681978382005 1531582042338813935473313)
    ·
      refine ⟨1148686531754110451604985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1531582042338813935473313 1148686531754110451604985)
      ·
        refine ⟨861514898815582838703739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1148686531754110451604985 861514898815582838703739)
        ·
          refine ⟨1292272348223374258055609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861514898815582838703739 1292272348223374258055609)
          ·
            refine ⟨969204261167530693541707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292272348223374258055609 969204261167530693541707)
            ·
              refine ⟨1453806391751296040312561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969204261167530693541707 1453806391751296040312561)
              ·
                refine ⟨1090354793813472030234421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1453806391751296040312561 1090354793813472030234421)
                ·
                  refine ⟨102220761920013002834477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1090354793813472030234421 102220761920013002834477)
                  ·
                    rfl

theorem cell21_447917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_447917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447917 prefixEnd_447917 := by exact prefixLift 447917
  have htrace : WordTrace (prefixWord ++ tailWord_447917) baseStart_447917 baseEnd_447917 := by
    simpa [prefixWord, tailWord_447917, baseEnd_447917] using wordTrace_append hprefix tailTrace_447917
  have hstable : (prefixWord ++ tailWord_447917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447917).length < 2 ^ (prefixWord ++ tailWord_447917).sum := by decide
  have hdescent : baseEnd_447917 < baseStart_447917 := by decide
  rcases family_descends (prefixWord ++ tailWord_447917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447928 : List Nat := [2, 1, 2, 1, 2, 2, 2, 9]
def baseStart_447928 : Nat := 118140960795 + 447928 * 2 ^ 59
def prefixEnd_447928 : Nat := 4983230072969 + 3 ^ 40 * 447928 * 2
def baseEnd_447928 : Nat := 34074424089959809383707

theorem tailTrace_447928 : CollatzResearch.WordTrace tailWord_447928 prefixEnd_447928 34074424089959809383707 := by
  unfold tailWord_447928
  simp only [CollatzResearch.WordTrace]
  refine ⟨8168638160620415428516219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10891517547493887238021625 8168638160620415428516219)
  ·
    refine ⟨12252957240930623142774329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8168638160620415428516219 12252957240930623142774329)
    ·
      refine ⟨9189717930697967357080747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12252957240930623142774329 9189717930697967357080747)
      ·
        refine ⟨13784576896046951035621121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9189717930697967357080747 13784576896046951035621121)
        ·
          refine ⟨10338432672035213276715841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13784576896046951035621121 10338432672035213276715841)
          ·
            refine ⟨7753824504026409957536881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10338432672035213276715841 7753824504026409957536881)
            ·
              refine ⟨5815368378019807468152661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7753824504026409957536881 5815368378019807468152661)
              ·
                refine ⟨34074424089959809383707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5815368378019807468152661 34074424089959809383707)
                ·
                  rfl

theorem cell21_447928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_447928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447928 prefixEnd_447928 := by exact prefixLift 447928
  have htrace : WordTrace (prefixWord ++ tailWord_447928) baseStart_447928 baseEnd_447928 := by
    simpa [prefixWord, tailWord_447928, baseEnd_447928] using wordTrace_append hprefix tailTrace_447928
  have hstable : (prefixWord ++ tailWord_447928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447928).length < 2 ^ (prefixWord ++ tailWord_447928).sum := by decide
  have hdescent : baseEnd_447928 < baseStart_447928 := by decide
  rcases family_descends (prefixWord ++ tailWord_447928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447948 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_447948 : Nat := 118140960795 + 447948 * 2 ^ 59
def prefixEnd_447948 : Nat := 4983230072969 + 3 ^ 40 * 447948 * 2
def baseEnd_447948 : Nat := 102227836542363837817747

theorem tailTrace_447948 : CollatzResearch.WordTrace tailWord_447948 prefixEnd_447948 102227836542363837817747 := by
  unfold tailWord_447948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8169002890584187136380249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10892003854112249515173665 8169002890584187136380249)
  ·
    refine ⟨6126752167938140352285187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8169002890584187136380249 6126752167938140352285187)
    ·
      refine ⟨9190128251907210528427781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6126752167938140352285187 9190128251907210528427781)
      ·
        refine ⟨1723149047232601974080209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9190128251907210528427781 1723149047232601974080209)
        ·
          refine ⟨1292361785424451480560157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1723149047232601974080209 1292361785424451480560157)
          ·
            refine ⟨484635669534169305210059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1292361785424451480560157 484635669534169305210059)
            ·
              refine ⟨726953504301253957815089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484635669534169305210059 726953504301253957815089)
              ·
                refine ⟨545215128225940468361317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726953504301253957815089 545215128225940468361317)
                ·
                  refine ⟨102227836542363837817747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545215128225940468361317 102227836542363837817747)
                  ·
                    rfl

theorem cell21_447948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_447948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_447948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_447948 prefixEnd_447948 := by exact prefixLift 447948
  have htrace : WordTrace (prefixWord ++ tailWord_447948) baseStart_447948 baseEnd_447948 := by
    simpa [prefixWord, tailWord_447948, baseEnd_447948] using wordTrace_append hprefix tailTrace_447948
  have hstable : (prefixWord ++ tailWord_447948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447948).length < 2 ^ (prefixWord ++ tailWord_447948).sum := by decide
  have hdescent : baseEnd_447948 < baseStart_447948 := by decide
  rcases family_descends (prefixWord ++ tailWord_447948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448010 : List Nat := [3, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_448010 : Nat := 118140960795 + 448010 * 2 ^ 59
def prefixEnd_448010 : Nat := 4983230072969 + 3 ^ 40 * 448010 * 2
def baseEnd_448010 : Nat := 102241985787065507784287

theorem tailTrace_448010 : CollatzResearch.WordTrace tailWord_448010 prefixEnd_448010 102241985787065507784287 := by
  unfold tailWord_448010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4085066776735939715379371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10893511404629172574344989 4085066776735939715379371)
  ·
    refine ⟨6127600165103909573069057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4085066776735939715379371 6127600165103909573069057)
    ·
      refine ⟨4595700123827932179801793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6127600165103909573069057 4595700123827932179801793)
      ·
        refine ⟨3446775092870949134851345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4595700123827932179801793 3446775092870949134851345)
        ·
          refine ⟨2585081319653211851138509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3446775092870949134851345 2585081319653211851138509)
          ·
            refine ⟨969405494869954444176941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2585081319653211851138509 969405494869954444176941)
            ·
              refine ⟨363527060576232916566353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 969405494869954444176941 363527060576232916566353)
              ·
                refine ⟨272645295432174687424765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363527060576232916566353 272645295432174687424765)
                ·
                  refine ⟨102241985787065507784287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272645295432174687424765 102241985787065507784287)
                  ·
                    rfl

theorem cell21_448010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_448010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448010 prefixEnd_448010 := by exact prefixLift 448010
  have htrace : WordTrace (prefixWord ++ tailWord_448010) baseStart_448010 baseEnd_448010 := by
    simpa [prefixWord, tailWord_448010, baseEnd_448010] using wordTrace_append hprefix tailTrace_448010
  have hstable : (prefixWord ++ tailWord_448010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448010).length < 2 ^ (prefixWord ++ tailWord_448010).sum := by decide
  have hdescent : baseEnd_448010 < baseStart_448010 := by decide
  rcases family_descends (prefixWord ++ tailWord_448010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448021 : List Nat := [1, 3, 2, 1, 3, 3, 2, 6]
def baseStart_448021 : Nat := 118140960795 + 448021 * 2 ^ 59
def prefixEnd_448021 : Nat := 4983230072969 + 3 ^ 40 * 448021 * 2
def baseEnd_448021 : Nat := 34081498712310644366977

theorem tailTrace_448021 : CollatzResearch.WordTrace tailWord_448021 prefixEnd_448021 34081498712310644366977 := by
  unfold tailWord_448021
  simp only [CollatzResearch.WordTrace]
  refine ⟨16340668309903907740167917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10893778873269271826778611 16340668309903907740167917)
  ·
    refine ⟨6127750616213965402562969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16340668309903907740167917 6127750616213965402562969)
    ·
      refine ⟨4595812962160474051922227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6127750616213965402562969 4595812962160474051922227)
      ·
        refine ⟨6893719443240711077883341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595812962160474051922227 6893719443240711077883341)
        ·
          refine ⟨2585144791215266654206253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6893719443240711077883341 2585144791215266654206253)
          ·
            refine ⟨969429296705724995327345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2585144791215266654206253 969429296705724995327345)
            ·
              refine ⟨727071972529293746495509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969429296705724995327345 727071972529293746495509)
              ·
                refine ⟨34081498712310644366977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 727071972529293746495509 34081498712310644366977)
                ·
                  rfl

theorem cell21_448021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 6].length) (baseStart_448021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448021 prefixEnd_448021 := by exact prefixLift 448021
  have htrace : WordTrace (prefixWord ++ tailWord_448021) baseStart_448021 baseEnd_448021 := by
    simpa [prefixWord, tailWord_448021, baseEnd_448021] using wordTrace_append hprefix tailTrace_448021
  have hstable : (prefixWord ++ tailWord_448021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448021).length < 2 ^ (prefixWord ++ tailWord_448021).sum := by decide
  have hdescent : baseEnd_448021 < baseStart_448021 := by decide
  rcases family_descends (prefixWord ++ tailWord_448021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448097 : List Nat := [1, 2, 3, 1, 1, 3, 5, 5]
def baseStart_448097 : Nat := 118140960795 + 448097 * 2 ^ 59
def prefixEnd_448097 : Nat := 4983230072969 + 3 ^ 40 * 448097 * 2
def baseEnd_448097 : Nat := 34087280124124229944703

theorem tailTrace_448097 : CollatzResearch.WordTrace tailWord_448097 prefixEnd_448097 34087280124124229944703 := by
  unfold tailWord_448097
  simp only [CollatzResearch.WordTrace]
  refine ⟨16343440257628572719934545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10895626838419048479956363 16343440257628572719934545)
  ·
    refine ⟨12257580193221429539950909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16343440257628572719934545 12257580193221429539950909)
    ·
      refine ⟨4596592572458036077481591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12257580193221429539950909 4596592572458036077481591)
      ·
        refine ⟨6894888858687054116222387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596592572458036077481591 6894888858687054116222387)
        ·
          refine ⟨10342333288030581174333581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6894888858687054116222387 10342333288030581174333581)
          ·
            refine ⟨3878374983011467940375093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10342333288030581174333581 3878374983011467940375093)
            ·
              refine ⟨363597654657325119410165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3878374983011467940375093 363597654657325119410165)
              ·
                refine ⟨34087280124124229944703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 363597654657325119410165 34087280124124229944703)
                ·
                  rfl

theorem cell21_448097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 5].length) (baseStart_448097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448097 prefixEnd_448097 := by exact prefixLift 448097
  have htrace : WordTrace (prefixWord ++ tailWord_448097) baseStart_448097 baseEnd_448097 := by
    simpa [prefixWord, tailWord_448097, baseEnd_448097] using wordTrace_append hprefix tailTrace_448097
  have hstable : (prefixWord ++ tailWord_448097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448097).length < 2 ^ (prefixWord ++ tailWord_448097).sum := by decide
  have hdescent : baseEnd_448097 < baseStart_448097 := by decide
  rcases family_descends (prefixWord ++ tailWord_448097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448128 : List Nat := [2, 1, 1, 2, 1, 4, 1, 6, 3]
def baseStart_448128 : Nat := 118140960795 + 448128 * 2 ^ 59
def prefixEnd_448128 : Nat := 4983230072969 + 3 ^ 40 * 448128 * 2
def baseEnd_448128 : Nat := 102268914994723524817379

theorem tailTrace_448128 : CollatzResearch.WordTrace tailWord_448128 prefixEnd_448128 102268914994723524817379 := by
  unfold tailWord_448128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172285460258132507156519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10896380613677510009542025 8172285460258132507156519)
  ·
    refine ⟨12258428190387198760734779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8172285460258132507156519 12258428190387198760734779)
    ·
      refine ⟨18387642285580798141102169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12258428190387198760734779 18387642285580798141102169)
      ·
        refine ⟨13790731714185598605826627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18387642285580798141102169 13790731714185598605826627)
        ·
          refine ⟨20686097571278397908739941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13790731714185598605826627 20686097571278397908739941)
          ·
            refine ⟨3878643294614699607888739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20686097571278397908739941 3878643294614699607888739)
            ·
              refine ⟨5817964941922049411833109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878643294614699607888739 5817964941922049411833109)
              ·
                refine ⟨272717106652596066179677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5817964941922049411833109 272717106652596066179677)
                ·
                  refine ⟨102268914994723524817379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272717106652596066179677 102268914994723524817379)
                  ·
                    rfl

theorem cell21_448128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_448128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448128 prefixEnd_448128 := by exact prefixLift 448128
  have htrace : WordTrace (prefixWord ++ tailWord_448128) baseStart_448128 baseEnd_448128 := by
    simpa [prefixWord, tailWord_448128, baseEnd_448128] using wordTrace_append hprefix tailTrace_448128
  have hstable : (prefixWord ++ tailWord_448128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448128).length < 2 ^ (prefixWord ++ tailWord_448128).sum := by decide
  have hdescent : baseEnd_448128 < baseStart_448128 := by decide
  rcases family_descends (prefixWord ++ tailWord_448128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448148 : List Nat := [2, 4, 2, 2, 3, 1, 2, 5]
def baseStart_448148 : Nat := 118140960795 + 448148 * 2 ^ 59
def prefixEnd_448148 : Nat := 4983230072969 + 3 ^ 40 * 448148 * 2
def baseEnd_448148 : Nat := 34091159755735978161335

theorem tailTrace_448148 : CollatzResearch.WordTrace tailWord_448148 prefixEnd_448148 34091159755735978161335 := by
  unfold tailWord_448148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172650190221904215020549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10896866920295872286694065 8172650190221904215020549)
  ·
    refine ⟨1532371910666607040316353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8172650190221904215020549 1532371910666607040316353)
    ·
      refine ⟨1149278932999955280237265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1532371910666607040316353 1149278932999955280237265)
      ·
        refine ⟨861959199749966460177949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1149278932999955280237265 861959199749966460177949)
        ·
          refine ⟨323234699906237422566731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 861959199749966460177949 323234699906237422566731)
          ·
            refine ⟨484852049859356133850097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323234699906237422566731 484852049859356133850097)
            ·
              refine ⟨363639037394517100387573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484852049859356133850097 363639037394517100387573)
              ·
                refine ⟨34091159755735978161335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 363639037394517100387573 34091159755735978161335)
                ·
                  rfl

theorem cell21_448148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_448148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448148 prefixEnd_448148 := by exact prefixLift 448148
  have htrace : WordTrace (prefixWord ++ tailWord_448148) baseStart_448148 baseEnd_448148 := by
    simpa [prefixWord, tailWord_448148, baseEnd_448148] using wordTrace_append hprefix tailTrace_448148
  have hstable : (prefixWord ++ tailWord_448148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448148).length < 2 ^ (prefixWord ++ tailWord_448148).sum := by decide
  have hdescent : baseEnd_448148 < baseStart_448148 := by decide
  rcases family_descends (prefixWord ++ tailWord_448148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448232 : List Nat := [2, 1, 4, 1, 3, 10]
def baseStart_448232 : Nat := 118140960795 + 448232 * 2 ^ 59
def prefixEnd_448232 : Nat := 4983230072969 + 3 ^ 40 * 448232 * 2
def baseEnd_448232 : Nat := 3788616637468239077179

theorem tailTrace_448232 : CollatzResearch.WordTrace tailWord_448232 prefixEnd_448232 3788616637468239077179 := by
  unfold tailWord_448232
  simp only [CollatzResearch.WordTrace]
  refine ⟨8174182056069745388049475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10898909408092993850732633 8174182056069745388049475)
  ·
    refine ⟨12261273084104618082074213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8174182056069745388049475 12261273084104618082074213)
    ·
      refine ⟨2298988703269615890388915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12261273084104618082074213 2298988703269615890388915)
      ·
        refine ⟨3448483054904423835583373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2298988703269615890388915 3448483054904423835583373)
        ·
          refine ⟨1293181145589158938343765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3448483054904423835583373 1293181145589158938343765)
          ·
            refine ⟨3788616637468239077179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1293181145589158938343765 3788616637468239077179)
            ·
              rfl

theorem cell21_448232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 10].length) (baseStart_448232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448232 prefixEnd_448232 := by exact prefixLift 448232
  have htrace : WordTrace (prefixWord ++ tailWord_448232) baseStart_448232 baseEnd_448232 := by
    simpa [prefixWord, tailWord_448232, baseEnd_448232] using wordTrace_append hprefix tailTrace_448232
  have hstable : (prefixWord ++ tailWord_448232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448232).length < 2 ^ (prefixWord ++ tailWord_448232).sum := by decide
  have hdescent : baseEnd_448232 < baseStart_448232 := by decide
  rcases family_descends (prefixWord ++ tailWord_448232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448280 : List Nat := [2, 1, 2, 3, 1, 1, 3, 5, 3]
def baseStart_448280 : Nat := 118140960795 + 448280 * 2 ^ 59
def prefixEnd_448280 : Nat := 4983230072969 + 3 ^ 40 * 448280 * 2
def baseEnd_448280 : Nat := 102303603465605038283735

theorem tailTrace_448280 : CollatzResearch.WordTrace tailWord_448280 prefixEnd_448280 102303603465605038283735 := by
  unfold tailWord_448280
  simp only [CollatzResearch.WordTrace]
  refine ⟨8175057407982797486923147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10900076543977063315897529 8175057407982797486923147)
  ·
    refine ⟨12262586111974196230384721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8175057407982797486923147 12262586111974196230384721)
    ·
      refine ⟨9196939583980647172788541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12262586111974196230384721 9196939583980647172788541)
      ·
        refine ⟨3448852343992742689795703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9196939583980647172788541 3448852343992742689795703)
        ·
          refine ⟨5173278515989114034693555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448852343992742689795703 5173278515989114034693555)
          ·
            refine ⟨7759917773983671052040333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173278515989114034693555 7759917773983671052040333)
            ·
              refine ⟨2909969165243876644515125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7759917773983671052040333 2909969165243876644515125)
              ·
                refine ⟨272809609241613435423293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2909969165243876644515125 272809609241613435423293)
                ·
                  refine ⟨102303603465605038283735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272809609241613435423293 102303603465605038283735)
                  ·
                    rfl

theorem cell21_448280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_448280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448280 prefixEnd_448280 := by exact prefixLift 448280
  have htrace : WordTrace (prefixWord ++ tailWord_448280) baseStart_448280 baseEnd_448280 := by
    simpa [prefixWord, tailWord_448280, baseEnd_448280] using wordTrace_append hprefix tailTrace_448280
  have hstable : (prefixWord ++ tailWord_448280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448280).length < 2 ^ (prefixWord ++ tailWord_448280).sum := by decide
  have hdescent : baseEnd_448280 < baseStart_448280 := by decide
  rcases family_descends (prefixWord ++ tailWord_448280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448286 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_448286 : Nat := 118140960795 + 448286 * 2 ^ 59
def prefixEnd_448286 : Nat := 4983230072969 + 3 ^ 40 * 448286 * 2
def baseEnd_448286 : Nat := 102304972747350361183723

theorem tailTrace_448286 : CollatzResearch.WordTrace tailWord_448286 prefixEnd_448286 102304972747350361183723 := by
  unfold tailWord_448286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043791706742982249820589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10900222435962571999043141 2043791706742982249820589)
  ·
    refine ⟨766421890028618343682721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2043791706742982249820589 766421890028618343682721)
    ·
      refine ⟨574816417521463757762041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 766421890028618343682721 574816417521463757762041)
      ·
        refine ⟨431112313141097818321531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574816417521463757762041 431112313141097818321531)
        ·
          refine ⟨646668469711646727482297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431112313141097818321531 646668469711646727482297)
          ·
            refine ⟨485001352283735045611723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646668469711646727482297 485001352283735045611723)
            ·
              refine ⟨727502028425602568417585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485001352283735045611723 727502028425602568417585)
              ·
                refine ⟨545626521319201926313189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727502028425602568417585 545626521319201926313189)
                ·
                  refine ⟨102304972747350361183723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545626521319201926313189 102304972747350361183723)
                  ·
                    rfl

theorem cell21_448286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_448286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448286 prefixEnd_448286 := by exact prefixLift 448286
  have htrace : WordTrace (prefixWord ++ tailWord_448286) baseStart_448286 baseEnd_448286 := by
    simpa [prefixWord, tailWord_448286, baseEnd_448286] using wordTrace_append hprefix tailTrace_448286
  have hstable : (prefixWord ++ tailWord_448286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448286).length < 2 ^ (prefixWord ++ tailWord_448286).sum := by decide
  have hdescent : baseEnd_448286 < baseStart_448286 := by decide
  rcases family_descends (prefixWord ++ tailWord_448286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448353 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 6]
def baseStart_448353 : Nat := 118140960795 + 448353 * 2 ^ 59
def prefixEnd_448353 : Nat := 4983230072969 + 3 ^ 40 * 448353 * 2
def baseEnd_448353 : Nat := 102320263060173133566919

theorem tailTrace_448353 : CollatzResearch.WordTrace tailWord_448353 prefixEnd_448353 102320263060173133566919 := by
  unfold tailWord_448353
  simp only [CollatzResearch.WordTrace]
  refine ⟨16352777344701128441253713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10901851563134085627502475 16352777344701128441253713)
  ·
    refine ⟨12264583008525846330940285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16352777344701128441253713 12264583008525846330940285)
    ·
      refine ⟨4599218628197192374102607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12264583008525846330940285 4599218628197192374102607)
      ·
        refine ⟨6898827942295788561153911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599218628197192374102607 6898827942295788561153911)
        ·
          refine ⟨10348241913443682841730867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6898827942295788561153911 10348241913443682841730867)
          ·
            refine ⟨15522362870165524262596301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10348241913443682841730867 15522362870165524262596301)
            ·
              refine ⟨5820886076312071598473613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15522362870165524262596301 5820886076312071598473613)
              ·
                refine ⟨2182832278617026849427605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820886076312071598473613 2182832278617026849427605)
                ·
                  refine ⟨102320263060173133566919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2182832278617026849427605 102320263060173133566919)
                  ·
                    rfl

theorem cell21_448353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_448353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448353 prefixEnd_448353 := by exact prefixLift 448353
  have htrace : WordTrace (prefixWord ++ tailWord_448353) baseStart_448353 baseEnd_448353 := by
    simpa [prefixWord, tailWord_448353, baseEnd_448353] using wordTrace_append hprefix tailTrace_448353
  have hstable : (prefixWord ++ tailWord_448353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448353).length < 2 ^ (prefixWord ++ tailWord_448353).sum := by decide
  have hdescent : baseEnd_448353 < baseStart_448353 := by decide
  rcases family_descends (prefixWord ++ tailWord_448353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448362 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_448362 : Nat := 118140960795 + 448362 * 2 ^ 59
def prefixEnd_448362 : Nat := 4983230072969 + 3 ^ 40 * 448362 * 2
def baseEnd_448362 : Nat := 102322316982791117916901

theorem tailTrace_448362 : CollatzResearch.WordTrace tailWord_448362 prefixEnd_448362 102322316982791117916901 := by
  unfold tailWord_448362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088276400417130744582835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10902070401112348652220893 4088276400417130744582835)
  ·
    refine ⟨6132414600625696116874253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4088276400417130744582835 6132414600625696116874253)
    ·
      refine ⟨2299655475234636043827845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6132414600625696116874253 2299655475234636043827845)
      ·
        refine ⟨431185401606494258217721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2299655475234636043827845 431185401606494258217721)
        ·
          refine ⟨323389051204870693663291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431185401606494258217721 323389051204870693663291)
          ·
            refine ⟨485083576807306040494937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323389051204870693663291 485083576807306040494937)
            ·
              refine ⟨363812682605479530371203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485083576807306040494937 363812682605479530371203)
              ·
                refine ⟨545719023908219295556805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363812682605479530371203 545719023908219295556805)
                ·
                  refine ⟨102322316982791117916901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545719023908219295556805 102322316982791117916901)
                  ·
                    rfl

theorem cell21_448362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_448362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448362 prefixEnd_448362 := by exact prefixLift 448362
  have htrace : WordTrace (prefixWord ++ tailWord_448362) baseStart_448362 baseEnd_448362 := by
    simpa [prefixWord, tailWord_448362, baseEnd_448362] using wordTrace_append hprefix tailTrace_448362
  have hstable : (prefixWord ++ tailWord_448362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448362).length < 2 ^ (prefixWord ++ tailWord_448362).sum := by decide
  have hdescent : baseEnd_448362 < baseStart_448362 := by decide
  rcases family_descends (prefixWord ++ tailWord_448362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448418 : List Nat := [3, 3, 1, 2, 3, 2, 1, 6]
def baseStart_448418 : Nat := 118140960795 + 448418 * 2 ^ 59
def prefixEnd_448418 : Nat := 4983230072969 + 3 ^ 40 * 448418 * 2
def baseEnd_448418 : Nat := 34111698981915821661151

theorem tailTrace_448418 : CollatzResearch.WordTrace tailWord_448418 prefixEnd_448418 34111698981915821661151 := by
  unfold tailWord_448418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088787022366411135592477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10903432059643763028246605 4088787022366411135592477)
  ·
    refine ⟨1533295133387404175847179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4088787022366411135592477 1533295133387404175847179)
    ·
      refine ⟨2299942700081106263770769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533295133387404175847179 2299942700081106263770769)
      ·
        refine ⟨1724957025060829697828077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2299942700081106263770769 1724957025060829697828077)
        ·
          refine ⟨646858884397811136685529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1724957025060829697828077 646858884397811136685529)
          ·
            refine ⟨485144163298358352514147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646858884397811136685529 485144163298358352514147)
            ·
              refine ⟨727716244947537528771221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485144163298358352514147 727716244947537528771221)
              ·
                refine ⟨34111698981915821661151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 727716244947537528771221 34111698981915821661151)
                ·
                  rfl

theorem cell21_448418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_448418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448418 prefixEnd_448418 := by exact prefixLift 448418
  have htrace : WordTrace (prefixWord ++ tailWord_448418) baseStart_448418 baseEnd_448418 := by
    simpa [prefixWord, tailWord_448418, baseEnd_448418] using wordTrace_append hprefix tailTrace_448418
  have hstable : (prefixWord ++ tailWord_448418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448418).length < 2 ^ (prefixWord ++ tailWord_448418).sum := by decide
  have hdescent : baseEnd_448418 < baseStart_448418 := by decide
  rcases family_descends (prefixWord ++ tailWord_448418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448460 : List Nat := [2, 2, 1, 4, 1, 3, 8]
def baseStart_448460 : Nat := 118140960795 + 448460 * 2 ^ 59
def prefixEnd_448460 : Nat := 4983230072969 + 3 ^ 40 * 448460 * 2
def baseEnd_448460 : Nat := 11371631324218302809263

theorem tailTrace_448460 : CollatzResearch.WordTrace tailWord_448460 prefixEnd_448460 11371631324218302809263 := by
  unfold tailWord_448460
  simp only [CollatzResearch.WordTrace]
  refine ⟨8178339977656742857699417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10904453303542323810265889 8178339977656742857699417)
  ·
    refine ⟨6133754983242557143274563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8178339977656742857699417 6133754983242557143274563)
    ·
      refine ⟨9200632474863835714911845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6133754983242557143274563 9200632474863835714911845)
      ·
        refine ⟨1725118589036969196545971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9200632474863835714911845 1725118589036969196545971)
        ·
          refine ⟨2587677883555453794818957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725118589036969196545971 2587677883555453794818957)
          ·
            refine ⟨970379206333295173057109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2587677883555453794818957 970379206333295173057109)
            ·
              refine ⟨11371631324218302809263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 970379206333295173057109 11371631324218302809263)
              ·
                rfl

theorem cell21_448460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 8].length) (baseStart_448460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448460 prefixEnd_448460 := by exact prefixLift 448460
  have htrace : WordTrace (prefixWord ++ tailWord_448460) baseStart_448460 baseEnd_448460 := by
    simpa [prefixWord, tailWord_448460, baseEnd_448460] using wordTrace_append hprefix tailTrace_448460
  have hstable : (prefixWord ++ tailWord_448460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448460).length < 2 ^ (prefixWord ++ tailWord_448460).sum := by decide
  have hdescent : baseEnd_448460 < baseStart_448460 := by decide
  rcases family_descends (prefixWord ++ tailWord_448460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448494 : List Nat := [4, 1, 2, 1, 3, 3, 2, 5]
def baseStart_448494 : Nat := 118140960795 + 448494 * 2 ^ 59
def prefixEnd_448494 : Nat := 4983230072969 + 3 ^ 40 * 448494 * 2
def baseEnd_448494 : Nat := 34117480393729407238877

theorem tailTrace_448494 : CollatzResearch.WordTrace tailWord_448494 prefixEnd_448494 34117480393729407238877 := by
  unfold tailWord_448494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2044740004648788690267067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10905280024793539681424357 2044740004648788690267067)
  ·
    refine ⟨3067110006973183035400601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2044740004648788690267067 3067110006973183035400601)
    ·
      refine ⟨2300332505229887276550451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3067110006973183035400601 2300332505229887276550451)
      ·
        refine ⟨3450498757844830914825677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300332505229887276550451 3450498757844830914825677)
        ·
          refine ⟨1293937034191811593059629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3450498757844830914825677 1293937034191811593059629)
          ·
            refine ⟨485226387821929347397361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1293937034191811593059629 485226387821929347397361)
            ·
              refine ⟨363919790866447010548021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485226387821929347397361 363919790866447010548021)
              ·
                refine ⟨34117480393729407238877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 363919790866447010548021 34117480393729407238877)
                ·
                  rfl

theorem cell21_448494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_448494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448494 prefixEnd_448494 := by exact prefixLift 448494
  have htrace : WordTrace (prefixWord ++ tailWord_448494) baseStart_448494 baseEnd_448494 := by
    simpa [prefixWord, tailWord_448494, baseEnd_448494] using wordTrace_append hprefix tailTrace_448494
  have hstable : (prefixWord ++ tailWord_448494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448494).length < 2 ^ (prefixWord ++ tailWord_448494).sum := by decide
  have hdescent : baseEnd_448494 < baseStart_448494 := by decide
  rcases family_descends (prefixWord ++ tailWord_448494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448505 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 6]
def baseStart_448505 : Nat := 118140960795 + 448505 * 2 ^ 59
def prefixEnd_448505 : Nat := 4983230072969 + 3 ^ 40 * 448505 * 2
def baseEnd_448505 : Nat := 102354951531054647033275

theorem tailTrace_448505 : CollatzResearch.WordTrace tailWord_448505 prefixEnd_448505 102354951531054647033275 := by
  unfold tailWord_448505
  simp only [CollatzResearch.WordTrace]
  refine ⟨16358321240150458400786969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10905547493433638933857979 16358321240150458400786969)
  ·
    refine ⟨12268740930112843800590227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16358321240150458400786969 12268740930112843800590227)
    ·
      refine ⟨18403111395169265700885341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12268740930112843800590227 18403111395169265700885341)
      ·
        refine ⟨6901166773188474637832003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18403111395169265700885341 6901166773188474637832003)
        ·
          refine ⟨10351750159782711956748005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901166773188474637832003 10351750159782711956748005)
          ·
            refine ⟨1940953154959258491890251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10351750159782711956748005 1940953154959258491890251)
            ·
              refine ⟨2911429732438887737835377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940953154959258491890251 2911429732438887737835377)
              ·
                refine ⟨2183572299329165803376533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2911429732438887737835377 2183572299329165803376533)
                ·
                  refine ⟨102354951531054647033275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2183572299329165803376533 102354951531054647033275)
                  ·
                    rfl

theorem cell21_448505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_448505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448505 prefixEnd_448505 := by exact prefixLift 448505
  have htrace : WordTrace (prefixWord ++ tailWord_448505) baseStart_448505 baseEnd_448505 := by
    simpa [prefixWord, tailWord_448505, baseEnd_448505] using wordTrace_append hprefix tailTrace_448505
  have hstable : (prefixWord ++ tailWord_448505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448505).length < 2 ^ (prefixWord ++ tailWord_448505).sum := by decide
  have hdescent : baseEnd_448505 < baseStart_448505 := by decide
  rcases family_descends (prefixWord ++ tailWord_448505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448536 : List Nat := [2, 1, 2, 3, 2, 1, 4, 6]
def baseStart_448536 : Nat := 118140960795 + 448536 * 2 ^ 59
def prefixEnd_448536 : Nat := 4983230072969 + 3 ^ 40 * 448536 * 2
def baseEnd_448536 : Nat := 34120675384468494005515

theorem tailTrace_448536 : CollatzResearch.WordTrace tailWord_448536 prefixEnd_448536 34120675384468494005515 := by
  unfold tailWord_448536
  simp only [CollatzResearch.WordTrace]
  refine ⟨8179725951519075347582731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10906301268692100463443641 8179725951519075347582731)
  ·
    refine ⟨12269588927278613021374097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8179725951519075347582731 12269588927278613021374097)
    ·
      refine ⟨9202191695458959766030573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12269588927278613021374097 9202191695458959766030573)
      ·
        refine ⟨3450821885797109912261465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9202191695458959766030573 3450821885797109912261465)
        ·
          refine ⟨2588116414347832434196099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3450821885797109912261465 2588116414347832434196099)
          ·
            refine ⟨3882174621521748651294149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588116414347832434196099 3882174621521748651294149)
            ·
              refine ⟨727907741535327872117653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3882174621521748651294149 727907741535327872117653)
              ·
                refine ⟨34120675384468494005515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 727907741535327872117653 34120675384468494005515)
                ·
                  rfl

theorem cell21_448536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_448536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448536 prefixEnd_448536 := by exact prefixLift 448536
  have htrace : WordTrace (prefixWord ++ tailWord_448536) baseStart_448536 baseEnd_448536 := by
    simpa [prefixWord, tailWord_448536, baseEnd_448536] using wordTrace_append hprefix tailTrace_448536
  have hstable : (prefixWord ++ tailWord_448536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448536).length < 2 ^ (prefixWord ++ tailWord_448536).sum := by decide
  have hdescent : baseEnd_448536 < baseStart_448536 := by decide
  rcases family_descends (prefixWord ++ tailWord_448536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448643 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 5]
def baseStart_448643 : Nat := 118140960795 + 448643 * 2 ^ 59
def prefixEnd_448643 : Nat := 4983230072969 + 3 ^ 40 * 448643 * 2
def baseEnd_448643 : Nat := 102386445011197073732993

theorem tailTrace_448643 : CollatzResearch.WordTrace tailWord_448643 prefixEnd_448643 102386445011197073732993 := by
  unfold tailWord_448643
  simp only [CollatzResearch.WordTrace]
  refine ⟨16363354513650507969310583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10908903009100338646207055 16363354513650507969310583)
  ·
    refine ⟨24545031770475761953965875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16363354513650507969310583 24545031770475761953965875)
    ·
      refine ⟨36817547655713642930948813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24545031770475761953965875 36817547655713642930948813)
      ·
        refine ⟨13806580370892616099105805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36817547655713642930948813 13806580370892616099105805)
        ·
          refine ⟨5177467639084731037164677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13806580370892616099105805 5177467639084731037164677)
          ·
            refine ⟨970775182328387069468377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5177467639084731037164677 970775182328387069468377)
            ·
              refine ⟨728081386746290302101283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970775182328387069468377 728081386746290302101283)
              ·
                refine ⟨1092122080119435453151925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728081386746290302101283 1092122080119435453151925)
                ·
                  refine ⟨102386445011197073732993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1092122080119435453151925 102386445011197073732993)
                  ·
                    rfl

theorem cell21_448643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 5].length) (baseStart_448643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448643 prefixEnd_448643 := by exact prefixLift 448643
  have htrace : WordTrace (prefixWord ++ tailWord_448643) baseStart_448643 baseEnd_448643 := by
    simpa [prefixWord, tailWord_448643, baseEnd_448643] using wordTrace_append hprefix tailTrace_448643
  have hstable : (prefixWord ++ tailWord_448643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448643).length < 2 ^ (prefixWord ++ tailWord_448643).sum := by decide
  have hdescent : baseEnd_448643 < baseStart_448643 := by decide
  rcases family_descends (prefixWord ++ tailWord_448643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448674 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_448674 : Nat := 118140960795 + 448674 * 2 ^ 59
def prefixEnd_448674 : Nat := 4983230072969 + 3 ^ 40 * 448674 * 2
def baseEnd_448674 : Nat := 102393519633547908716263

theorem tailTrace_448674 : CollatzResearch.WordTrace tailWord_448674 prefixEnd_448674 102393519633547908716263 := by
  unfold tailWord_448674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091121294134550065922269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10909656784358800175792717 4091121294134550065922269)
  ·
    refine ⟨1534170485300456274720851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4091121294134550065922269 1534170485300456274720851)
    ·
      refine ⟨2301255727950684412081277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534170485300456274720851 2301255727950684412081277)
      ·
        refine ⟨862970897981506654530479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2301255727950684412081277 862970897981506654530479)
        ·
          refine ⟨1294456346972259981795719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862970897981506654530479 1294456346972259981795719)
          ·
            refine ⟨1941684520458389972693579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294456346972259981795719 1941684520458389972693579)
            ·
              refine ⟨2912526780687584959040369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941684520458389972693579 2912526780687584959040369)
              ·
                refine ⟨2184395085515688719280277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912526780687584959040369 2184395085515688719280277)
                ·
                  refine ⟨102393519633547908716263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2184395085515688719280277 102393519633547908716263)
                  ·
                    rfl

theorem cell21_448674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_448674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448674 prefixEnd_448674 := by exact prefixLift 448674
  have htrace : WordTrace (prefixWord ++ tailWord_448674) baseStart_448674 baseEnd_448674 := by
    simpa [prefixWord, tailWord_448674, baseEnd_448674] using wordTrace_append hprefix tailTrace_448674
  have hstable : (prefixWord ++ tailWord_448674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448674).length < 2 ^ (prefixWord ++ tailWord_448674).sum := by decide
  have hdescent : baseEnd_448674 < baseStart_448674 := by decide
  rcases family_descends (prefixWord ++ tailWord_448674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448708 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_448708 : Nat := 118140960795 + 448708 * 2 ^ 59
def prefixEnd_448708 : Nat := 4983230072969 + 3 ^ 40 * 448708 * 2
def baseEnd_448708 : Nat := 102401278896771405149527

theorem tailTrace_448708 : CollatzResearch.WordTrace tailWord_448708 prefixEnd_448708 102401278896771405149527 := by
  unfold tailWord_448708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182862629207512035213389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10910483505610016046951185 8182862629207512035213389)
  ·
    refine ⟨3068573485952817013205021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8182862629207512035213389 3068573485952817013205021)
    ·
      refine ⟨1150715057232306379951883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3068573485952817013205021 1150715057232306379951883)
      ·
        refine ⟨1726072585848459569927825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150715057232306379951883 1726072585848459569927825)
        ·
          refine ⟨1294554439386344677445869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1726072585848459569927825 1294554439386344677445869)
          ·
            refine ⟨485457914769879254042201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1294554439386344677445869 485457914769879254042201)
            ·
              refine ⟨364093436077409440531651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485457914769879254042201 364093436077409440531651)
              ·
                refine ⟨546140154116114160797477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364093436077409440531651 546140154116114160797477)
                ·
                  refine ⟨102401278896771405149527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 546140154116114160797477 102401278896771405149527)
                  ·
                    rfl

theorem cell21_448708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_448708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448708 prefixEnd_448708 := by exact prefixLift 448708
  have htrace : WordTrace (prefixWord ++ tailWord_448708) baseStart_448708 baseEnd_448708 := by
    simpa [prefixWord, tailWord_448708, baseEnd_448708] using wordTrace_append hprefix tailTrace_448708
  have hstable : (prefixWord ++ tailWord_448708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448708).length < 2 ^ (prefixWord ++ tailWord_448708).sum := by decide
  have hdescent : baseEnd_448708 < baseStart_448708 := by decide
  rcases family_descends (prefixWord ++ tailWord_448708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448764 : List Nat := [2, 2, 2, 1, 4, 1, 3, 6]
def baseStart_448764 : Nat := 118140960795 + 448764 * 2 ^ 59
def prefixEnd_448764 : Nat := 4983230072969 + 3 ^ 40 * 448764 * 2
def baseEnd_448764 : Nat := 34138019619909250738693

theorem tailTrace_448764 : CollatzResearch.WordTrace tailWord_448764 prefixEnd_448764 34138019619909250738693 := by
  unfold tailWord_448764
  simp only [CollatzResearch.WordTrace]
  refine ⟨8183883873106072817232673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10911845164141430422976897 8183883873106072817232673)
  ·
    refine ⟨6137912904829554612924505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8183883873106072817232673 6137912904829554612924505)
    ·
      refine ⟨4603434678622165959693379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6137912904829554612924505 4603434678622165959693379)
      ·
        refine ⟨6905152017933248939540069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4603434678622165959693379 6905152017933248939540069)
        ·
          refine ⟨1294716003362484176163763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6905152017933248939540069 1294716003362484176163763)
          ·
            refine ⟨1942074005043726264245645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294716003362484176163763 1942074005043726264245645)
            ·
              refine ⟨728277751891397349092117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942074005043726264245645 728277751891397349092117)
              ·
                refine ⟨34138019619909250738693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 728277751891397349092117 34138019619909250738693)
                ·
                  rfl

theorem cell21_448764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_448764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448764 prefixEnd_448764 := by exact prefixLift 448764
  have htrace : WordTrace (prefixWord ++ tailWord_448764) baseStart_448764 baseEnd_448764 := by
    simpa [prefixWord, tailWord_448764, baseEnd_448764] using wordTrace_append hprefix tailTrace_448764
  have hstable : (prefixWord ++ tailWord_448764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448764).length < 2 ^ (prefixWord ++ tailWord_448764).sum := by decide
  have hdescent : baseEnd_448764 < baseStart_448764 := by decide
  rcases family_descends (prefixWord ++ tailWord_448764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448778 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_448778 : Nat := 118140960795 + 448778 * 2 ^ 59
def prefixEnd_448778 : Nat := 4983230072969 + 3 ^ 40 * 448778 * 2
def baseEnd_448778 : Nat := 102417253850466838982717

theorem tailTrace_448778 : CollatzResearch.WordTrace tailWord_448778 prefixEnd_448778 102417253850466838982717 := by
  unfold tailWord_448778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092069592040356506368747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10912185578774284016983325 4092069592040356506368747)
  ·
    refine ⟨6138104388060534759553121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4092069592040356506368747 6138104388060534759553121)
    ·
      refine ⟨4603578291045401069664841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6138104388060534759553121 4603578291045401069664841)
      ·
        refine ⟨3452683718284050802248631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4603578291045401069664841 3452683718284050802248631)
        ·
          refine ⟨5179025577426076203372947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452683718284050802248631 5179025577426076203372947)
          ·
            refine ⟨7768538366139114305059421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179025577426076203372947 7768538366139114305059421)
            ·
              refine ⟨2913201887302167864397283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7768538366139114305059421 2913201887302167864397283)
              ·
                refine ⟨4369802830953251796595925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913201887302167864397283 4369802830953251796595925)
                ·
                  refine ⟨102417253850466838982717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4369802830953251796595925 102417253850466838982717)
                  ·
                    rfl

theorem cell21_448778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_448778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448778 prefixEnd_448778 := by exact prefixLift 448778
  have htrace : WordTrace (prefixWord ++ tailWord_448778) baseStart_448778 baseEnd_448778 := by
    simpa [prefixWord, tailWord_448778, baseEnd_448778] using wordTrace_append hprefix tailTrace_448778
  have hstable : (prefixWord ++ tailWord_448778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448778).length < 2 ^ (prefixWord ++ tailWord_448778).sum := by decide
  have hdescent : baseEnd_448778 < baseStart_448778 := by decide
  rcases family_descends (prefixWord ++ tailWord_448778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448795 : List Nat := [1, 1, 1, 1, 1, 1, 7, 5, 3]
def baseStart_448795 : Nat := 118140960795 + 448795 * 2 ^ 59
def prefixEnd_448795 : Nat := 4983230072969 + 3 ^ 40 * 448795 * 2
def baseEnd_448795 : Nat := 102421133482078587199349

theorem tailTrace_448795 : CollatzResearch.WordTrace tailWord_448795 prefixEnd_448795 102421133482078587199349 := by
  unfold tailWord_448795
  simp only [CollatzResearch.WordTrace]
  refine ⟨16368898409099837928843839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10912598939399891952562559 16368898409099837928843839)
  ·
    refine ⟨24553347613649756893265759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16368898409099837928843839 24553347613649756893265759)
    ·
      refine ⟨36830021420474635339898639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24553347613649756893265759 36830021420474635339898639)
      ·
        refine ⟨55245032130711953009847959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36830021420474635339898639 55245032130711953009847959)
        ·
          refine ⟨82867548196067929514771939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55245032130711953009847959 82867548196067929514771939)
          ·
            refine ⟨124301322294101894272157909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82867548196067929514771939 124301322294101894272157909)
            ·
              refine ⟨2913312241268013147003701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 124301322294101894272157909 2913312241268013147003701)
              ·
                refine ⟨273123022618876232531597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2913312241268013147003701 273123022618876232531597)
                ·
                  refine ⟨102421133482078587199349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273123022618876232531597 102421133482078587199349)
                  ·
                    rfl

theorem cell21_448795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 3].length) (baseStart_448795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448795 prefixEnd_448795 := by exact prefixLift 448795
  have htrace : WordTrace (prefixWord ++ tailWord_448795) baseStart_448795 baseEnd_448795 := by
    simpa [prefixWord, tailWord_448795, baseEnd_448795] using wordTrace_append hprefix tailTrace_448795
  have hstable : (prefixWord ++ tailWord_448795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448795).length < 2 ^ (prefixWord ++ tailWord_448795).sum := by decide
  have hdescent : baseEnd_448795 < baseStart_448795 := by decide
  rcases family_descends (prefixWord ++ tailWord_448795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448840 : List Nat := [2, 1, 3, 1, 1, 2, 6, 5]
def baseStart_448840 : Nat := 118140960795 + 448840 * 2 ^ 59
def prefixEnd_448840 : Nat := 4983230072969 + 3 ^ 40 * 448840 * 2
def baseEnd_448840 : Nat := 34143801031722836316419

theorem tailTrace_448840 : CollatzResearch.WordTrace tailWord_448840 prefixEnd_448840 34143801031722836316419 := by
  unfold tailWord_448840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8185269846968405307115987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10913693129291207076154649 8185269846968405307115987)
  ·
    refine ⟨12277904770452607960673981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8185269846968405307115987 12277904770452607960673981)
    ·
      refine ⟨4604214288919727985252743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12277904770452607960673981 4604214288919727985252743)
      ·
        refine ⟨6906321433379591977879115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604214288919727985252743 6906321433379591977879115)
        ·
          refine ⟨10359482150069387966818673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6906321433379591977879115 10359482150069387966818673)
          ·
            refine ⟨7769611612552040975114005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10359482150069387966818673 7769611612552040975114005)
            ·
              refine ⟨364200544338376920708469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7769611612552040975114005 364200544338376920708469)
              ·
                refine ⟨34143801031722836316419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364200544338376920708469 34143801031722836316419)
                ·
                  rfl

theorem cell21_448840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_448840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448840 prefixEnd_448840 := by exact prefixLift 448840
  have htrace : WordTrace (prefixWord ++ tailWord_448840) baseStart_448840 baseEnd_448840 := by
    simpa [prefixWord, tailWord_448840, baseEnd_448840] using wordTrace_append hprefix tailTrace_448840
  have hstable : (prefixWord ++ tailWord_448840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448840).length < 2 ^ (prefixWord ++ tailWord_448840).sum := by decide
  have hdescent : baseEnd_448840 < baseStart_448840 := by decide
  rcases family_descends (prefixWord ++ tailWord_448840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448871 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 5]
def baseStart_448871 : Nat := 118140960795 + 448871 * 2 ^ 59
def prefixEnd_448871 : Nat := 4983230072969 + 3 ^ 40 * 448871 * 2
def baseEnd_448871 : Nat := 102438477717519343932527

theorem tailTrace_448871 : CollatzResearch.WordTrace tailWord_448871 prefixEnd_448871 102438477717519343932527 := by
  unfold tailWord_448871
  simp only [CollatzResearch.WordTrace]
  refine ⟨16371670356824502908610467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10914446904549668605740311 16371670356824502908610467)
  ·
    refine ⟨24557505535236754362915701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16371670356824502908610467 24557505535236754362915701)
    ·
      refine ⟨2302266143928445721523347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24557505535236754362915701 2302266143928445721523347)
      ·
        refine ⟨3453399215892668582285021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302266143928445721523347 3453399215892668582285021)
        ·
          refine ⟨1295024705959750718356883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3453399215892668582285021 1295024705959750718356883)
          ·
            refine ⟨1942537058939626077535325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295024705959750718356883 1942537058939626077535325)
            ·
              refine ⟨728451397102359779075747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942537058939626077535325 728451397102359779075747)
              ·
                refine ⟨1092677095653539668613621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728451397102359779075747 1092677095653539668613621)
                ·
                  refine ⟨102438477717519343932527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1092677095653539668613621 102438477717519343932527)
                  ·
                    rfl

theorem cell21_448871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 5].length) (baseStart_448871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448871 prefixEnd_448871 := by exact prefixLift 448871
  have htrace : WordTrace (prefixWord ++ tailWord_448871) baseStart_448871 baseEnd_448871 := by
    simpa [prefixWord, tailWord_448871, baseEnd_448871] using wordTrace_append hprefix tailTrace_448871
  have hstable : (prefixWord ++ tailWord_448871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448871).length < 2 ^ (prefixWord ++ tailWord_448871).sum := by decide
  have hdescent : baseEnd_448871 < baseStart_448871 := by decide
  rcases family_descends (prefixWord ++ tailWord_448871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448916 : List Nat := [2, 4, 2, 1, 3, 9]
def baseStart_448916 : Nat := 118140960795 + 448916 * 2 ^ 59
def prefixEnd_448916 : Nat := 4983230072969 + 3 ^ 40 * 448916 * 2
def baseEnd_448916 : Nat := 3794398049281824654905

theorem tailTrace_448916 : CollatzResearch.WordTrace tailWord_448916 prefixEnd_448916 3794398049281824654905 := by
  unfold tailWord_448916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8186655820830737796999301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10915541094440983729332401 8186655820830737796999301)
  ·
    refine ⟨1534997966405763336937369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8186655820830737796999301 1534997966405763336937369)
    ·
      refine ⟨1151248474804322502703027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1534997966405763336937369 1151248474804322502703027)
      ·
        refine ⟨1726872712206483754054541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151248474804322502703027 1726872712206483754054541)
        ·
          refine ⟨647577267077431407770453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1726872712206483754054541 647577267077431407770453)
          ·
            refine ⟨3794398049281824654905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 647577267077431407770453 3794398049281824654905)
            ·
              rfl

theorem cell21_448916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 9].length) (baseStart_448916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448916 prefixEnd_448916 := by exact prefixLift 448916
  have htrace : WordTrace (prefixWord ++ tailWord_448916) baseStart_448916 baseEnd_448916 := by
    simpa [prefixWord, tailWord_448916, baseEnd_448916] using wordTrace_append hprefix tailTrace_448916
  have hstable : (prefixWord ++ tailWord_448916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448916).length < 2 ^ (prefixWord ++ tailWord_448916).sum := by decide
  have hdescent : baseEnd_448916 < baseStart_448916 := by decide
  rcases family_descends (prefixWord ++ tailWord_448916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448995 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 4]
def baseStart_448995 : Nat := 118140960795 + 448995 * 2 ^ 59
def prefixEnd_448995 : Nat := 4983230072969 + 3 ^ 40 * 448995 * 2
def baseEnd_448995 : Nat := 102466776206922683865607

theorem tailTrace_448995 : CollatzResearch.WordTrace tailWord_448995 prefixEnd_448995 102466776206922683865607 := by
  unfold tailWord_448995
  simp only [CollatzResearch.WordTrace]
  refine ⟨16376193008375272086124439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10917462005583514724082959 16376193008375272086124439)
  ·
    refine ⟨24564289512562908129186659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16376193008375272086124439 24564289512562908129186659)
    ·
      refine ⟨36846434268844362193779989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24564289512562908129186659 36846434268844362193779989)
      ·
        refine ⟨1727176606352079477833437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36846434268844362193779989 1727176606352079477833437)
        ·
          refine ⟨647691227382029804187539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1727176606352079477833437 647691227382029804187539)
          ·
            refine ⟨971536841073044706281309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647691227382029804187539 971536841073044706281309)
            ·
              refine ⟨364326315402391764855491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 971536841073044706281309 364326315402391764855491)
              ·
                refine ⟨546489473103587647283237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364326315402391764855491 546489473103587647283237)
                ·
                  refine ⟨102466776206922683865607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 546489473103587647283237 102466776206922683865607)
                  ·
                    rfl

theorem cell21_448995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 4].length) (baseStart_448995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_448995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_448995 prefixEnd_448995 := by exact prefixLift 448995
  have htrace : WordTrace (prefixWord ++ tailWord_448995) baseStart_448995 baseEnd_448995 := by
    simpa [prefixWord, tailWord_448995, baseEnd_448995] using wordTrace_append hprefix tailTrace_448995
  have hstable : (prefixWord ++ tailWord_448995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448995).length < 2 ^ (prefixWord ++ tailWord_448995).sum := by decide
  have hdescent : baseEnd_448995 < baseStart_448995 := by decide
  rcases family_descends (prefixWord ++ tailWord_448995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449026 : List Nat := [3, 4, 1, 2, 3, 1, 7]
def baseStart_449026 : Nat := 118140960795 + 449026 * 2 ^ 59
def prefixEnd_449026 : Nat := 4983230072969 + 3 ^ 40 * 449026 * 2
def baseEnd_449026 : Nat := 11385983425474835427653

theorem tailTrace_449026 : CollatzResearch.WordTrace tailWord_449026 prefixEnd_449026 11385983425474835427653 := by
  unfold tailWord_449026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094330917815741095125733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10918215780841976253668621 4094330917815741095125733)
  ·
    refine ⟨767687047090451455336075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4094330917815741095125733 767687047090451455336075)
    ·
      refine ⟨1151530570635677183004113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 767687047090451455336075 1151530570635677183004113)
      ·
        refine ⟨863647927976757887253085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1151530570635677183004113 863647927976757887253085)
        ·
          refine ⟨323867972991284207719907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 863647927976757887253085 323867972991284207719907)
          ·
            refine ⟨485801959486926311579861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323867972991284207719907 485801959486926311579861)
            ·
              refine ⟨11385983425474835427653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 485801959486926311579861 11385983425474835427653)
              ·
                rfl

theorem cell21_449026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 7].length) (baseStart_449026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449026 prefixEnd_449026 := by exact prefixLift 449026
  have htrace : WordTrace (prefixWord ++ tailWord_449026) baseStart_449026 baseEnd_449026 := by
    simpa [prefixWord, tailWord_449026, baseEnd_449026] using wordTrace_append hprefix tailTrace_449026
  have hstable : (prefixWord ++ tailWord_449026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449026).length < 2 ^ (prefixWord ++ tailWord_449026).sum := by decide
  have hdescent : baseEnd_449026 < baseStart_449026 := by decide
  rcases family_descends (prefixWord ++ tailWord_449026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449096 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_449096 : Nat := 118140960795 + 449096 * 2 ^ 59
def prefixEnd_449096 : Nat := 4983230072969 + 3 ^ 40 * 449096 * 2
def baseEnd_449096 : Nat := 102489825782968952682067

theorem tailTrace_449096 : CollatzResearch.WordTrace tailWord_449096 prefixEnd_449096 102489825782968952682067 := by
  unfold tailWord_449096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189938390504683167775571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10919917854006244223700761 8189938390504683167775571)
  ·
    refine ⟨12284907585757024751663357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8189938390504683167775571 12284907585757024751663357)
    ·
      refine ⟨4606840344658884281873759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12284907585757024751663357 4606840344658884281873759)
      ·
        refine ⟨6910260516988326422810639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606840344658884281873759 6910260516988326422810639)
        ·
          refine ⟨10365390775482489634215959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6910260516988326422810639 10365390775482489634215959)
          ·
            refine ⟨15548086163223734451323939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10365390775482489634215959 15548086163223734451323939)
            ·
              refine ⟨23322129244835601676985909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15548086163223734451323939 23322129244835601676985909)
              ·
                refine ⟨2186449616703337657217429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23322129244835601676985909 2186449616703337657217429)
                ·
                  refine ⟨102489825782968952682067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2186449616703337657217429 102489825782968952682067)
                  ·
                    rfl

theorem cell21_449096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_449096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449096 prefixEnd_449096 := by exact prefixLift 449096
  have htrace : WordTrace (prefixWord ++ tailWord_449096) baseStart_449096 baseEnd_449096 := by
    simpa [prefixWord, tailWord_449096, baseEnd_449096] using wordTrace_append hprefix tailTrace_449096
  have hstable : (prefixWord ++ tailWord_449096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449096).length < 2 ^ (prefixWord ++ tailWord_449096).sum := by decide
  have hdescent : baseEnd_449096 < baseStart_449096 := by decide
  rcases family_descends (prefixWord ++ tailWord_449096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449178 : List Nat := [3, 1, 1, 6, 1, 2, 2, 5]
def baseStart_449178 : Nat := 118140960795 + 449178 * 2 ^ 59
def prefixEnd_449178 : Nat := 4983230072969 + 3 ^ 40 * 449178 * 2
def baseEnd_449178 : Nat := 34169513100051677438411

theorem tailTrace_449178 : CollatzResearch.WordTrace tailWord_449178 prefixEnd_449178 34169513100051677438411 := by
  unfold tailWord_449178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4095716891678073585009047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10921911711141529560024125 4095716891678073585009047)
  ·
    refine ⟨6143575337517110377513571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4095716891678073585009047 6143575337517110377513571)
    ·
      refine ⟨9215363006275665566270357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6143575337517110377513571 9215363006275665566270357)
      ·
        refine ⟨431970140919171823418923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9215363006275665566270357 431970140919171823418923)
        ·
          refine ⟨647955211378757735128385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431970140919171823418923 647955211378757735128385)
          ·
            refine ⟨485966408534068301346289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647955211378757735128385 485966408534068301346289)
            ·
              refine ⟨364474806400551226009717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485966408534068301346289 364474806400551226009717)
              ·
                refine ⟨34169513100051677438411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364474806400551226009717 34169513100051677438411)
                ·
                  rfl

theorem cell21_449178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_449178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449178 prefixEnd_449178 := by exact prefixLift 449178
  have htrace : WordTrace (prefixWord ++ tailWord_449178) baseStart_449178 baseEnd_449178 := by
    simpa [prefixWord, tailWord_449178, baseEnd_449178] using wordTrace_append hprefix tailTrace_449178
  have hstable : (prefixWord ++ tailWord_449178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449178).length < 2 ^ (prefixWord ++ tailWord_449178).sum := by decide
  have hdescent : baseEnd_449178 < baseStart_449178 := by decide
  rcases family_descends (prefixWord ++ tailWord_449178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449203 : List Nat := [1, 1, 1, 2, 3, 6, 7]
def baseStart_449203 : Nat := 118140960795 + 449203 * 2 ^ 59
def prefixEnd_449203 : Nat := 4983230072969 + 3 ^ 40 * 449203 * 2
def baseEnd_449203 : Nat := 11390471626751171599835

theorem tailTrace_449203 : CollatzResearch.WordTrace tailWord_449203 prefixEnd_449203 11390471626751171599835 := by
  unfold tailWord_449203
  simp only [CollatzResearch.WordTrace]
  refine ⟨16383779391621723609696263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10922519594414482406464175 16383779391621723609696263)
  ·
    refine ⟨24575669087432585414544395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16383779391621723609696263 24575669087432585414544395)
    ·
      refine ⟨36863503631148878121816593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24575669087432585414544395 36863503631148878121816593)
      ·
        refine ⟨27647627723361658591362445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36863503631148878121816593 27647627723361658591362445)
        ·
          refine ⟨10367860396260621971760917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27647627723361658591362445 10367860396260621971760917)
          ·
            refine ⟨485993456074716654926293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10367860396260621971760917 485993456074716654926293)
            ·
              refine ⟨11390471626751171599835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 485993456074716654926293 11390471626751171599835)
              ·
                rfl

theorem cell21_449203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 7].length) (baseStart_449203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449203 prefixEnd_449203 := by exact prefixLift 449203
  have htrace : WordTrace (prefixWord ++ tailWord_449203) baseStart_449203 baseEnd_449203 := by
    simpa [prefixWord, tailWord_449203, baseEnd_449203] using wordTrace_append hprefix tailTrace_449203
  have hstable : (prefixWord ++ tailWord_449203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449203).length < 2 ^ (prefixWord ++ tailWord_449203).sum := by decide
  have hdescent : baseEnd_449203 < baseStart_449203 := by decide
  rcases family_descends (prefixWord ++ tailWord_449203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449220 : List Nat := [2, 3, 3, 1, 1, 3, 2, 6]
def baseStart_449220 : Nat := 118140960795 + 449220 * 2 ^ 59
def prefixEnd_449220 : Nat := 4983230072969 + 3 ^ 40 * 449220 * 2
def baseEnd_449220 : Nat := 34172708090790764205049

theorem tailTrace_449220 : CollatzResearch.WordTrace tailWord_449220 prefixEnd_449220 34172708090790764205049 := by
  unfold tailWord_449220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8192199716280067756532557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10922932955040090342043409 8192199716280067756532557)
  ·
    refine ⟨3072074893605025408699709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8192199716280067756532557 3072074893605025408699709)
    ·
      refine ⟨1152028085101884528262391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3072074893605025408699709 1152028085101884528262391)
      ·
        refine ⟨1728042127652826792393587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152028085101884528262391 1728042127652826792393587)
        ·
          refine ⟨2592063191479240188590381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728042127652826792393587 2592063191479240188590381)
          ·
            refine ⟨972023696804715070721393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2592063191479240188590381 972023696804715070721393)
            ·
              refine ⟨729017772603536303041045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972023696804715070721393 729017772603536303041045)
              ·
                refine ⟨34172708090790764205049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 729017772603536303041045 34172708090790764205049)
                ·
                  rfl

theorem cell21_449220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_449220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449220 prefixEnd_449220 := by exact prefixLift 449220
  have htrace : WordTrace (prefixWord ++ tailWord_449220) baseStart_449220 baseEnd_449220 := by
    simpa [prefixWord, tailWord_449220, baseEnd_449220] using wordTrace_append hprefix tailTrace_449220
  have hstable : (prefixWord ++ tailWord_449220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449220).length < 2 ^ (prefixWord ++ tailWord_449220).sum := by decide
  have hdescent : baseEnd_449220 < baseStart_449220 := by decide
  rcases family_descends (prefixWord ++ tailWord_449220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449265 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 4]
def baseStart_449265 : Nat := 118140960795 + 449265 * 2 ^ 59
def prefixEnd_449265 : Nat := 4983230072969 + 3 ^ 40 * 449265 * 2
def baseEnd_449265 : Nat := 102528393885462214365055

theorem tailTrace_449265 : CollatzResearch.WordTrace tailWord_449265 prefixEnd_449265 102528393885462214365055 := by
  unfold tailWord_449265
  simp only [CollatzResearch.WordTrace]
  refine ⟨16386040717397108198453249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10924027144931405465635499 16386040717397108198453249)
  ·
    refine ⟨12289530538047831148839937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16386040717397108198453249 12289530538047831148839937)
    ·
      refine ⟨9217147903535873361629953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12289530538047831148839937 9217147903535873361629953)
      ·
        refine ⟨6912860927651905021222465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9217147903535873361629953 6912860927651905021222465)
        ·
          refine ⟨5184645695738928765916849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6912860927651905021222465 5184645695738928765916849)
          ·
            refine ⟨3888484271804196574437637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5184645695738928765916849 3888484271804196574437637)
            ·
              refine ⟨729090800963286857707057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3888484271804196574437637 729090800963286857707057)
              ·
                refine ⟨546818100722465143280293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729090800963286857707057 546818100722465143280293)
                ·
                  refine ⟨102528393885462214365055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 546818100722465143280293 102528393885462214365055)
                  ·
                    rfl

theorem cell21_449265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_449265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449265 prefixEnd_449265 := by exact prefixLift 449265
  have htrace : WordTrace (prefixWord ++ tailWord_449265) baseStart_449265 baseEnd_449265 := by
    simpa [prefixWord, tailWord_449265, baseEnd_449265] using wordTrace_append hprefix tailTrace_449265
  have hstable : (prefixWord ++ tailWord_449265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449265).length < 2 ^ (prefixWord ++ tailWord_449265).sum := by decide
  have hdescent : baseEnd_449265 < baseStart_449265 := by decide
  rcases family_descends (prefixWord ++ tailWord_449265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449282 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_449282 : Nat := 118140960795 + 449282 * 2 ^ 59
def prefixEnd_449282 : Nat := 4983230072969 + 3 ^ 40 * 449282 * 2
def baseEnd_449282 : Nat := 102532273517073962581687

theorem tailTrace_449282 : CollatzResearch.WordTrace tailWord_449282 prefixEnd_449282 102532273517073962581687 := by
  unfold tailWord_449282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096665189583880025455525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10924440505557013401214733 4096665189583880025455525)
  ·
    refine ⟨768124723046977504772911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4096665189583880025455525 768124723046977504772911)
    ·
      refine ⟨1152187084570466257159367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768124723046977504772911 1152187084570466257159367)
      ·
        refine ⟨1728280626855699385739051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152187084570466257159367 1728280626855699385739051)
        ·
          refine ⟨2592420940283549078608577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728280626855699385739051 2592420940283549078608577)
          ·
            refine ⟨1944315705212661808956433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2592420940283549078608577 1944315705212661808956433)
            ·
              refine ⟨1458236778909496356717325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944315705212661808956433 1458236778909496356717325)
              ·
                refine ⟨546838792091061133768997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1458236778909496356717325 546838792091061133768997)
                ·
                  refine ⟨102532273517073962581687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 546838792091061133768997 102532273517073962581687)
                  ·
                    rfl

theorem cell21_449282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_449282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449282 prefixEnd_449282 := by exact prefixLift 449282
  have htrace : WordTrace (prefixWord ++ tailWord_449282) baseStart_449282 baseEnd_449282 := by
    simpa [prefixWord, tailWord_449282, baseEnd_449282] using wordTrace_append hprefix tailTrace_449282
  have hstable : (prefixWord ++ tailWord_449282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449282).length < 2 ^ (prefixWord ++ tailWord_449282).sum := by decide
  have hdescent : baseEnd_449282 < baseStart_449282 := by decide
  rcases family_descends (prefixWord ++ tailWord_449282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449324 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_449324 : Nat := 118140960795 + 449324 * 2 ^ 59
def prefixEnd_449324 : Nat := 4983230072969 + 3 ^ 40 * 449324 * 2
def baseEnd_449324 : Nat := 102541858489291222881601

theorem tailTrace_449324 : CollatzResearch.WordTrace tailWord_449324 prefixEnd_449324 102541858489291222881601 := by
  unfold tailWord_449324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8194096312091680637425513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10925461749455574183234017 8194096312091680637425513)
  ·
    refine ⟨6145572234068760478069135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8194096312091680637425513 6145572234068760478069135)
    ·
      refine ⟨9218358351103140717103703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6145572234068760478069135 9218358351103140717103703)
      ·
        refine ⟨13827537526654711075655555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9218358351103140717103703 13827537526654711075655555)
        ·
          refine ⟨20741306289982066613483333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13827537526654711075655555 20741306289982066613483333)
          ·
            refine ⟨3888994929371637490028125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20741306289982066613483333 3888994929371637490028125)
            ·
              refine ⟨1458373098514364058760547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3888994929371637490028125 1458373098514364058760547)
              ·
                refine ⟨2187559647771546088140821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458373098514364058760547 2187559647771546088140821)
                ·
                  refine ⟨102541858489291222881601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2187559647771546088140821 102541858489291222881601)
                  ·
                    rfl

theorem cell21_449324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_449324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449324 prefixEnd_449324 := by exact prefixLift 449324
  have htrace : WordTrace (prefixWord ++ tailWord_449324) baseStart_449324 baseEnd_449324 := by
    simpa [prefixWord, tailWord_449324, baseEnd_449324] using wordTrace_append hprefix tailTrace_449324
  have hstable : (prefixWord ++ tailWord_449324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449324).length < 2 ^ (prefixWord ++ tailWord_449324).sum := by decide
  have hdescent : baseEnd_449324 < baseStart_449324 := by decide
  rcases family_descends (prefixWord ++ tailWord_449324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449361 : List Nat := [1, 2, 2, 1, 7, 1, 1, 3, 3]
def baseStart_449361 : Nat := 118140960795 + 449361 * 2 ^ 59
def prefixEnd_449361 : Nat := 4983230072969 + 3 ^ 40 * 449361 * 2
def baseEnd_449361 : Nat := 102550302393387380764859

theorem tailTrace_449361 : CollatzResearch.WordTrace tailWord_449361 prefixEnd_449361 102550302393387380764859 := by
  unfold tailWord_449361
  simp only [CollatzResearch.WordTrace]
  refine ⟨16389542125049316593947937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10926361416699544395965291 16389542125049316593947937)
  ·
    refine ⟨12292156593786987445460953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16389542125049316593947937 12292156593786987445460953)
    ·
      refine ⟨9219117445340240584095715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12292156593786987445460953 9219117445340240584095715)
      ·
        refine ⟨13828676168010360876143573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9219117445340240584095715 13828676168010360876143573)
        ·
          refine ⟨324109597687742833034615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13828676168010360876143573 324109597687742833034615)
          ·
            refine ⟨486164396531614249551923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324109597687742833034615 486164396531614249551923)
            ·
              refine ⟨729246594797421374327885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486164396531614249551923 729246594797421374327885)
              ·
                refine ⟨273467473049033015372957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 729246594797421374327885 273467473049033015372957)
                ·
                  refine ⟨102550302393387380764859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273467473049033015372957 102550302393387380764859)
                  ·
                    rfl

theorem cell21_449361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_449361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449361 prefixEnd_449361 := by exact prefixLift 449361
  have htrace : WordTrace (prefixWord ++ tailWord_449361) baseStart_449361 baseEnd_449361 := by
    simpa [prefixWord, tailWord_449361, baseEnd_449361] using wordTrace_append hprefix tailTrace_449361
  have hstable : (prefixWord ++ tailWord_449361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449361).length < 2 ^ (prefixWord ++ tailWord_449361).sum := by decide
  have hdescent : baseEnd_449361 < baseStart_449361 := by decide
  rcases family_descends (prefixWord ++ tailWord_449361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449372 : List Nat := [2, 2, 4, 2, 1, 3, 7]
def baseStart_449372 : Nat := 118140960795 + 449372 * 2 ^ 59
def prefixEnd_449372 : Nat := 4983230072969 + 3 ^ 40 * 449372 * 2
def baseEnd_449372 : Nat := 11394756971472645120167

theorem tailTrace_449372 : CollatzResearch.WordTrace tailWord_449372 prefixEnd_449372 11394756971472645120167 := by
  unfold tailWord_449372
  simp only [CollatzResearch.WordTrace]
  refine ⟨8194971664004732736299185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10926628885339643648398913 8194971664004732736299185)
  ·
    refine ⟨6146228748003549552224389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8194971664004732736299185 6146228748003549552224389)
    ·
      refine ⟨1152417890250665541042073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6146228748003549552224389 1152417890250665541042073)
      ·
        refine ⟨864313417687999155781555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1152417890250665541042073 864313417687999155781555)
        ·
          refine ⟨1296470126531998733672333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864313417687999155781555 1296470126531998733672333)
          ·
            refine ⟨486176297449499525127125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1296470126531998733672333 486176297449499525127125)
            ·
              refine ⟨11394756971472645120167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 486176297449499525127125 11394756971472645120167)
              ·
                rfl

theorem cell21_449372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 7].length) (baseStart_449372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449372 prefixEnd_449372 := by exact prefixLift 449372
  have htrace : WordTrace (prefixWord ++ tailWord_449372) baseStart_449372 baseEnd_449372 := by
    simpa [prefixWord, tailWord_449372, baseEnd_449372] using wordTrace_append hprefix tailTrace_449372
  have hstable : (prefixWord ++ tailWord_449372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449372).length < 2 ^ (prefixWord ++ tailWord_449372).sum := by decide
  have hdescent : baseEnd_449372 < baseStart_449372 := by decide
  rcases family_descends (prefixWord ++ tailWord_449372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449434 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_449434 : Nat := 118140960795 + 449434 * 2 ^ 59
def prefixEnd_449434 : Nat := 4983230072969 + 3 ^ 40 * 449434 * 2
def baseEnd_449434 : Nat := 102566961987955476048043

theorem tailTrace_449434 : CollatzResearch.WordTrace tailWord_449434 prefixEnd_449434 102566961987955476048043 := by
  unfold tailWord_449434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098051163446212515338839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10928136435856566707570237 4098051163446212515338839)
  ·
    refine ⟨6147076745169318773008259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4098051163446212515338839 6147076745169318773008259)
    ·
      refine ⟨9220615117753978159512389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6147076745169318773008259 9220615117753978159512389)
      ·
        refine ⟨1728865334578870904908573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9220615117753978159512389 1728865334578870904908573)
        ·
          refine ⟨648324500467076589340715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1728865334578870904908573 648324500467076589340715)
          ·
            refine ⟨972486750700614884011073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648324500467076589340715 972486750700614884011073)
            ·
              refine ⟨729365063025461163008305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972486750700614884011073 729365063025461163008305)
              ·
                refine ⟨547023797269095872256229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729365063025461163008305 547023797269095872256229)
                ·
                  refine ⟨102566961987955476048043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547023797269095872256229 102566961987955476048043)
                  ·
                    rfl

theorem cell21_449434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_449434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449434 prefixEnd_449434 := by exact prefixLift 449434
  have htrace : WordTrace (prefixWord ++ tailWord_449434) baseStart_449434 baseEnd_449434 := by
    simpa [prefixWord, tailWord_449434, baseEnd_449434] using wordTrace_append hprefix tailTrace_449434
  have hstable : (prefixWord ++ tailWord_449434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449434).length < 2 ^ (prefixWord ++ tailWord_449434).sum := by decide
  have hdescent : baseEnd_449434 < baseStart_449434 := by decide
  rcases family_descends (prefixWord ++ tailWord_449434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449485 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 4]
def baseStart_449485 : Nat := 118140960795 + 449485 * 2 ^ 59
def prefixEnd_449485 : Nat := 4983230072969 + 3 ^ 40 * 449485 * 2
def baseEnd_449485 : Nat := 102578600882790720697939

theorem tailTrace_449485 : CollatzResearch.WordTrace tailWord_449485 prefixEnd_449485 102578600882790720697939 := by
  unfold tailWord_449485
  simp only [CollatzResearch.WordTrace]
  refine ⟨16394064776600085771461909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10929376517733390514307939 16394064776600085771461909)
  ·
    refine ⟨768471786403129020537277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16394064776600085771461909 768471786403129020537277)
    ·
      refine ⟨288176919901173382701479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 768471786403129020537277 288176919901173382701479)
      ·
        refine ⟨432265379851760074052219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288176919901173382701479 432265379851760074052219)
        ·
          refine ⟨648398069777640111078329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432265379851760074052219 648398069777640111078329)
          ·
            refine ⟨486298552333230083308747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648398069777640111078329 486298552333230083308747)
            ·
              refine ⟨729447828499845124963121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486298552333230083308747 729447828499845124963121)
              ·
                refine ⟨547085871374883843722341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729447828499845124963121 547085871374883843722341)
                ·
                  refine ⟨102578600882790720697939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547085871374883843722341 102578600882790720697939)
                  ·
                    rfl

theorem cell21_449485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_449485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449485 prefixEnd_449485 := by exact prefixLift 449485
  have htrace : WordTrace (prefixWord ++ tailWord_449485) baseStart_449485 baseEnd_449485 := by
    simpa [prefixWord, tailWord_449485, baseEnd_449485] using wordTrace_append hprefix tailTrace_449485
  have hstable : (prefixWord ++ tailWord_449485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449485).length < 2 ^ (prefixWord ++ tailWord_449485).sum := by decide
  have hdescent : baseEnd_449485 < baseStart_449485 := by decide
  rcases family_descends (prefixWord ++ tailWord_449485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449493 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 6]
def baseStart_449493 : Nat := 118140960795 + 449493 * 2 ^ 59
def prefixEnd_449493 : Nat := 4983230072969 + 3 ^ 40 * 449493 * 2
def baseEnd_449493 : Nat := 102580426591784484564589

theorem tailTrace_449493 : CollatzResearch.WordTrace tailWord_449493 prefixEnd_449493 102580426591784484564589 := by
  unfold tailWord_449493
  simp only [CollatzResearch.WordTrace]
  refine ⟨16394356560571103137753133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10929571040380735425168755 16394356560571103137753133)
  ·
    refine ⟨6147883710214163676657425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16394356560571103137753133 6147883710214163676657425)
    ·
      refine ⟨4610912782660622757493069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6147883710214163676657425 4610912782660622757493069)
      ·
        refine ⟨1729092293497733534059901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4610912782660622757493069 1729092293497733534059901)
        ·
          refine ⟨648409610061650075272463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1729092293497733534059901 648409610061650075272463)
          ·
            refine ⟨972614415092475112908695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648409610061650075272463 972614415092475112908695)
            ·
              refine ⟨1458921622638712669363043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972614415092475112908695 1458921622638712669363043)
              ·
                refine ⟨2188382433958069004044565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458921622638712669363043 2188382433958069004044565)
                ·
                  refine ⟨102580426591784484564589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2188382433958069004044565 102580426591784484564589)
                  ·
                    rfl

theorem cell21_449493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_449493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449493 prefixEnd_449493 := by exact prefixLift 449493
  have htrace : WordTrace (prefixWord ++ tailWord_449493) baseStart_449493 baseEnd_449493 := by
    simpa [prefixWord, tailWord_449493, baseEnd_449493] using wordTrace_append hprefix tailTrace_449493
  have hstable : (prefixWord ++ tailWord_449493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449493).length < 2 ^ (prefixWord ++ tailWord_449493).sum := by decide
  have hdescent : baseEnd_449493 < baseStart_449493 := by decide
  rcases family_descends (prefixWord ++ tailWord_449493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449569 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 4]
def baseStart_449569 : Nat := 118140960795 + 449569 * 2 ^ 59
def prefixEnd_449569 : Nat := 4983230072969 + 3 ^ 40 * 449569 * 2
def baseEnd_449569 : Nat := 102597770827225241297767

theorem tailTrace_449569 : CollatzResearch.WordTrace tailWord_449569 prefixEnd_449569 102597770827225241297767 := by
  unfold tailWord_449569
  simp only [CollatzResearch.WordTrace]
  refine ⟨16397128508295768117519761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10931419005530512078346507 16397128508295768117519761)
  ·
    refine ⟨12297846381221826088139821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16397128508295768117519761 12297846381221826088139821)
    ·
      refine ⟨4611692392958184783052433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12297846381221826088139821 4611692392958184783052433)
      ·
        refine ⟨3458769294718638587289325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4611692392958184783052433 3458769294718638587289325)
        ·
          refine ⟨1297038485519489470233497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3458769294718638587289325 1297038485519489470233497)
          ·
            refine ⟨972778864139617102675123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297038485519489470233497 972778864139617102675123)
            ·
              refine ⟨1459168296209425654012685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972778864139617102675123 1459168296209425654012685)
              ·
                refine ⟨547188111078534620254757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1459168296209425654012685 547188111078534620254757)
                ·
                  refine ⟨102597770827225241297767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547188111078534620254757 102597770827225241297767)
                  ·
                    rfl

theorem cell21_449569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_449569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449569 prefixEnd_449569 := by exact prefixLift 449569
  have htrace : WordTrace (prefixWord ++ tailWord_449569) baseStart_449569 baseEnd_449569 := by
    simpa [prefixWord, tailWord_449569, baseEnd_449569] using wordTrace_append hprefix tailTrace_449569
  have hstable : (prefixWord ++ tailWord_449569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449569).length < 2 ^ (prefixWord ++ tailWord_449569).sum := by decide
  have hdescent : baseEnd_449569 < baseStart_449569 := by decide
  rcases family_descends (prefixWord ++ tailWord_449569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449606 : List Nat := [6, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_449606 : Nat := 118140960795 + 449606 * 2 ^ 59
def prefixEnd_449606 : Nat := 4983230072969 + 3 ^ 40 * 449606 * 2
def baseEnd_449606 : Nat := 102606214731321399181025

theorem tailTrace_449606 : CollatzResearch.WordTrace tailWord_449606 prefixEnd_449606 102606214731321399181025 := by
  unfold tailWord_449606
  simp only [CollatzResearch.WordTrace]
  refine ⟨512452437786303857394271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10932318672774482291077781 512452437786303857394271)
  ·
    refine ⟨768678656679455786091407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 512452437786303857394271 768678656679455786091407)
    ·
      refine ⟨1153017985019183679137111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768678656679455786091407 1153017985019183679137111)
      ·
        refine ⟨1729526977528775518705667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153017985019183679137111 1729526977528775518705667)
        ·
          refine ⟨2594290466293163278058501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729526977528775518705667 2594290466293163278058501)
          ·
            refine ⟨486429462429968114635969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2594290466293163278058501 486429462429968114635969)
            ·
              refine ⟨364822096822476085976977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486429462429968114635969 364822096822476085976977)
              ·
                refine ⟨273616572616857064482733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364822096822476085976977 273616572616857064482733)
                ·
                  refine ⟨102606214731321399181025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273616572616857064482733 102606214731321399181025)
                  ·
                    rfl

theorem cell21_449606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_449606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449606 prefixEnd_449606 := by exact prefixLift 449606
  have htrace : WordTrace (prefixWord ++ tailWord_449606) baseStart_449606 baseEnd_449606 := by
    simpa [prefixWord, tailWord_449606, baseEnd_449606] using wordTrace_append hprefix tailTrace_449606
  have hstable : (prefixWord ++ tailWord_449606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449606).length < 2 ^ (prefixWord ++ tailWord_449606).sum := by decide
  have hdescent : baseEnd_449606 < baseStart_449606 := by decide
  rcases family_descends (prefixWord ++ tailWord_449606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449673 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 5]
def baseStart_449673 : Nat := 118140960795 + 449673 * 2 ^ 59
def prefixEnd_449673 : Nat := 4983230072969 + 3 ^ 40 * 449673 * 2
def baseEnd_449673 : Nat := 102621505044144171564221

theorem tailTrace_449673 : CollatzResearch.WordTrace tailWord_449673 prefixEnd_449673 102621505044144171564221 := by
  unfold tailWord_449673
  simp only [CollatzResearch.WordTrace]
  refine ⟨16400921699918993879305673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10933947799945995919537115 16400921699918993879305673)
  ·
    refine ⟨12300691274939245409479255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16400921699918993879305673 12300691274939245409479255)
    ·
      refine ⟨18451036912408868114218883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12300691274939245409479255 18451036912408868114218883)
      ·
        refine ⟨27676555368613302171328325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18451036912408868114218883 27676555368613302171328325)
        ·
          refine ⟨5189354131614994157124061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27676555368613302171328325 5189354131614994157124061)
          ·
            refine ⟨1946007799355622808921523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5189354131614994157124061 1946007799355622808921523)
            ·
              refine ⟨2919011699033434213382285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946007799355622808921523 2919011699033434213382285)
              ·
                refine ⟨1094629387137537830018357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2919011699033434213382285 1094629387137537830018357)
                ·
                  refine ⟨102621505044144171564221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1094629387137537830018357 102621505044144171564221)
                  ·
                    rfl

theorem cell21_449673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_449673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449673 prefixEnd_449673 := by exact prefixLift 449673
  have htrace : WordTrace (prefixWord ++ tailWord_449673) baseStart_449673 baseEnd_449673 := by
    simpa [prefixWord, tailWord_449673, baseEnd_449673] using wordTrace_append hprefix tailTrace_449673
  have hstable : (prefixWord ++ tailWord_449673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449673).length < 2 ^ (prefixWord ++ tailWord_449673).sum := by decide
  have hdescent : baseEnd_449673 < baseStart_449673 := by decide
  rcases family_descends (prefixWord ++ tailWord_449673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449690 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_449690 : Nat := 118140960795 + 449690 * 2 ^ 59
def prefixEnd_449690 : Nat := 4983230072969 + 3 ^ 40 * 449690 * 2
def baseEnd_449690 : Nat := 102625384675755919780853

theorem tailTrace_449690 : CollatzResearch.WordTrace tailWord_449690 prefixEnd_449690 102625384675755919780853 := by
  unfold tailWord_449690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100385435214351445668631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10934361160571603855116349 4100385435214351445668631)
  ·
    refine ⟨6150578152821527168502947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4100385435214351445668631 6150578152821527168502947)
    ·
      refine ⟨9225867229232290752754421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6150578152821527168502947 9225867229232290752754421)
      ·
        refine ⟨864925052740527258070727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9225867229232290752754421 864925052740527258070727)
        ·
          refine ⟨1297387579110790887106091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864925052740527258070727 1297387579110790887106091)
          ·
            refine ⟨1946081368666186330659137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297387579110790887106091 1946081368666186330659137)
            ·
              refine ⟨1459561026499639747994353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946081368666186330659137 1459561026499639747994353)
              ·
                refine ⟨1094670769874729810995765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459561026499639747994353 1094670769874729810995765)
                ·
                  refine ⟨102625384675755919780853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1094670769874729810995765 102625384675755919780853)
                  ·
                    rfl

theorem cell21_449690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_449690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449690 prefixEnd_449690 := by exact prefixLift 449690
  have htrace : WordTrace (prefixWord ++ tailWord_449690) baseStart_449690 baseEnd_449690 := by
    simpa [prefixWord, tailWord_449690, baseEnd_449690] using wordTrace_append hprefix tailTrace_449690
  have hstable : (prefixWord ++ tailWord_449690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449690).length < 2 ^ (prefixWord ++ tailWord_449690).sum := by decide
  have hdescent : baseEnd_449690 < baseStart_449690 := by decide
  rcases family_descends (prefixWord ++ tailWord_449690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449724 : List Nat := [2, 2, 2, 3, 2, 2, 3, 2, 3]
def baseStart_449724 : Nat := 118140960795 + 449724 * 2 ^ 59
def prefixEnd_449724 : Nat := 4983230072969 + 3 ^ 40 * 449724 * 2
def baseEnd_449724 : Nat := 102633143938979416214117

theorem tailTrace_449724 : CollatzResearch.WordTrace tailWord_449724 prefixEnd_449724 102633143938979416214117 := by
  unfold tailWord_449724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8201390911367114794706113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10935187881822819726274817 8201390911367114794706113)
  ·
    refine ⟨6151043183525336096029585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8201390911367114794706113 6151043183525336096029585)
    ·
      refine ⟨4613282387644002072022189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6151043183525336096029585 4613282387644002072022189)
      ·
        refine ⟨1729980895366500777008321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4613282387644002072022189 1729980895366500777008321)
        ·
          refine ⟨1297485671524875582756241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1729980895366500777008321 1297485671524875582756241)
          ·
            refine ⟨973114253643656687067181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297485671524875582756241 973114253643656687067181)
            ·
              refine ⟨364917845116371257650193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 973114253643656687067181 364917845116371257650193)
              ·
                refine ⟨273688383837278443237645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364917845116371257650193 273688383837278443237645)
                ·
                  refine ⟨102633143938979416214117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273688383837278443237645 102633143938979416214117)
                  ·
                    rfl

theorem cell21_449724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_449724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449724 prefixEnd_449724 := by exact prefixLift 449724
  have htrace : WordTrace (prefixWord ++ tailWord_449724) baseStart_449724 baseEnd_449724 := by
    simpa [prefixWord, tailWord_449724, baseEnd_449724] using wordTrace_append hprefix tailTrace_449724
  have hstable : (prefixWord ++ tailWord_449724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449724).length < 2 ^ (prefixWord ++ tailWord_449724).sum := by decide
  have hdescent : baseEnd_449724 < baseStart_449724 := by decide
  rcases family_descends (prefixWord ++ tailWord_449724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449738 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_449738 : Nat := 118140960795 + 449738 * 2 ^ 59
def prefixEnd_449738 : Nat := 4983230072969 + 3 ^ 40 * 449738 * 2
def baseEnd_449738 : Nat := 102636338929718502980755

theorem tailTrace_449738 : CollatzResearch.WordTrace tailWord_449738 prefixEnd_449738 102636338929718502980755 := by
  unfold tailWord_449738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100823111170877495105467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10935528296455673320281245 4100823111170877495105467)
  ·
    refine ⟨6151234666756316242658201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4100823111170877495105467 6151234666756316242658201)
    ·
      refine ⟨4613426000067237181993651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6151234666756316242658201 4613426000067237181993651)
      ·
        refine ⟨6920139000100855772990477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613426000067237181993651 6920139000100855772990477)
        ·
          refine ⟨2595052125037820914871429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6920139000100855772990477 2595052125037820914871429)
          ·
            refine ⟨486572273444591421538393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2595052125037820914871429 486572273444591421538393)
            ·
              refine ⟨364929205083443566153795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486572273444591421538393 364929205083443566153795)
              ·
                refine ⟨547393807625165349230693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364929205083443566153795 547393807625165349230693)
                ·
                  refine ⟨102636338929718502980755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547393807625165349230693 102636338929718502980755)
                  ·
                    rfl

theorem cell21_449738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_449738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449738 prefixEnd_449738 := by exact prefixLift 449738
  have htrace : WordTrace (prefixWord ++ tailWord_449738) baseStart_449738 baseEnd_449738 := by
    simpa [prefixWord, tailWord_449738, baseEnd_449738] using wordTrace_append hprefix tailTrace_449738
  have hstable : (prefixWord ++ tailWord_449738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449738).length < 2 ^ (prefixWord ++ tailWord_449738).sum := by decide
  have hdescent : baseEnd_449738 < baseStart_449738 := by decide
  rcases family_descends (prefixWord ++ tailWord_449738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449842 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_449842 : Nat := 118140960795 + 449842 * 2 ^ 59
def prefixEnd_449842 : Nat := 4983230072969 + 3 ^ 40 * 449842 * 2
def baseEnd_449842 : Nat := 102660073146637433247209

theorem tailTrace_449842 : CollatzResearch.WordTrace tailWord_449842 prefixEnd_449842 102660073146637433247209 := by
  unfold tailWord_449842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101771409076683935551945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10938057090871157161471853 4101771409076683935551945)
  ·
    refine ⟨3076328556807512951663959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4101771409076683935551945 3076328556807512951663959)
    ·
      refine ⟨4614492835211269427495939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3076328556807512951663959 4614492835211269427495939)
      ·
        refine ⟨6921739252816904141243909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4614492835211269427495939 6921739252816904141243909)
        ·
          refine ⟨1297826109903169526483233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6921739252816904141243909 1297826109903169526483233)
          ·
            refine ⟨973369582427377144862425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297826109903169526483233 973369582427377144862425)
            ·
              refine ⟨730027186820532858646819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973369582427377144862425 730027186820532858646819)
              ·
                refine ⟨1095040780230799287970229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730027186820532858646819 1095040780230799287970229)
                ·
                  refine ⟨102660073146637433247209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1095040780230799287970229 102660073146637433247209)
                  ·
                    rfl

theorem cell21_449842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_449842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449842 prefixEnd_449842 := by exact prefixLift 449842
  have htrace : WordTrace (prefixWord ++ tailWord_449842) baseStart_449842 baseEnd_449842 := by
    simpa [prefixWord, tailWord_449842, baseEnd_449842] using wordTrace_append hprefix tailTrace_449842
  have hstable : (prefixWord ++ tailWord_449842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449842).length < 2 ^ (prefixWord ++ tailWord_449842).sum := by decide
  have hdescent : baseEnd_449842 < baseStart_449842 := by decide
  rcases family_descends (prefixWord ++ tailWord_449842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449870 : List Nat := [4, 1, 1, 1, 1, 1, 5, 7]
def baseStart_449870 : Nat := 118140960795 + 449870 * 2 ^ 59
def prefixEnd_449870 : Nat := 4983230072969 + 3 ^ 40 * 449870 * 2
def baseEnd_449870 : Nat := 34222154376038535593495

theorem tailTrace_449870 : CollatzResearch.WordTrace tailWord_449870 prefixEnd_449870 34222154376038535593495 := by
  unfold tailWord_449870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051013360025662065528383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10938737920136864349484709 2051013360025662065528383)
  ·
    refine ⟨3076520040038493098292575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2051013360025662065528383 3076520040038493098292575)
    ·
      refine ⟨4614780060057739647438863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3076520040038493098292575 4614780060057739647438863)
      ·
        refine ⟨6922170090086609471158295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4614780060057739647438863 6922170090086609471158295)
        ·
          refine ⟨10383255135129914206737443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6922170090086609471158295 10383255135129914206737443)
          ·
            refine ⟨15574882702694871310106165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10383255135129914206737443 15574882702694871310106165)
            ·
              refine ⟨1460145253377644185322453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15574882702694871310106165 1460145253377644185322453)
              ·
                refine ⟨34222154376038535593495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1460145253377644185322453 34222154376038535593495)
                ·
                  rfl

theorem cell21_449870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_449870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449870 prefixEnd_449870 := by exact prefixLift 449870
  have htrace : WordTrace (prefixWord ++ tailWord_449870) baseStart_449870 baseEnd_449870 := by
    simpa [prefixWord, tailWord_449870, baseEnd_449870] using wordTrace_append hprefix tailTrace_449870
  have hstable : (prefixWord ++ tailWord_449870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449870).length < 2 ^ (prefixWord ++ tailWord_449870).sum := by decide
  have hdescent : baseEnd_449870 < baseStart_449870 := by decide
  rcases family_descends (prefixWord ++ tailWord_449870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449949 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 4]
def baseStart_449949 : Nat := 118140960795 + 449949 * 2 ^ 59
def prefixEnd_449949 : Nat := 4983230072969 + 3 ^ 40 * 449949 * 2
def baseEnd_449949 : Nat := 102684492004429024963657

theorem tailTrace_449949 : CollatzResearch.WordTrace tailWord_449949 prefixEnd_449949 102684492004429024963657 := by
  unfold tailWord_449949
  simp only [CollatzResearch.WordTrace]
  refine ⟨16410988246919093016352901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10940658831279395344235267 16410988246919093016352901)
  ·
    refine ⟨3077060296297329940566169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16410988246919093016352901 3077060296297329940566169)
    ·
      refine ⟨2307795222222997455424627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3077060296297329940566169 2307795222222997455424627)
      ·
        refine ⟨3461692833334496183136941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307795222222997455424627 3461692833334496183136941)
        ·
          refine ⟨1298134812500436068676353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3461692833334496183136941 1298134812500436068676353)
          ·
            refine ⟨973601109375327051507265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1298134812500436068676353 973601109375327051507265)
            ·
              refine ⟨730200832031495288630449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973601109375327051507265 730200832031495288630449)
              ·
                refine ⟨547650624023621466472837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730200832031495288630449 547650624023621466472837)
                ·
                  refine ⟨102684492004429024963657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547650624023621466472837 102684492004429024963657)
                  ·
                    rfl

theorem cell21_449949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_449949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449949 prefixEnd_449949 := by exact prefixLift 449949
  have htrace : WordTrace (prefixWord ++ tailWord_449949) baseStart_449949 baseEnd_449949 := by
    simpa [prefixWord, tailWord_449949, baseEnd_449949] using wordTrace_append hprefix tailTrace_449949
  have hstable : (prefixWord ++ tailWord_449949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449949).length < 2 ^ (prefixWord ++ tailWord_449949).sum := by decide
  have hdescent : baseEnd_449949 < baseStart_449949 := by decide
  rcases family_descends (prefixWord ++ tailWord_449949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449980 : List Nat := [2, 2, 2, 4, 2, 1, 3, 5]
def baseStart_449980 : Nat := 118140960795 + 449980 * 2 ^ 59
def prefixEnd_449980 : Nat := 4983230072969 + 3 ^ 40 * 449980 * 2
def baseEnd_449980 : Nat := 34230522208926619982309

theorem tailTrace_449980 : CollatzResearch.WordTrace tailWord_449980 prefixEnd_449980 34230522208926619982309 := by
  unfold tailWord_449980
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206059454903392655365697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10941412606537856873820929 8206059454903392655365697)
  ·
    refine ⟨6154544591177544491524273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8206059454903392655365697 6154544591177544491524273)
    ·
      refine ⟨4615908443383158368643205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6154544591177544491524273 4615908443383158368643205)
      ·
        refine ⟨865482833134342194120601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4615908443383158368643205 865482833134342194120601)
        ·
          refine ⟨649112124850756645590451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865482833134342194120601 649112124850756645590451)
          ·
            refine ⟨973668187276134968385677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649112124850756645590451 973668187276134968385677)
            ·
              refine ⟨365125570228550613144629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 973668187276134968385677 365125570228550613144629)
              ·
                refine ⟨34230522208926619982309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 365125570228550613144629 34230522208926619982309)
                ·
                  rfl

theorem cell21_449980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_449980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449980 prefixEnd_449980 := by exact prefixLift 449980
  have htrace : WordTrace (prefixWord ++ tailWord_449980) baseStart_449980 baseEnd_449980 := by
    simpa [prefixWord, tailWord_449980, baseEnd_449980] using wordTrace_append hprefix tailTrace_449980
  have hstable : (prefixWord ++ tailWord_449980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449980).length < 2 ^ (prefixWord ++ tailWord_449980).sum := by decide
  have hdescent : baseEnd_449980 < baseStart_449980 := by decide
  rcases family_descends (prefixWord ++ tailWord_449980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449991 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 6]
def baseStart_449991 : Nat := 118140960795 + 449991 * 2 ^ 59
def prefixEnd_449991 : Nat := 4983230072969 + 3 ^ 40 * 449991 * 2
def baseEnd_449991 : Nat := 102694076976646285263571

theorem tailTrace_449991 : CollatzResearch.WordTrace tailWord_449991 prefixEnd_449991 102694076976646285263571 := by
  unfold tailWord_449991
  simp only [CollatzResearch.WordTrace]
  refine ⟨16412520112766934189381827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10941680075177956126254551 16412520112766934189381827)
  ·
    refine ⟨24618780169150401284072741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16412520112766934189381827 24618780169150401284072741)
    ·
      refine ⟨4616021281715700240763639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24618780169150401284072741 4616021281715700240763639)
      ·
        refine ⟨6924031922573550361145459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616021281715700240763639 6924031922573550361145459)
        ·
          refine ⟨10386047883860325541718189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6924031922573550361145459 10386047883860325541718189)
          ·
            refine ⟨3894767956447622078144321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10386047883860325541718189 3894767956447622078144321)
            ·
              refine ⟨2921075967335716558608241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3894767956447622078144321 2921075967335716558608241)
              ·
                refine ⟨2190806975501787418956181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2921075967335716558608241 2190806975501787418956181)
                ·
                  refine ⟨102694076976646285263571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2190806975501787418956181 102694076976646285263571)
                  ·
                    rfl

theorem cell21_449991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_449991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449991 prefixEnd_449991 := by exact prefixLift 449991
  have htrace : WordTrace (prefixWord ++ tailWord_449991) baseStart_449991 baseEnd_449991 := by
    simpa [prefixWord, tailWord_449991, baseEnd_449991] using wordTrace_append hprefix tailTrace_449991
  have hstable : (prefixWord ++ tailWord_449991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449991).length < 2 ^ (prefixWord ++ tailWord_449991).sum := by decide
  have hdescent : baseEnd_449991 < baseStart_449991 := by decide
  rcases family_descends (prefixWord ++ tailWord_449991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449994 : List Nat := [3, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_449994 : Nat := 118140960795 + 449994 * 2 ^ 59
def prefixEnd_449994 : Nat := 4983230072969 + 3 ^ 40 * 449994 * 2
def baseEnd_449994 : Nat := 102694761617518946713565

theorem tailTrace_449994 : CollatzResearch.WordTrace tailWord_449994 prefixEnd_449994 102694761617518946713565 := by
  unfold tailWord_449994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4103157382939016425435259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10941753021170710467827357 4103157382939016425435259)
  ·
    refine ⟨6154736074408524638152889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4103157382939016425435259 6154736074408524638152889)
    ·
      refine ⟨4616052055806393478614667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6154736074408524638152889 4616052055806393478614667)
      ·
        refine ⟨6924078083709590217922001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616052055806393478614667 6924078083709590217922001)
        ·
          refine ⟨5193058562782192663441501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6924078083709590217922001 5193058562782192663441501)
          ·
            refine ⟨1947396961043322248790563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5193058562782192663441501 1947396961043322248790563)
            ·
              refine ⟨2921095441564983373185845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947396961043322248790563 2921095441564983373185845)
              ·
                refine ⟨273852697646717191236173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2921095441564983373185845 273852697646717191236173)
                ·
                  refine ⟨102694761617518946713565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273852697646717191236173 102694761617518946713565)
                  ·
                    rfl

theorem cell21_449994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_449994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_449994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_449994 prefixEnd_449994 := by exact prefixLift 449994
  have htrace : WordTrace (prefixWord ++ tailWord_449994) baseStart_449994 baseEnd_449994 := by
    simpa [prefixWord, tailWord_449994, baseEnd_449994] using wordTrace_append hprefix tailTrace_449994
  have hstable : (prefixWord ++ tailWord_449994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449994).length < 2 ^ (prefixWord ++ tailWord_449994).sum := by decide
  have hdescent : baseEnd_449994 < baseStart_449994 := by decide
  rcases family_descends (prefixWord ++ tailWord_449994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450008 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_450008 : Nat := 118140960795 + 450008 * 2 ^ 59
def prefixEnd_450008 : Nat := 4983230072969 + 3 ^ 40 * 450008 * 2
def baseEnd_450008 : Nat := 102697956608258033480203

theorem tailTrace_450008 : CollatzResearch.WordTrace tailWord_450008 prefixEnd_450008 102697956608258033480203 := by
  unfold tailWord_450008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206570076852673046375339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10942093435803564061833785 8206570076852673046375339)
  ·
    refine ⟨12309855115279009569563009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8206570076852673046375339 12309855115279009569563009)
    ·
      refine ⟨9232391336459257177172257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12309855115279009569563009 9232391336459257177172257)
      ·
        refine ⟨6924293502344442882879193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9232391336459257177172257 6924293502344442882879193)
        ·
          refine ⟨5193220126758332162159395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6924293502344442882879193 5193220126758332162159395)
          ·
            refine ⟨7789830190137498243239093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193220126758332162159395 7789830190137498243239093)
            ·
              refine ⟨730296580325390460303665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7789830190137498243239093 730296580325390460303665)
              ·
                refine ⟨547722435244042845227749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730296580325390460303665 547722435244042845227749)
                ·
                  refine ⟨102697956608258033480203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547722435244042845227749 102697956608258033480203)
                  ·
                    rfl

theorem cell21_450008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_450008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450008 prefixEnd_450008 := by exact prefixLift 450008
  have htrace : WordTrace (prefixWord ++ tailWord_450008) baseStart_450008 baseEnd_450008 := by
    simpa [prefixWord, tailWord_450008, baseEnd_450008] using wordTrace_append hprefix tailTrace_450008
  have hstable : (prefixWord ++ tailWord_450008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450008).length < 2 ^ (prefixWord ++ tailWord_450008).sum := by decide
  have hdescent : baseEnd_450008 < baseStart_450008 := by decide
  rcases family_descends (prefixWord ++ tailWord_450008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450067 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 6]
def baseStart_450067 : Nat := 118140960795 + 450067 * 2 ^ 59
def prefixEnd_450067 : Nat := 4983230072969 + 3 ^ 40 * 450067 * 2
def baseEnd_450067 : Nat := 102711421212087041996749

theorem tailTrace_450067 : CollatzResearch.WordTrace tailWord_450067 prefixEnd_450067 102711421212087041996749 := by
  unfold tailWord_450067
  simp only [CollatzResearch.WordTrace]
  refine ⟨16415292060491599169148455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10943528040327732779432303 16415292060491599169148455)
  ·
    refine ⟨24622938090737398753722683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16415292060491599169148455 24622938090737398753722683)
    ·
      refine ⟨36934407136106098130584025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24622938090737398753722683 36934407136106098130584025)
      ·
        refine ⟨27700805352079573597938019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36934407136106098130584025 27700805352079573597938019)
        ·
          refine ⟨41551208028119360396907029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27700805352079573597938019 41551208028119360396907029)
          ·
            refine ⟨1947712876318095018605017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41551208028119360396907029 1947712876318095018605017)
            ·
              refine ⟨1460784657238571263953763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947712876318095018605017 1460784657238571263953763)
              ·
                refine ⟨2191176985857856895930645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460784657238571263953763 2191176985857856895930645)
                ·
                  refine ⟨102711421212087041996749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2191176985857856895930645 102711421212087041996749)
                  ·
                    rfl

theorem cell21_450067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_450067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450067 prefixEnd_450067 := by exact prefixLift 450067
  have htrace : WordTrace (prefixWord ++ tailWord_450067) baseStart_450067 baseEnd_450067 := by
    simpa [prefixWord, tailWord_450067, baseEnd_450067] using wordTrace_append hprefix tailTrace_450067
  have hstable : (prefixWord ++ tailWord_450067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450067).length < 2 ^ (prefixWord ++ tailWord_450067).sum := by decide
  have hdescent : baseEnd_450067 < baseStart_450067 := by decide
  rcases family_descends (prefixWord ++ tailWord_450067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450177 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 4]
def baseStart_450177 : Nat := 118140960795 + 450177 * 2 ^ 59
def prefixEnd_450177 : Nat := 4983230072969 + 3 ^ 40 * 450177 * 2
def baseEnd_450177 : Nat := 102736524710751295163191

theorem tailTrace_450177 : CollatzResearch.WordTrace tailWord_450177 prefixEnd_450177 102736524710751295163191 := by
  unfold tailWord_450177
  simp only [CollatzResearch.WordTrace]
  refine ⟨16419304090093087955652785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10946202726728725303768523 16419304090093087955652785)
  ·
    refine ⟨12314478067569815966739589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16419304090093087955652785 12314478067569815966739589)
    ·
      refine ⟨2308964637669340493763673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12314478067569815966739589 2308964637669340493763673)
      ·
        refine ⟨1731723478252005370322755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2308964637669340493763673 1731723478252005370322755)
        ·
          refine ⟨2597585217378008055484133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731723478252005370322755 2597585217378008055484133)
          ·
            refine ⟨487047228258376510403275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2597585217378008055484133 487047228258376510403275)
            ·
              refine ⟨730570842387564765604913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487047228258376510403275 730570842387564765604913)
              ·
                refine ⟨547928131790673574203685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730570842387564765604913 547928131790673574203685)
                ·
                  refine ⟨102736524710751295163191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547928131790673574203685 102736524710751295163191)
                  ·
                    rfl

theorem cell21_450177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_450177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450177 prefixEnd_450177 := by exact prefixLift 450177
  have htrace : WordTrace (prefixWord ++ tailWord_450177) baseStart_450177 baseEnd_450177 := by
    simpa [prefixWord, tailWord_450177, baseEnd_450177] using wordTrace_append hprefix tailTrace_450177
  have hstable : (prefixWord ++ tailWord_450177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450177).length < 2 ^ (prefixWord ++ tailWord_450177).sum := by decide
  have hdescent : baseEnd_450177 < baseStart_450177 := by decide
  rcases family_descends (prefixWord ++ tailWord_450177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450194 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_450194 : Nat := 118140960795 + 450194 * 2 ^ 59
def prefixEnd_450194 : Nat := 4983230072969 + 3 ^ 40 * 450194 * 2
def baseEnd_450194 : Nat := 102740404342363043379823

theorem tailTrace_450194 : CollatzResearch.WordTrace tailWord_450194 prefixEnd_450194 102740404342363043379823 := by
  unfold tailWord_450194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4104981032757874964755409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10946616087354333239347757 4104981032757874964755409)
  ·
    refine ⟨3078735774568406223566557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4104981032757874964755409 3078735774568406223566557)
    ·
      refine ⟨1154525915463152333837459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3078735774568406223566557 1154525915463152333837459)
      ·
        refine ⟨1731788873194728500756189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154525915463152333837459 1731788873194728500756189)
        ·
          refine ⟨649420827448023187783571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1731788873194728500756189 649420827448023187783571)
          ·
            refine ⟨974131241172034781675357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649420827448023187783571 974131241172034781675357)
            ·
              refine ⟨365299215439513043128259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 974131241172034781675357 365299215439513043128259)
              ·
                refine ⟨547948823159269564692389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365299215439513043128259 547948823159269564692389)
                ·
                  refine ⟨102740404342363043379823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547948823159269564692389 102740404342363043379823)
                  ·
                    rfl

theorem cell21_450194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_450194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450194 prefixEnd_450194 := by exact prefixLift 450194
  have htrace : WordTrace (prefixWord ++ tailWord_450194) baseStart_450194 baseEnd_450194 := by
    simpa [prefixWord, tailWord_450194, baseEnd_450194] using wordTrace_append hprefix tailTrace_450194
  have hstable : (prefixWord ++ tailWord_450194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450194).length < 2 ^ (prefixWord ++ tailWord_450194).sum := by decide
  have hdescent : baseEnd_450194 < baseStart_450194 := by decide
  rcases family_descends (prefixWord ++ tailWord_450194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450233 : List Nat := [1, 2, 1, 4, 1, 1, 11]
def baseStart_450233 : Nat := 118140960795 + 450233 * 2 ^ 59
def prefixEnd_450233 : Nat := 4983230072969 + 3 ^ 40 * 450233 * 2
def baseEnd_450233 : Nat := 11416589408189738025527

theorem tailTrace_450233 : CollatzResearch.WordTrace tailWord_450233 prefixEnd_450233 11416589408189738025527 := by
  unfold tailWord_450233
  simp only [CollatzResearch.WordTrace]
  refine ⟨16421346577890209519691353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10947564385260139679794235 16421346577890209519691353)
  ·
    refine ⟨12316009933417657139768515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16421346577890209519691353 12316009933417657139768515)
    ·
      refine ⟨18474014900126485709652773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12316009933417657139768515 18474014900126485709652773)
      ·
        refine ⟨3463877793773716070559895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18474014900126485709652773 3463877793773716070559895)
        ·
          refine ⟨5195816690660574105839843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3463877793773716070559895 5195816690660574105839843)
          ·
            refine ⟨7793725035990861158759765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195816690660574105839843 7793725035990861158759765)
            ·
              refine ⟨11416589408189738025527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7793725035990861158759765 11416589408189738025527)
              ·
                rfl

theorem cell21_450233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 11].length) (baseStart_450233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450233 prefixEnd_450233 := by exact prefixLift 450233
  have htrace : WordTrace (prefixWord ++ tailWord_450233) baseStart_450233 baseEnd_450233 := by
    simpa [prefixWord, tailWord_450233, baseEnd_450233] using wordTrace_append hprefix tailTrace_450233
  have hstable : (prefixWord ++ tailWord_450233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450233).length < 2 ^ (prefixWord ++ tailWord_450233).sum := by decide
  have hdescent : baseEnd_450233 < baseStart_450233 := by decide
  rcases family_descends (prefixWord ++ tailWord_450233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450264 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_450264 : Nat := 118140960795 + 450264 * 2 ^ 59
def prefixEnd_450264 : Nat := 4983230072969 + 3 ^ 40 * 450264 * 2
def baseEnd_450264 : Nat := 102756379296058477213013

theorem tailTrace_450264 : CollatzResearch.WordTrace tailWord_450264 prefixEnd_450264 102756379296058477213013 := by
  unfold tailWord_450264
  simp only [CollatzResearch.WordTrace]
  refine ⟨8211238620388950907034923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10948318160518601209379897 8211238620388950907034923)
  ·
    refine ⟨12316857930583426360552385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8211238620388950907034923 12316857930583426360552385)
    ·
      refine ⟨9237643447937569770414289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12316857930583426360552385 9237643447937569770414289)
      ·
        refine ⟨6928232585953177327810717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9237643447937569770414289 6928232585953177327810717)
        ·
          refine ⟨2598087219732441497929019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6928232585953177327810717 2598087219732441497929019)
          ·
            refine ⟨3897130829598662246893529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598087219732441497929019 3897130829598662246893529)
            ·
              refine ⟨2922848122198996685170147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897130829598662246893529 2922848122198996685170147)
              ·
                refine ⟨4384272183298495027755221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922848122198996685170147 4384272183298495027755221)
                ·
                  refine ⟨102756379296058477213013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4384272183298495027755221 102756379296058477213013)
                  ·
                    rfl

theorem cell21_450264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_450264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450264 prefixEnd_450264 := by exact prefixLift 450264
  have htrace : WordTrace (prefixWord ++ tailWord_450264) baseStart_450264 baseEnd_450264 := by
    simpa [prefixWord, tailWord_450264, baseEnd_450264] using wordTrace_append hprefix tailTrace_450264
  have hstable : (prefixWord ++ tailWord_450264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450264).length < 2 ^ (prefixWord ++ tailWord_450264).sum := by decide
  have hdescent : baseEnd_450264 < baseStart_450264 := by decide
  rcases family_descends (prefixWord ++ tailWord_450264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450281 : List Nat := [1, 2, 1, 1, 1, 2, 3, 7, 3]
def baseStart_450281 : Nat := 118140960795 + 450281 * 2 ^ 59
def prefixEnd_450281 : Nat := 4983230072969 + 3 ^ 40 * 450281 * 2
def baseEnd_450281 : Nat := 102760258927670225429645

theorem tailTrace_450281 : CollatzResearch.WordTrace tailWord_450281 prefixEnd_450281 102760258927670225429645 := by
  unfold tailWord_450281
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423097281716313717438697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10948731521144209144959131 16423097281716313717438697)
  ·
    refine ⟨12317322961287235288079023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16423097281716313717438697 12317322961287235288079023)
    ·
      refine ⟨18475984441930852932118535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12317322961287235288079023 18475984441930852932118535)
      ·
        refine ⟨27713976662896279398177803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18475984441930852932118535 27713976662896279398177803)
        ·
          refine ⟨41570964994344419097266705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27713976662896279398177803 41570964994344419097266705)
          ·
            refine ⟨31178223745758314322950029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41570964994344419097266705 31178223745758314322950029)
            ·
              refine ⟨11691833904659367871106261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31178223745758314322950029 11691833904659367871106261)
              ·
                refine ⟨274027357140453934479053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11691833904659367871106261 274027357140453934479053)
                ·
                  refine ⟨102760258927670225429645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274027357140453934479053 102760258927670225429645)
                  ·
                    rfl

theorem cell21_450281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_450281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450281 prefixEnd_450281 := by exact prefixLift 450281
  have htrace : WordTrace (prefixWord ++ tailWord_450281) baseStart_450281 baseEnd_450281 := by
    simpa [prefixWord, tailWord_450281, baseEnd_450281] using wordTrace_append hprefix tailTrace_450281
  have hstable : (prefixWord ++ tailWord_450281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450281).length < 2 ^ (prefixWord ++ tailWord_450281).sum := by decide
  have hdescent : baseEnd_450281 < baseStart_450281 := by decide
  rcases family_descends (prefixWord ++ tailWord_450281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450295 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 4]
def baseStart_450295 : Nat := 118140960795 + 450295 * 2 ^ 59
def prefixEnd_450295 : Nat := 4983230072969 + 3 ^ 40 * 450295 * 2
def baseEnd_450295 : Nat := 102763453918409312196283

theorem tailTrace_450295 : CollatzResearch.WordTrace tailWord_450295 prefixEnd_450295 102763453918409312196283 := by
  unfold tailWord_450295
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423607903665594108448339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10949071935777062738965559 16423607903665594108448339)
  ·
    refine ⟨24635411855498391162672509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16423607903665594108448339 24635411855498391162672509)
    ·
      refine ⟨9238279445811896686002191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24635411855498391162672509 9238279445811896686002191)
      ·
        refine ⟨13857419168717845029003287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9238279445811896686002191 13857419168717845029003287)
        ·
          refine ⟨20786128753076767543504931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13857419168717845029003287 20786128753076767543504931)
          ·
            refine ⟨31179193129615151315257397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20786128753076767543504931 31179193129615151315257397)
            ·
              refine ⟨2923049355901420435805381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31179193129615151315257397 2923049355901420435805381)
              ·
                refine ⟨548071754231516331713509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2923049355901420435805381 548071754231516331713509)
                ·
                  refine ⟨102763453918409312196283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548071754231516331713509 102763453918409312196283)
                  ·
                    rfl

theorem cell21_450295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 4].length) (baseStart_450295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450295 prefixEnd_450295 := by exact prefixLift 450295
  have htrace : WordTrace (prefixWord ++ tailWord_450295) baseStart_450295 baseEnd_450295 := by
    simpa [prefixWord, tailWord_450295, baseEnd_450295] using wordTrace_append hprefix tailTrace_450295
  have hstable : (prefixWord ++ tailWord_450295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450295).length < 2 ^ (prefixWord ++ tailWord_450295).sum := by decide
  have hdescent : baseEnd_450295 < baseStart_450295 := by decide
  rcases family_descends (prefixWord ++ tailWord_450295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450391 : List Nat := [1, 1, 3, 2, 5, 2, 1, 3, 3]
def baseStart_450391 : Nat := 118140960795 + 450391 * 2 ^ 59
def prefixEnd_450391 : Nat := 4983230072969 + 3 ^ 40 * 450391 * 2
def baseEnd_450391 : Nat := 102785362426334478596087

theorem tailTrace_450391 : CollatzResearch.WordTrace tailWord_450391 prefixEnd_450391 102785362426334478596087 := by
  unfold tailWord_450391
  simp only [CollatzResearch.WordTrace]
  refine ⟨16427109311317802503943027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10951406207545201669295351 16427109311317802503943027)
  ·
    refine ⟨24640663966976703755914541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16427109311317802503943027 24640663966976703755914541)
    ·
      refine ⟨9240248987616263908467953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24640663966976703755914541 9240248987616263908467953)
      ·
        refine ⟨6930186740712197931350965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9240248987616263908467953 6930186740712197931350965)
        ·
          refine ⟨649705006941768556064153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6930186740712197931350965 649705006941768556064153)
          ·
            refine ⟨487278755206326417048115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649705006941768556064153 487278755206326417048115)
            ·
              refine ⟨730918132809489625572173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487278755206326417048115 730918132809489625572173)
              ·
                refine ⟨274094299803558609589565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 730918132809489625572173 274094299803558609589565)
                ·
                  refine ⟨102785362426334478596087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274094299803558609589565 102785362426334478596087)
                  ·
                    rfl

theorem cell21_450391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 3].length) (baseStart_450391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450391 prefixEnd_450391 := by exact prefixLift 450391
  have htrace : WordTrace (prefixWord ++ tailWord_450391) baseStart_450391 baseEnd_450391 := by
    simpa [prefixWord, tailWord_450391, baseEnd_450391] using wordTrace_append hprefix tailTrace_450391
  have hstable : (prefixWord ++ tailWord_450391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450391).length < 2 ^ (prefixWord ++ tailWord_450391).sum := by decide
  have hdescent : baseEnd_450391 < baseStart_450391 := by decide
  rcases family_descends (prefixWord ++ tailWord_450391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450402 : List Nat := [3, 3, 2, 1, 2, 1, 9]
def baseStart_450402 : Nat := 118140960795 + 450402 * 2 ^ 59
def prefixEnd_450402 : Nat := 4983230072969 + 3 ^ 40 * 450402 * 2
def baseEnd_450402 : Nat := 11420874752911211545859

theorem tailTrace_450402 : CollatzResearch.WordTrace tailWord_450402 prefixEnd_450402 11420874752911211545859 := by
  unfold tailWord_450402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106877628569487845648365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10951673676185300921728973 4106877628569487845648365)
  ·
    refine ⟨1540079110713557942118137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4106877628569487845648365 1540079110713557942118137)
    ·
      refine ⟨1155059333035168456588603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1540079110713557942118137 1155059333035168456588603)
      ·
        refine ⟨1732588999552752684882905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155059333035168456588603 1732588999552752684882905)
        ·
          refine ⟨1299441749664564513662179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1732588999552752684882905 1299441749664564513662179)
          ·
            refine ⟨1949162624496846770493269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299441749664564513662179 1949162624496846770493269)
            ·
              refine ⟨11420874752911211545859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1949162624496846770493269 11420874752911211545859)
              ·
                rfl

theorem cell21_450402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 9].length) (baseStart_450402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450402 prefixEnd_450402 := by exact prefixLift 450402
  have htrace : WordTrace (prefixWord ++ tailWord_450402) baseStart_450402 baseEnd_450402 := by
    simpa [prefixWord, tailWord_450402, baseEnd_450402] using wordTrace_append hprefix tailTrace_450402
  have hstable : (prefixWord ++ tailWord_450402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450402).length < 2 ^ (prefixWord ++ tailWord_450402).sum := by decide
  have hdescent : baseEnd_450402 < baseStart_450402 := by decide
  rcases family_descends (prefixWord ++ tailWord_450402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450461 : List Nat := [1, 4, 2, 1, 2, 11]
def baseStart_450461 : Nat := 118140960795 + 450461 * 2 ^ 59
def prefixEnd_450461 : Nat := 4983230072969 + 3 ^ 40 * 450461 * 2
def baseEnd_450461 : Nat := 3807456940001107867751

theorem tailTrace_450461 : CollatzResearch.WordTrace tailWord_450461 prefixEnd_450461 3807456940001107867751 := by
  unfold tailWord_450461
  simp only [CollatzResearch.WordTrace]
  refine ⟨16429662421064204458991237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10953108280709469639327491 16429662421064204458991237)
  ·
    refine ⟨3080561703949538336060857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16429662421064204458991237 3080561703949538336060857)
    ·
      refine ⟨2310421277962153752045643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3080561703949538336060857 2310421277962153752045643)
      ·
        refine ⟨3465631916943230628068465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2310421277962153752045643 3465631916943230628068465)
        ·
          refine ⟨2599223937707422971051349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3465631916943230628068465 2599223937707422971051349)
          ·
            refine ⟨3807456940001107867751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2599223937707422971051349 3807456940001107867751)
            ·
              rfl

theorem cell21_450461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 11].length) (baseStart_450461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450461 prefixEnd_450461 := by exact prefixLift 450461
  have htrace : WordTrace (prefixWord ++ tailWord_450461) baseStart_450461 baseEnd_450461 := by
    simpa [prefixWord, tailWord_450461, baseEnd_450461] using wordTrace_append hprefix tailTrace_450461
  have hstable : (prefixWord ++ tailWord_450461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450461).length < 2 ^ (prefixWord ++ tailWord_450461).sum := by decide
  have hdescent : baseEnd_450461 < baseStart_450461 := by decide
  rcases family_descends (prefixWord ++ tailWord_450461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450613 : List Nat := [1, 3, 3, 1, 1, 1, 4, 7]
def baseStart_450613 : Nat := 118140960795 + 450613 * 2 ^ 59
def prefixEnd_450613 : Nat := 4983230072969 + 3 ^ 40 * 450613 * 2
def baseEnd_450613 : Nat := 34278675283637141965211

theorem tailTrace_450613 : CollatzResearch.WordTrace tailWord_450613 prefixEnd_450613 34278675283637141965211 := by
  unfold tailWord_450613
  simp only [CollatzResearch.WordTrace]
  refine ⟨16435206316513534418524493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10956804211009022945682995 16435206316513534418524493)
  ·
    refine ⟨6163202368692575406946685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16435206316513534418524493 6163202368692575406946685)
    ·
      refine ⟨2311200888259715777605007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6163202368692575406946685 2311200888259715777605007)
      ·
        refine ⟨3466801332389573666407511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311200888259715777605007 3466801332389573666407511)
        ·
          refine ⟨5200201998584360499611267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466801332389573666407511 5200201998584360499611267)
          ·
            refine ⟨7800302997876540749416901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200201998584360499611267 7800302997876540749416901)
            ·
              refine ⟨1462556812101851390515669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7800302997876540749416901 1462556812101851390515669)
              ·
                refine ⟨34278675283637141965211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1462556812101851390515669 34278675283637141965211)
                ·
                  rfl

theorem cell21_450613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 7].length) (baseStart_450613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450613 prefixEnd_450613 := by exact prefixLift 450613
  have htrace : WordTrace (prefixWord ++ tailWord_450613) baseStart_450613 baseEnd_450613 := by
    simpa [prefixWord, tailWord_450613, baseEnd_450613] using wordTrace_append hprefix tailTrace_450613
  have hstable : (prefixWord ++ tailWord_450613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450613).length < 2 ^ (prefixWord ++ tailWord_450613).sum := by decide
  have hdescent : baseEnd_450613 < baseStart_450613 := by decide
  rcases family_descends (prefixWord ++ tailWord_450613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450627 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 9]
def baseStart_450627 : Nat := 118140960795 + 450627 * 2 ^ 59
def prefixEnd_450627 : Nat := 4983230072969 + 3 ^ 40 * 450627 * 2
def baseEnd_450627 : Nat := 102839220841650512662271

theorem tailTrace_450627 : CollatzResearch.WordTrace tailWord_450627 prefixEnd_450627 102839220841650512662271 := by
  unfold tailWord_450627
  simp only [CollatzResearch.WordTrace]
  refine ⟨16435716938462814809534135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10957144625641876539689423 16435716938462814809534135)
  ·
    refine ⟨24653575407694222214301203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16435716938462814809534135 24653575407694222214301203)
    ·
      refine ⟨36980363111541333321451805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24653575407694222214301203 36980363111541333321451805)
      ·
        refine ⟨13867636166827999995544427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36980363111541333321451805 13867636166827999995544427)
        ·
          refine ⟨20801454250241999993316641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13867636166827999995544427 20801454250241999993316641)
          ·
            refine ⟨15601090687681499994987481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20801454250241999993316641 15601090687681499994987481)
            ·
              refine ⟨11700818015761124996240611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15601090687681499994987481 11700818015761124996240611)
              ·
                refine ⟨17551227023641687494360917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11700818015761124996240611 17551227023641687494360917)
                ·
                  refine ⟨102839220841650512662271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17551227023641687494360917 102839220841650512662271)
                  ·
                    rfl

theorem cell21_450627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_450627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450627 prefixEnd_450627 := by exact prefixLift 450627
  have htrace : WordTrace (prefixWord ++ tailWord_450627) baseStart_450627 baseEnd_450627 := by
    simpa [prefixWord, tailWord_450627, baseEnd_450627] using wordTrace_append hprefix tailTrace_450627
  have hstable : (prefixWord ++ tailWord_450627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450627).length < 2 ^ (prefixWord ++ tailWord_450627).sum := by decide
  have hdescent : baseEnd_450627 < baseStart_450627 := by decide
  rcases family_descends (prefixWord ++ tailWord_450627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450644 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_450644 : Nat := 118140960795 + 450644 * 2 ^ 59
def prefixEnd_450644 : Nat := 4983230072969 + 3 ^ 40 * 450644 * 2
def baseEnd_450644 : Nat := 102843100473262260878903

theorem tailTrace_450644 : CollatzResearch.WordTrace tailWord_450644 prefixEnd_450644 102843100473262260878903 := by
  unfold tailWord_450644
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218168489700613356451493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10957557986267484475268657 8218168489700613356451493)
  ·
    refine ⟨1540906591818865004334655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8218168489700613356451493 1540906591818865004334655)
    ·
      refine ⟨2311359887728297506501983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1540906591818865004334655 2311359887728297506501983)
      ·
        refine ⟨3467039831592446259752975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311359887728297506501983 3467039831592446259752975)
        ·
          refine ⟨5200559747388669389629463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467039831592446259752975 5200559747388669389629463)
          ·
            refine ⟨7800839621083004084444195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200559747388669389629463 7800839621083004084444195)
            ·
              refine ⟨11701259431624506126666293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800839621083004084444195 11701259431624506126666293)
              ·
                refine ⟨1096993071714797449374965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11701259431624506126666293 1096993071714797449374965)
                ·
                  refine ⟨102843100473262260878903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1096993071714797449374965 102843100473262260878903)
                  ·
                    rfl

theorem cell21_450644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_450644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450644 prefixEnd_450644 := by exact prefixLift 450644
  have htrace : WordTrace (prefixWord ++ tailWord_450644) baseStart_450644 baseEnd_450644 := by
    simpa [prefixWord, tailWord_450644, baseEnd_450644] using wordTrace_append hprefix tailTrace_450644
  have hstable : (prefixWord ++ tailWord_450644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450644).length < 2 ^ (prefixWord ++ tailWord_450644).sum := by decide
  have hdescent : baseEnd_450644 < baseStart_450644 := by decide
  rcases family_descends (prefixWord ++ tailWord_450644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450678 : List Nat := [5, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_450678 : Nat := 118140960795 + 450678 * 2 ^ 59
def prefixEnd_450678 : Nat := 4983230072969 + 3 ^ 40 * 450678 * 2
def baseEnd_450678 : Nat := 102850859736485757312167

theorem tailTrace_450678 : CollatzResearch.WordTrace tailWord_450678 prefixEnd_450678 102850859736485757312167 := by
  unfold tailWord_450678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027348566329878157477543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10958384707518700346427125 1027348566329878157477543)
  ·
    refine ⟨1541022849494817236216315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1027348566329878157477543 1541022849494817236216315)
    ·
      refine ⟨2311534274242225854324473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541022849494817236216315 2311534274242225854324473)
      ·
        refine ⟨1733650705681669390743355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2311534274242225854324473 1733650705681669390743355)
        ·
          refine ⟨2600476058522504086115033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733650705681669390743355 2600476058522504086115033)
          ·
            refine ⟨1950357043891878064586275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2600476058522504086115033 1950357043891878064586275)
            ·
              refine ⟨2925535565837817096879413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950357043891878064586275 2925535565837817096879413)
              ·
                refine ⟨274268959297295352832445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2925535565837817096879413 274268959297295352832445)
                ·
                  refine ⟨102850859736485757312167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274268959297295352832445 102850859736485757312167)
                  ·
                    rfl

theorem cell21_450678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_450678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450678 prefixEnd_450678 := by exact prefixLift 450678
  have htrace : WordTrace (prefixWord ++ tailWord_450678) baseStart_450678 baseEnd_450678 := by
    simpa [prefixWord, tailWord_450678, baseEnd_450678] using wordTrace_append hprefix tailTrace_450678
  have hstable : (prefixWord ++ tailWord_450678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450678).length < 2 ^ (prefixWord ++ tailWord_450678).sum := by decide
  have hdescent : baseEnd_450678 < baseStart_450678 := by decide
  rcases family_descends (prefixWord ++ tailWord_450678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450720 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_450720 : Nat := 118140960795 + 450720 * 2 ^ 59
def prefixEnd_450720 : Nat := 4983230072969 + 3 ^ 40 * 450720 * 2
def baseEnd_450720 : Nat := 102860444708703017612081

theorem tailTrace_450720 : CollatzResearch.WordTrace tailWord_450720 prefixEnd_450720 102860444708703017612081 := by
  unfold tailWord_450720
  simp only [CollatzResearch.WordTrace]
  refine ⟨8219554463562945846334807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10959405951417261128446409 8219554463562945846334807)
  ·
    refine ⟨12329331695344418769502211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8219554463562945846334807 12329331695344418769502211)
    ·
      refine ⟨18493997543016628154253317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12329331695344418769502211 18493997543016628154253317)
      ·
        refine ⟨3467624539315617778922497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18493997543016628154253317 3467624539315617778922497)
        ·
          refine ⟨2600718404486713334191873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3467624539315617778922497 2600718404486713334191873)
          ·
            refine ⟨1950538803365035000643905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2600718404486713334191873 1950538803365035000643905)
            ·
              refine ⟨1462904102523776250482929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1950538803365035000643905 1462904102523776250482929)
              ·
                refine ⟨1097178076892832187862197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462904102523776250482929 1097178076892832187862197)
                ·
                  refine ⟨102860444708703017612081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1097178076892832187862197 102860444708703017612081)
                  ·
                    rfl

theorem cell21_450720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_450720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450720 prefixEnd_450720 := by exact prefixLift 450720
  have htrace : WordTrace (prefixWord ++ tailWord_450720) baseStart_450720 baseEnd_450720 := by
    simpa [prefixWord, tailWord_450720, baseEnd_450720] using wordTrace_append hprefix tailTrace_450720
  have hstable : (prefixWord ++ tailWord_450720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450720).length < 2 ^ (prefixWord ++ tailWord_450720).sum := by decide
  have hdescent : baseEnd_450720 < baseStart_450720 := by decide
  rcases family_descends (prefixWord ++ tailWord_450720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450858 : List Nat := [3, 1, 4, 2, 2, 1, 8]
def baseStart_450858 : Nat := 118140960795 + 450858 * 2 ^ 59
def prefixEnd_450858 : Nat := 4983230072969 + 3 ^ 40 * 450858 * 2
def baseEnd_450858 : Nat := 11432437576538382701311

theorem tailTrace_450858 : CollatzResearch.WordTrace tailWord_450858 prefixEnd_450858 11432437576538382701311 := by
  unfold tailWord_450858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4111035550156485315298307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10962761467083960840795485 4111035550156485315298307)
  ·
    refine ⟨6166553325234727972947461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4111035550156485315298307 6166553325234727972947461)
    ·
      refine ⟨1156228748481511494927649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6166553325234727972947461 1156228748481511494927649)
      ·
        refine ⟨867171561361133621195737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1156228748481511494927649 867171561361133621195737)
        ·
          refine ⟨650378671020850215896803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 867171561361133621195737 650378671020850215896803)
          ·
            refine ⟨975568006531275323845205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650378671020850215896803 975568006531275323845205)
            ·
              refine ⟨11432437576538382701311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 975568006531275323845205 11432437576538382701311)
              ·
                rfl

theorem cell21_450858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 8].length) (baseStart_450858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450858 prefixEnd_450858 := by exact prefixLift 450858
  have htrace : WordTrace (prefixWord ++ tailWord_450858) baseStart_450858 baseEnd_450858 := by
    simpa [prefixWord, tailWord_450858, baseEnd_450858] using wordTrace_append hprefix tailTrace_450858
  have hstable : (prefixWord ++ tailWord_450858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450858).length < 2 ^ (prefixWord ++ tailWord_450858).sum := by decide
  have hdescent : baseEnd_450858 < baseStart_450858 := by decide
  rcases family_descends (prefixWord ++ tailWord_450858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450917 : List Nat := [1, 3, 1, 3, 1, 5, 7]
def baseStart_450917 : Nat := 118140960795 + 450917 * 2 ^ 59
def prefixEnd_450917 : Nat := 4983230072969 + 3 ^ 40 * 450917 * 2
def baseEnd_450917 : Nat := 11433933643630494758705

theorem tailTrace_450917 : CollatzResearch.WordTrace tailWord_450917 prefixEnd_450917 11433933643630494758705 := by
  unfold tailWord_450917
  simp only [CollatzResearch.WordTrace]
  refine ⟨16446294107412194337591005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10964196071608129558394003 16446294107412194337591005)
  ·
    refine ⟨6167360290279572876596627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16446294107412194337591005 6167360290279572876596627)
    ·
      refine ⟨9251040435419359314894941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6167360290279572876596627 9251040435419359314894941)
      ·
        refine ⟨3469140163282259743085603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9251040435419359314894941 3469140163282259743085603)
        ·
          refine ⟨5203710244923389614628405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469140163282259743085603 5203710244923389614628405)
          ·
            refine ⟨487847835461567776371413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5203710244923389614628405 487847835461567776371413)
            ·
              refine ⟨11433933643630494758705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 487847835461567776371413 11433933643630494758705)
              ·
                rfl

theorem cell21_450917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 7].length) (baseStart_450917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450917 prefixEnd_450917 := by exact prefixLift 450917
  have htrace : WordTrace (prefixWord ++ tailWord_450917) baseStart_450917 baseEnd_450917 := by
    simpa [prefixWord, tailWord_450917, baseEnd_450917] using wordTrace_append hprefix tailTrace_450917
  have hstable : (prefixWord ++ tailWord_450917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450917).length < 2 ^ (prefixWord ++ tailWord_450917).sum := by decide
  have hdescent : baseEnd_450917 < baseStart_450917 := by decide
  rcases family_descends (prefixWord ++ tailWord_450917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450976 : List Nat := [2, 1, 1, 4, 1, 12]
def baseStart_450976 : Nat := 118140960795 + 450976 * 2 ^ 59
def prefixEnd_450976 : Nat := 4983230072969 + 3 ^ 40 * 450976 * 2
def baseEnd_450976 : Nat := 3811809903574202272033

theorem tailTrace_450976 : CollatzResearch.WordTrace tailWord_450976 prefixEnd_450976 3811809903574202272033 := by
  unfold tailWord_450976
  simp only [CollatzResearch.WordTrace]
  refine ⟨8224223007099223706994391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10965630676132298275992521 8224223007099223706994391)
  ·
    refine ⟨12336334510648835560491587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8224223007099223706994391 12336334510648835560491587)
    ·
      refine ⟨18504501765973253340737381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12336334510648835560491587 18504501765973253340737381)
      ·
        refine ⟨3469594081119985001388259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18504501765973253340737381 3469594081119985001388259)
        ·
          refine ⟨5204391121679977502082389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469594081119985001388259 5204391121679977502082389)
          ·
            refine ⟨3811809903574202272033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5204391121679977502082389 3811809903574202272033)
            ·
              rfl

theorem cell21_450976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 12].length) (baseStart_450976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450976 prefixEnd_450976 := by exact prefixLift 450976
  have htrace : WordTrace (prefixWord ++ tailWord_450976) baseStart_450976 baseEnd_450976 := by
    simpa [prefixWord, tailWord_450976, baseEnd_450976] using wordTrace_append hprefix tailTrace_450976
  have hstable : (prefixWord ++ tailWord_450976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450976).length < 2 ^ (prefixWord ++ tailWord_450976).sum := by decide
  have hdescent : baseEnd_450976 < baseStart_450976 := by decide
  rcases family_descends (prefixWord ++ tailWord_450976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450979 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 4]
def baseStart_450979 : Nat := 118140960795 + 450979 * 2 ^ 59
def prefixEnd_450979 : Nat := 4983230072969 + 3 ^ 40 * 450979 * 2
def baseEnd_450979 : Nat := 102919552037376122794885

theorem tailTrace_450979 : CollatzResearch.WordTrace tailWord_450979 prefixEnd_450979 102919552037376122794885 := by
  unfold tailWord_450979
  simp only [CollatzResearch.WordTrace]
  refine ⟨16448555433187578926347991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10965703622125052617565327 16448555433187578926347991)
  ·
    refine ⟨24672833149781368389521987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16448555433187578926347991 24672833149781368389521987)
    ·
      refine ⟨37009249724672052584282981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24672833149781368389521987 37009249724672052584282981)
      ·
        refine ⟨6939234323376009859553059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37009249724672052584282981 6939234323376009859553059)
        ·
          refine ⟨10408851485064014789329589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939234323376009859553059 10408851485064014789329589)
          ·
            refine ⟨975829826724751386499649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10408851485064014789329589 975829826724751386499649)
            ·
              refine ⟨731872370043563539874737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975829826724751386499649 731872370043563539874737)
              ·
                refine ⟨548904277532672654906053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731872370043563539874737 548904277532672654906053)
                ·
                  refine ⟨102919552037376122794885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548904277532672654906053 102919552037376122794885)
                  ·
                    rfl

theorem cell21_450979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 4].length) (baseStart_450979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450979 prefixEnd_450979 := by exact prefixLift 450979
  have htrace : WordTrace (prefixWord ++ tailWord_450979) baseStart_450979 baseEnd_450979 := by
    simpa [prefixWord, tailWord_450979, baseEnd_450979] using wordTrace_append hprefix tailTrace_450979
  have hstable : (prefixWord ++ tailWord_450979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450979).length < 2 ^ (prefixWord ++ tailWord_450979).sum := by decide
  have hdescent : baseEnd_450979 < baseStart_450979 := by decide
  rcases family_descends (prefixWord ++ tailWord_450979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450993 : List Nat := [1, 2, 2, 4, 1, 2, 3, 6]
def baseStart_450993 : Nat := 118140960795 + 450993 * 2 ^ 59
def prefixEnd_450993 : Nat := 4983230072969 + 3 ^ 40 * 450993 * 2
def baseEnd_450993 : Nat := 34307582342705069853841

theorem tailTrace_450993 : CollatzResearch.WordTrace tailWord_450993 prefixEnd_450993 34307582342705069853841 := by
  unfold tailWord_450993
  simp only [CollatzResearch.WordTrace]
  refine ⟨16449066055136859317357633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10966044036757906211571755 16449066055136859317357633)
  ·
    refine ⟨12336799541352644488018225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16449066055136859317357633 12336799541352644488018225)
    ·
      refine ⟨9252599656014483366013669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12336799541352644488018225 9252599656014483366013669)
      ·
        refine ⟨1734862435502715631127563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9252599656014483366013669 1734862435502715631127563)
        ·
          refine ⟨2602293653254073446691345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734862435502715631127563 2602293653254073446691345)
          ·
            refine ⟨1951720239940555085018509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2602293653254073446691345 1951720239940555085018509)
            ·
              refine ⟨731895089977708156881941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1951720239940555085018509 731895089977708156881941)
              ·
                refine ⟨34307582342705069853841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 731895089977708156881941 34307582342705069853841)
                ·
                  rfl

theorem cell21_450993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 6].length) (baseStart_450993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_450993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_450993 prefixEnd_450993 := by exact prefixLift 450993
  have htrace : WordTrace (prefixWord ++ tailWord_450993) baseStart_450993 baseEnd_450993 := by
    simpa [prefixWord, tailWord_450993, baseEnd_450993] using wordTrace_append hprefix tailTrace_450993
  have hstable : (prefixWord ++ tailWord_450993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450993).length < 2 ^ (prefixWord ++ tailWord_450993).sum := by decide
  have hdescent : baseEnd_450993 < baseStart_450993 := by decide
  rcases family_descends (prefixWord ++ tailWord_450993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451052 : List Nat := [2, 2, 1, 1, 2, 1, 4, 8]
def baseStart_451052 : Nat := 118140960795 + 451052 * 2 ^ 59
def prefixEnd_451052 : Nat := 4983230072969 + 3 ^ 40 * 451052 * 2
def baseEnd_451052 : Nat := 34312070543981406026023

theorem tailTrace_451052 : CollatzResearch.WordTrace tailWord_451052 prefixEnd_451052 34312070543981406026023 := by
  unfold tailWord_451052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8225608980961556196877705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10967478641282074929170273 8225608980961556196877705)
  ·
    refine ⟨6169206735721167147658279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8225608980961556196877705 6169206735721167147658279)
    ·
      refine ⟨9253810103581750721487419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6169206735721167147658279 9253810103581750721487419)
      ·
        refine ⟨13880715155372626082231129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9253810103581750721487419 13880715155372626082231129)
        ·
          refine ⟨10410536366529469561673347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13880715155372626082231129 10410536366529469561673347)
          ·
            refine ⟨15615804549794204342510021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10410536366529469561673347 15615804549794204342510021)
            ·
              refine ⟨2927963353086413314220629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15615804549794204342510021 2927963353086413314220629)
              ·
                refine ⟨34312070543981406026023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2927963353086413314220629 34312070543981406026023)
                ·
                  rfl

theorem cell21_451052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_451052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451052 prefixEnd_451052 := by exact prefixLift 451052
  have htrace : WordTrace (prefixWord ++ tailWord_451052) baseStart_451052 baseEnd_451052 := by
    simpa [prefixWord, tailWord_451052, baseEnd_451052] using wordTrace_append hprefix tailTrace_451052
  have hstable : (prefixWord ++ tailWord_451052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451052).length < 2 ^ (prefixWord ++ tailWord_451052).sum := by decide
  have hdescent : baseEnd_451052 < baseStart_451052 := by decide
  rcases family_descends (prefixWord ++ tailWord_451052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451100 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_451100 : Nat := 118140960795 + 451100 * 2 ^ 59
def prefixEnd_451100 : Nat := 4983230072969 + 3 ^ 40 * 451100 * 2
def baseEnd_451100 : Nat := 102947165885906801277971

theorem tailTrace_451100 : CollatzResearch.WordTrace tailWord_451100 prefixEnd_451100 102947165885906801277971 := by
  unfold tailWord_451100
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226484332874608295751377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10968645777166144394335169 8226484332874608295751377)
  ·
    refine ⟨6169863249655956221813533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8226484332874608295751377 6169863249655956221813533)
    ·
      refine ⟨2313698718620983583180075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6169863249655956221813533 2313698718620983583180075)
      ·
        refine ⟨3470548077931475374770113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313698718620983583180075 3470548077931475374770113)
        ·
          refine ⟨2602911058448606531077585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3470548077931475374770113 2602911058448606531077585)
          ·
            refine ⟨1952183293836454898308189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2602911058448606531077585 1952183293836454898308189)
            ·
              refine ⟨732068735188670586865571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1952183293836454898308189 732068735188670586865571)
              ·
                refine ⟨1098103102783005880298357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732068735188670586865571 1098103102783005880298357)
                ·
                  refine ⟨102947165885906801277971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1098103102783005880298357 102947165885906801277971)
                  ·
                    rfl

theorem cell21_451100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_451100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451100 prefixEnd_451100 := by exact prefixLift 451100
  have htrace : WordTrace (prefixWord ++ tailWord_451100) baseStart_451100 baseEnd_451100 := by
    simpa [prefixWord, tailWord_451100, baseEnd_451100] using wordTrace_append hprefix tailTrace_451100
  have hstable : (prefixWord ++ tailWord_451100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451100).length < 2 ^ (prefixWord ++ tailWord_451100).sum := by decide
  have hdescent : baseEnd_451100 < baseStart_451100 := by decide
  rcases family_descends (prefixWord ++ tailWord_451100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451128 : List Nat := [2, 1, 2, 1, 4, 1, 1, 9]
def baseStart_451128 : Nat := 118140960795 + 451128 * 2 ^ 59
def prefixEnd_451128 : Nat := 4983230072969 + 3 ^ 40 * 451128 * 2
def baseEnd_451128 : Nat := 34317851955794991603749

theorem tailTrace_451128 : CollatzResearch.WordTrace tailWord_451128 prefixEnd_451128 34317851955794991603749 := by
  unfold tailWord_451128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226994954823888686761019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10969326606431851582348025 8226994954823888686761019)
  ·
    refine ⟨12340492432235833030141529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8226994954823888686761019 12340492432235833030141529)
    ·
      refine ⟨9255369324176874772606147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12340492432235833030141529 9255369324176874772606147)
      ·
        refine ⟨13883053986265312158909221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255369324176874772606147 13883053986265312158909221)
        ·
          refine ⟨2603072622424746029795479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13883053986265312158909221 2603072622424746029795479)
          ·
            refine ⟨3904608933637119044693219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603072622424746029795479 3904608933637119044693219)
            ·
              refine ⟨5856913400455678567039829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904608933637119044693219 5856913400455678567039829)
              ·
                refine ⟨34317851955794991603749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5856913400455678567039829 34317851955794991603749)
                ·
                  rfl

theorem cell21_451128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_451128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451128 prefixEnd_451128 := by exact prefixLift 451128
  have htrace : WordTrace (prefixWord ++ tailWord_451128) baseStart_451128 baseEnd_451128 := by
    simpa [prefixWord, tailWord_451128, baseEnd_451128] using wordTrace_append hprefix tailTrace_451128
  have hstable : (prefixWord ++ tailWord_451128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451128).length < 2 ^ (prefixWord ++ tailWord_451128).sum := by decide
  have hdescent : baseEnd_451128 < baseStart_451128 := by decide
  rcases family_descends (prefixWord ++ tailWord_451128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451159 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 5]
def baseStart_451159 : Nat := 118140960795 + 451159 * 2 ^ 59
def prefixEnd_451159 : Nat := 4983230072969 + 3 ^ 40 * 451159 * 2
def baseEnd_451159 : Nat := 102960630489735809794517

theorem tailTrace_451159 : CollatzResearch.WordTrace tailWord_451159 prefixEnd_451159 102960630489735809794517 := by
  unfold tailWord_451159
  simp only [CollatzResearch.WordTrace]
  refine ⟨16455120572535469667900531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10970080381690313111933687 16455120572535469667900531)
  ·
    refine ⟨24682680858803204501850797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16455120572535469667900531 24682680858803204501850797)
    ·
      refine ⟨9256005322051201688194049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24682680858803204501850797 9256005322051201688194049)
      ·
        refine ⟨6942003991538401266145537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9256005322051201688194049 6942003991538401266145537)
        ·
          refine ⟨5206502993653800949609153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6942003991538401266145537 5206502993653800949609153)
          ·
            refine ⟨3904877245240350712206865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5206502993653800949609153 3904877245240350712206865)
            ·
              refine ⟨2928657933930263034155149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3904877245240350712206865 2928657933930263034155149)
              ·
                refine ⟨1098246725223848637808181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2928657933930263034155149 1098246725223848637808181)
                ·
                  refine ⟨102960630489735809794517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1098246725223848637808181 102960630489735809794517)
                  ·
                    rfl

theorem cell21_451159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_451159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451159 prefixEnd_451159 := by exact prefixLift 451159
  have htrace : WordTrace (prefixWord ++ tailWord_451159) baseStart_451159 baseEnd_451159 := by
    simpa [prefixWord, tailWord_451159, baseEnd_451159] using wordTrace_append hprefix tailTrace_451159
  have hstable : (prefixWord ++ tailWord_451159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451159).length < 2 ^ (prefixWord ++ tailWord_451159).sum := by decide
  have hdescent : baseEnd_451159 < baseStart_451159 := by decide
  rcases family_descends (prefixWord ++ tailWord_451159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451193 : List Nat := [1, 2, 1, 3, 3, 3, 2, 3, 3]
def baseStart_451193 : Nat := 118140960795 + 451193 * 2 ^ 59
def prefixEnd_451193 : Nat := 4983230072969 + 3 ^ 40 * 451193 * 2
def baseEnd_451193 : Nat := 102968389752959306227781

theorem tailTrace_451193 : CollatzResearch.WordTrace tailWord_451193 prefixEnd_451193 102968389752959306227781 := by
  unfold tailWord_451193
  simp only [CollatzResearch.WordTrace]
  refine ⟨16456360654412293474638233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10970907102941528983092155 16456360654412293474638233)
  ·
    refine ⟨12342270490809220105978675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16456360654412293474638233 12342270490809220105978675)
    ·
      refine ⟨18513405736213830158968013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12342270490809220105978675 18513405736213830158968013)
      ·
        refine ⟨6942527151080186309613005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18513405736213830158968013 6942527151080186309613005)
        ·
          refine ⟨2603447681655069866104877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6942527151080186309613005 2603447681655069866104877)
          ·
            refine ⟨976292880620651199789329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2603447681655069866104877 976292880620651199789329)
            ·
              refine ⟨732219660465488399841997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976292880620651199789329 732219660465488399841997)
              ·
                refine ⟨274582372674558149940749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 732219660465488399841997 274582372674558149940749)
                ·
                  refine ⟨102968389752959306227781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274582372674558149940749 102968389752959306227781)
                  ·
                    rfl

theorem cell21_451193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_451193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451193 prefixEnd_451193 := by exact prefixLift 451193
  have htrace : WordTrace (prefixWord ++ tailWord_451193) baseStart_451193 baseEnd_451193 := by
    simpa [prefixWord, tailWord_451193, baseEnd_451193] using wordTrace_append hprefix tailTrace_451193
  have hstable : (prefixWord ++ tailWord_451193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451193).length < 2 ^ (prefixWord ++ tailWord_451193).sum := by decide
  have hdescent : baseEnd_451193 < baseStart_451193 := by decide
  rcases family_descends (prefixWord ++ tailWord_451193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451393 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 4]
def baseStart_451393 : Nat := 118140960795 + 451393 * 2 ^ 59
def prefixEnd_451393 : Nat := 4983230072969 + 3 ^ 40 * 451393 * 2
def baseEnd_451393 : Nat := 103014032477803402894039

theorem tailTrace_451393 : CollatzResearch.WordTrace tailWord_451393 prefixEnd_451393 103014032477803402894039 := by
  unfold tailWord_451393
  simp only [CollatzResearch.WordTrace]
  refine ⟨16463655253687727631918833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10975770169125151754612555 16463655253687727631918833)
  ·
    refine ⟨12347741440265795723939125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16463655253687727631918833 12347741440265795723939125)
    ·
      refine ⟨1157600760024918349119293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12347741440265795723939125 1157600760024918349119293)
      ·
        refine ⟨434100285009344380919735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1157600760024918349119293 434100285009344380919735)
        ·
          refine ⟨651150427514016571379603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434100285009344380919735 651150427514016571379603)
          ·
            refine ⟨976725641271024857069405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651150427514016571379603 976725641271024857069405)
            ·
              refine ⟨366272115476634321401027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 976725641271024857069405 366272115476634321401027)
              ·
                refine ⟨549408173214951482101541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366272115476634321401027 549408173214951482101541)
                ·
                  refine ⟨103014032477803402894039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549408173214951482101541 103014032477803402894039)
                  ·
                    rfl

theorem cell21_451393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_451393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451393 prefixEnd_451393 := by exact prefixLift 451393
  have htrace : WordTrace (prefixWord ++ tailWord_451393) baseStart_451393 baseEnd_451393 := by
    simpa [prefixWord, tailWord_451393, baseEnd_451393] using wordTrace_append hprefix tailTrace_451393
  have hstable : (prefixWord ++ tailWord_451393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451393).length < 2 ^ (prefixWord ++ tailWord_451393).sum := by decide
  have hdescent : baseEnd_451393 < baseStart_451393 := by decide
  rcases family_descends (prefixWord ++ tailWord_451393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451432 : List Nat := [2, 1, 4, 2, 1, 2, 9]
def baseStart_451432 : Nat := 118140960795 + 451432 * 2 ^ 59
def prefixEnd_451432 : Nat := 4983230072969 + 3 ^ 40 * 451432 * 2
def baseEnd_451432 : Nat := 11446992534349777971551

theorem tailTrace_451432 : CollatzResearch.WordTrace tailWord_451432 prefixEnd_451432 11446992534349777971551 := by
  unfold tailWord_451432
  simp only [CollatzResearch.WordTrace]
  refine ⟨8232538850273218646294275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10976718467030958195059033 8232538850273218646294275)
  ·
    refine ⟨12348808275409827969441413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8232538850273218646294275 12348808275409827969441413)
    ·
      refine ⟨2315401551639342744270265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12348808275409827969441413 2315401551639342744270265)
      ·
        refine ⟨1736551163729507058202699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2315401551639342744270265 1736551163729507058202699)
        ·
          refine ⟨2604826745594260587304049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736551163729507058202699 2604826745594260587304049)
          ·
            refine ⟨1953620059195695440478037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2604826745594260587304049 1953620059195695440478037)
            ·
              refine ⟨11446992534349777971551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1953620059195695440478037 11446992534349777971551)
              ·
                rfl

theorem cell21_451432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 9].length) (baseStart_451432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451432 prefixEnd_451432 := by exact prefixLift 451432
  have htrace : WordTrace (prefixWord ++ tailWord_451432) baseStart_451432 baseEnd_451432 := by
    simpa [prefixWord, tailWord_451432, baseEnd_451432] using wordTrace_append hprefix tailTrace_451432
  have hstable : (prefixWord ++ tailWord_451432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451432).length < 2 ^ (prefixWord ++ tailWord_451432).sum := by decide
  have hdescent : baseEnd_451432 < baseStart_451432 := by decide
  rcases family_descends (prefixWord ++ tailWord_451432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451438 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_451438 : Nat := 118140960795 + 451438 * 2 ^ 59
def prefixEnd_451438 : Nat := 4983230072969 + 3 ^ 40 * 451438 * 2
def baseEnd_451438 : Nat := 103024302090893324643947

theorem tailTrace_451438 : CollatzResearch.WordTrace tailWord_451438 prefixEnd_451438 103024302090893324643947 := by
  unfold tailWord_451438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2058162067315587539663371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10976864359016466878204645 2058162067315587539663371)
  ·
    refine ⟨3087243100973381309495057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2058162067315587539663371 3087243100973381309495057)
    ·
      refine ⟨2315432325730035982121293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3087243100973381309495057 2315432325730035982121293)
      ·
        refine ⟨868287122148763493295485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2315432325730035982121293 868287122148763493295485)
        ·
          refine ⟨325607670805786309985807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 868287122148763493295485 325607670805786309985807)
          ·
            refine ⟨488411506208679464978711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325607670805786309985807 488411506208679464978711)
            ·
              refine ⟨732617259313019197468067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488411506208679464978711 732617259313019197468067)
              ·
                refine ⟨1098925888969528796202101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732617259313019197468067 1098925888969528796202101)
                ·
                  refine ⟨103024302090893324643947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1098925888969528796202101 103024302090893324643947)
                  ·
                    rfl

theorem cell21_451438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_451438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451438 prefixEnd_451438 := by exact prefixLift 451438
  have htrace : WordTrace (prefixWord ++ tailWord_451438) baseStart_451438 baseEnd_451438 := by
    simpa [prefixWord, tailWord_451438, baseEnd_451438] using wordTrace_append hprefix tailTrace_451438
  have hstable : (prefixWord ++ tailWord_451438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451438).length < 2 ^ (prefixWord ++ tailWord_451438).sum := by decide
  have hdescent : baseEnd_451438 < baseStart_451438 := by decide
  rcases family_descends (prefixWord ++ tailWord_451438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451615 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 5]
def baseStart_451615 : Nat := 118140960795 + 451615 * 2 ^ 59
def prefixEnd_451615 : Nat := 4983230072969 + 3 ^ 40 * 451615 * 2
def baseEnd_451615 : Nat := 103064695902380350193585

theorem tailTrace_451615 : CollatzResearch.WordTrace tailWord_451615 prefixEnd_451615 103064695902380350193585 := by
  unfold tailWord_451615
  simp only [CollatzResearch.WordTrace]
  refine ⟨16471752258883459546500299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10981168172588973031000199 16471752258883459546500299)
  ·
    refine ⟨24707628388325189319750449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16471752258883459546500299 24707628388325189319750449)
    ·
      refine ⟨18530721291243891989812837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24707628388325189319750449 18530721291243891989812837)
      ·
        refine ⟨3474510242108229748089907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18530721291243891989812837 3474510242108229748089907)
        ·
          refine ⟨5211765363162344622134861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474510242108229748089907 5211765363162344622134861)
          ·
            refine ⟨1954412011185879233300573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5211765363162344622134861 1954412011185879233300573)
            ·
              refine ⟨732904504194704712487715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1954412011185879233300573 732904504194704712487715)
              ·
                refine ⟨1099356756292057068731573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732904504194704712487715 1099356756292057068731573)
                ·
                  refine ⟨103064695902380350193585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1099356756292057068731573 103064695902380350193585)
                  ·
                    rfl

theorem cell21_451615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 5].length) (baseStart_451615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451615 prefixEnd_451615 := by exact prefixLift 451615
  have htrace : WordTrace (prefixWord ++ tailWord_451615) baseStart_451615 baseEnd_451615 := by
    simpa [prefixWord, tailWord_451615, baseEnd_451615] using wordTrace_append hprefix tailTrace_451615
  have hstable : (prefixWord ++ tailWord_451615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451615).length < 2 ^ (prefixWord ++ tailWord_451615).sum := by decide
  have hdescent : baseEnd_451615 < baseStart_451615 := by decide
  rcases family_descends (prefixWord ++ tailWord_451615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451666 : List Nat := [3, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_451666 : Nat := 118140960795 + 451666 * 2 ^ 59
def prefixEnd_451666 : Nat := 4983230072969 + 3 ^ 40 * 451666 * 2
def baseEnd_451666 : Nat := 103076334797215594843481

theorem tailTrace_451666 : CollatzResearch.WordTrace tailWord_451666 prefixEnd_451666 103076334797215594843481 := by
  unfold tailWord_451666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4118403095424673814151713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10982408254465796837737901 4118403095424673814151713)
  ·
    refine ⟨3088802321568505360613785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4118403095424673814151713 3088802321568505360613785)
    ·
      refine ⟨2316601741176379020460339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3088802321568505360613785 2316601741176379020460339)
      ·
        refine ⟨3474902611764568530690509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316601741176379020460339 3474902611764568530690509)
        ·
          refine ⟨1303088479411713199008941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3474902611764568530690509 1303088479411713199008941)
          ·
            refine ⟨488658179779392449628353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1303088479411713199008941 488658179779392449628353)
            ·
              refine ⟨366493634834544337221265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488658179779392449628353 366493634834544337221265)
              ·
                refine ⟨274870226125908252915949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366493634834544337221265 274870226125908252915949)
                ·
                  refine ⟨103076334797215594843481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274870226125908252915949 103076334797215594843481)
                  ·
                    rfl

theorem cell21_451666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_451666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451666 prefixEnd_451666 := by exact prefixLift 451666
  have htrace : WordTrace (prefixWord ++ tailWord_451666) baseStart_451666 baseEnd_451666 := by
    simpa [prefixWord, tailWord_451666, baseEnd_451666] using wordTrace_append hprefix tailTrace_451666
  have hstable : (prefixWord ++ tailWord_451666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451666).length < 2 ^ (prefixWord ++ tailWord_451666).sum := by decide
  have hdescent : baseEnd_451666 < baseStart_451666 := by decide
  rcases family_descends (prefixWord ++ tailWord_451666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451708 : List Nat := [2, 2, 2, 1, 1, 3, 4, 3, 3]
def baseStart_451708 : Nat := 118140960795 + 451708 * 2 ^ 59
def prefixEnd_451708 : Nat := 4983230072969 + 3 ^ 40 * 451708 * 2
def baseEnd_451708 : Nat := 103085919769432855143395

theorem tailTrace_451708 : CollatzResearch.WordTrace tailWord_451708 prefixEnd_451708 103085919769432855143395 := by
  unfold tailWord_451708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8237572123773268214817889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10983429498364357619757185 8237572123773268214817889)
  ·
    refine ⟨6178179092829951161113417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8237572123773268214817889 6178179092829951161113417)
    ·
      refine ⟨4633634319622463370835063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6178179092829951161113417 4633634319622463370835063)
      ·
        refine ⟨6950451479433695056252595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4633634319622463370835063 6950451479433695056252595)
        ·
          refine ⟨10425677219150542584378893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950451479433695056252595 10425677219150542584378893)
          ·
            refine ⟨3909628957181453469142085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10425677219150542584378893 3909628957181453469142085)
            ·
              refine ⟨733055429471522525464141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3909628957181453469142085 733055429471522525464141)
              ·
                refine ⟨274895786051820947049053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 733055429471522525464141 274895786051820947049053)
                ·
                  refine ⟨103085919769432855143395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274895786051820947049053 103085919769432855143395)
                  ·
                    rfl

theorem cell21_451708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_451708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451708 prefixEnd_451708 := by exact prefixLift 451708
  have htrace : WordTrace (prefixWord ++ tailWord_451708) baseStart_451708 baseEnd_451708 := by
    simpa [prefixWord, tailWord_451708, baseEnd_451708] using wordTrace_append hprefix tailTrace_451708
  have hstable : (prefixWord ++ tailWord_451708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451708).length < 2 ^ (prefixWord ++ tailWord_451708).sum := by decide
  have hdescent : baseEnd_451708 < baseStart_451708 := by decide
  rcases family_descends (prefixWord ++ tailWord_451708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451781 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 4]
def baseStart_451781 : Nat := 118140960795 + 451781 * 2 ^ 59
def prefixEnd_451781 : Nat := 4983230072969 + 3 ^ 40 * 451781 * 2
def baseEnd_451781 : Nat := 103102579364000950426579

theorem tailTrace_451781 : CollatzResearch.WordTrace tailWord_451781 prefixEnd_451781 103102579364000950426579 := by
  unfold tailWord_451781
  simp only [CollatzResearch.WordTrace]
  refine ⟨16477806776282069897043197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10985204517521379931362131 16477806776282069897043197)
  ·
    refine ⟨6179177541105776211391199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16477806776282069897043197 6179177541105776211391199)
    ·
      refine ⟨9268766311658664317086799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6179177541105776211391199 9268766311658664317086799)
      ·
        refine ⟨13903149467487996475630199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9268766311658664317086799 13903149467487996475630199)
        ·
          refine ⟨20854724201231994713445299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13903149467487996475630199 20854724201231994713445299)
          ·
            refine ⟨31282086301847992070167949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20854724201231994713445299 31282086301847992070167949)
            ·
              refine ⟨11730782363192997026312981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31282086301847992070167949 11730782363192997026312981)
              ·
                refine ⟨549880423274671735608421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11730782363192997026312981 549880423274671735608421)
                ·
                  refine ⟨103102579364000950426579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549880423274671735608421 103102579364000950426579)
                  ·
                    rfl

theorem cell21_451781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_451781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451781 prefixEnd_451781 := by exact prefixLift 451781
  have htrace : WordTrace (prefixWord ++ tailWord_451781) baseStart_451781 baseEnd_451781 := by
    simpa [prefixWord, tailWord_451781, baseEnd_451781] using wordTrace_append hprefix tailTrace_451781
  have hstable : (prefixWord ++ tailWord_451781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451781).length < 2 ^ (prefixWord ++ tailWord_451781).sum := by decide
  have hdescent : baseEnd_451781 < baseStart_451781 := by decide
  rcases family_descends (prefixWord ++ tailWord_451781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451857 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 4]
def baseStart_451857 : Nat := 118140960795 + 451857 * 2 ^ 59
def prefixEnd_451857 : Nat := 4983230072969 + 3 ^ 40 * 451857 * 2
def baseEnd_451857 : Nat := 103119923599441707159757

theorem tailTrace_451857 : CollatzResearch.WordTrace tailWord_451857 prefixEnd_451857 103119923599441707159757 := by
  unfold tailWord_451857
  simp only [CollatzResearch.WordTrace]
  refine ⟨16480578724006734876809825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10987052482671156584539883 16480578724006734876809825)
  ·
    refine ⟨12360434043005051157607369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16480578724006734876809825 12360434043005051157607369)
    ·
      refine ⟨9270325532253788368205527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12360434043005051157607369 9270325532253788368205527)
      ·
        refine ⟨13905488298380682552308291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270325532253788368205527 13905488298380682552308291)
        ·
          refine ⟨20858232447571023828462437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13905488298380682552308291 20858232447571023828462437)
          ·
            refine ⟨3910918583919566967836707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20858232447571023828462437 3910918583919566967836707)
            ·
              refine ⟨5866377875879350451755061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910918583919566967836707 5866377875879350451755061)
              ·
                refine ⟨549972925863689104852037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5866377875879350451755061 549972925863689104852037)
                ·
                  refine ⟨103119923599441707159757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549972925863689104852037 103119923599441707159757)
                  ·
                    rfl

theorem cell21_451857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_451857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451857 prefixEnd_451857 := by exact prefixLift 451857
  have htrace : WordTrace (prefixWord ++ tailWord_451857) baseStart_451857 baseEnd_451857 := by
    simpa [prefixWord, tailWord_451857, baseEnd_451857] using wordTrace_append hprefix tailTrace_451857
  have hstable : (prefixWord ++ tailWord_451857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451857).length < 2 ^ (prefixWord ++ tailWord_451857).sum := by decide
  have hdescent : baseEnd_451857 < baseStart_451857 := by decide
  rcases family_descends (prefixWord ++ tailWord_451857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451908 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_451908 : Nat := 118140960795 + 451908 * 2 ^ 59
def prefixEnd_451908 : Nat := 4983230072969 + 3 ^ 40 * 451908 * 2
def baseEnd_451908 : Nat := 103131562494276951809653

theorem tailTrace_451908 : CollatzResearch.WordTrace tailWord_451908 prefixEnd_451908 103131562494276951809653 := by
  unfold tailWord_451908
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241219423410985293458189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10988292564547980391277585 8241219423410985293458189)
  ·
    refine ⟨3090457283779119485046821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8241219423410985293458189 3090457283779119485046821)
    ·
      refine ⟨579460740708584903446279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3090457283779119485046821 579460740708584903446279)
      ·
        refine ⟨869191111062877355169419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579460740708584903446279 869191111062877355169419)
        ·
          refine ⟨1303786666594316032754129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869191111062877355169419 1303786666594316032754129)
          ·
            refine ⟨977839999945737024565597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1303786666594316032754129 977839999945737024565597)
            ·
              refine ⟨366689999979651384212099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 977839999945737024565597 366689999979651384212099)
              ·
                refine ⟨550034999969477076318149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366689999979651384212099 550034999969477076318149)
                ·
                  refine ⟨103131562494276951809653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550034999969477076318149 103131562494276951809653)
                  ·
                    rfl

theorem cell21_451908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_451908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451908 prefixEnd_451908 := by exact prefixLift 451908
  have htrace : WordTrace (prefixWord ++ tailWord_451908) baseStart_451908 baseEnd_451908 := by
    simpa [prefixWord, tailWord_451908, baseEnd_451908] using wordTrace_append hprefix tailTrace_451908
  have hstable : (prefixWord ++ tailWord_451908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451908).length < 2 ^ (prefixWord ++ tailWord_451908).sum := by decide
  have hdescent : baseEnd_451908 < baseStart_451908 := by decide
  rcases family_descends (prefixWord ++ tailWord_451908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451936 : List Nat := [2, 1, 1, 3, 4, 1, 3, 3, 3]
def baseStart_451936 : Nat := 118140960795 + 451936 * 2 ^ 59
def prefixEnd_451936 : Nat := 4983230072969 + 3 ^ 40 * 451936 * 2
def baseEnd_451936 : Nat := 103137952475755125342929

theorem tailTrace_451936 : CollatzResearch.WordTrace tailWord_451936 prefixEnd_451936 103137952475755125342929 := by
  unfold tailWord_451936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241730045360265684467831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10988973393813687579290441 8241730045360265684467831)
  ·
    refine ⟨12362595068040398526701747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241730045360265684467831 12362595068040398526701747)
    ·
      refine ⟨18543892602060597790052621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12362595068040398526701747 18543892602060597790052621)
      ·
        refine ⟨6953959725772724171269733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18543892602060597790052621 6953959725772724171269733)
        ·
          refine ⟨1303867448582385782113075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6953959725772724171269733 1303867448582385782113075)
          ·
            refine ⟨1955801172873578673169613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303867448582385782113075 1955801172873578673169613)
            ·
              refine ⟨733425439827592002438605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1955801172873578673169613 733425439827592002438605)
              ·
                refine ⟨275034539935347000914477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 733425439827592002438605 275034539935347000914477)
                ·
                  refine ⟨103137952475755125342929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275034539935347000914477 103137952475755125342929)
                  ·
                    rfl

theorem cell21_451936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_451936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_451936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_451936 prefixEnd_451936 := by exact prefixLift 451936
  have htrace : WordTrace (prefixWord ++ tailWord_451936) baseStart_451936 baseEnd_451936 := by
    simpa [prefixWord, tailWord_451936, baseEnd_451936] using wordTrace_append hprefix tailTrace_451936
  have hstable : (prefixWord ++ tailWord_451936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451936).length < 2 ^ (prefixWord ++ tailWord_451936).sum := by decide
  have hdescent : baseEnd_451936 < baseStart_451936 := by decide
  rcases family_descends (prefixWord ++ tailWord_451936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452012 : List Nat := [2, 2, 1, 1, 1, 1, 8, 2, 3]
def baseStart_452012 : Nat := 118140960795 + 452012 * 2 ^ 59
def prefixEnd_452012 : Nat := 4983230072969 + 3 ^ 40 * 452012 * 2
def baseEnd_452012 : Nat := 103155296711195882076107

theorem tailTrace_452012 : CollatzResearch.WordTrace tailWord_452012 prefixEnd_452012 103155296711195882076107 := by
  unfold tailWord_452012
  simp only [CollatzResearch.WordTrace]
  refine ⟨8243116019222598174351145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10990821358963464232468193 8243116019222598174351145)
  ·
    refine ⟨6182337014416948630763359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8243116019222598174351145 6182337014416948630763359)
    ·
      refine ⟨9273505521625422946145039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6182337014416948630763359 9273505521625422946145039)
      ·
        refine ⟨13910258282438134419217559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9273505521625422946145039 13910258282438134419217559)
        ·
          refine ⟨20865387423657201628826339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13910258282438134419217559 20865387423657201628826339)
          ·
            refine ⟨31298081135485802443239509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20865387423657201628826339 31298081135485802443239509)
            ·
              refine ⟨366774388306474247381713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 31298081135485802443239509 366774388306474247381713)
              ·
                refine ⟨275080791229855685536285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366774388306474247381713 275080791229855685536285)
                ·
                  refine ⟨103155296711195882076107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275080791229855685536285 103155296711195882076107)
                  ·
                    rfl

theorem cell21_452012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_452012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452012 prefixEnd_452012 := by exact prefixLift 452012
  have htrace : WordTrace (prefixWord ++ tailWord_452012) baseStart_452012 baseEnd_452012 := by
    simpa [prefixWord, tailWord_452012, baseEnd_452012] using wordTrace_append hprefix tailTrace_452012
  have hstable : (prefixWord ++ tailWord_452012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452012).length < 2 ^ (prefixWord ++ tailWord_452012).sum := by decide
  have hdescent : baseEnd_452012 < baseStart_452012 := by decide
  rcases family_descends (prefixWord ++ tailWord_452012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452040 : List Nat := [2, 1, 3, 1, 3, 1, 5, 5]
def baseStart_452040 : Nat := 118140960795 + 452040 * 2 ^ 59
def prefixEnd_452040 : Nat := 4983230072969 + 3 ^ 40 * 452040 * 2
def baseEnd_452040 : Nat := 34387228897558018536461

theorem tailTrace_452040 : CollatzResearch.WordTrace tailWord_452040 prefixEnd_452040 34387228897558018536461 := by
  unfold tailWord_452040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8243626641171878565360787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10991502188229171420481049 8243626641171878565360787)
  ·
    refine ⟨12365439961757817848041181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8243626641171878565360787 12365439961757817848041181)
    ·
      refine ⟨4637039985659181693015443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12365439961757817848041181 4637039985659181693015443)
      ·
        refine ⟨6955559978488772539523165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637039985659181693015443 6955559978488772539523165)
        ·
          refine ⟨2608334991933289702321187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6955559978488772539523165 2608334991933289702321187)
          ·
            refine ⟨3912502487899934553481781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608334991933289702321187 3912502487899934553481781)
            ·
              refine ⟨366797108240618864388917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3912502487899934553481781 366797108240618864388917)
              ·
                refine ⟨34387228897558018536461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 366797108240618864388917 34387228897558018536461)
                ·
                  rfl

theorem cell21_452040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_452040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452040 prefixEnd_452040 := by exact prefixLift 452040
  have htrace : WordTrace (prefixWord ++ tailWord_452040) baseStart_452040 baseEnd_452040 := by
    simpa [prefixWord, tailWord_452040, baseEnd_452040] using wordTrace_append hprefix tailTrace_452040
  have hstable : (prefixWord ++ tailWord_452040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452040).length < 2 ^ (prefixWord ++ tailWord_452040).sum := by decide
  have hdescent : baseEnd_452040 < baseStart_452040 := by decide
  rcases family_descends (prefixWord ++ tailWord_452040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452071 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 5]
def baseStart_452071 : Nat := 118140960795 + 452071 * 2 ^ 59
def prefixEnd_452071 : Nat := 4983230072969 + 3 ^ 40 * 452071 * 2
def baseEnd_452071 : Nat := 103168761315024890592653

theorem tailTrace_452071 : CollatzResearch.WordTrace tailWord_452071 prefixEnd_452071 103168761315024890592653 := by
  unfold tailWord_452071
  simp only [CollatzResearch.WordTrace]
  refine ⟨16488383945231449425100067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10992255963487632950066711 16488383945231449425100067)
  ·
    refine ⟨24732575917847174137650101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16488383945231449425100067 24732575917847174137650101)
    ·
      refine ⟨2318678992298172575404697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24732575917847174137650101 2318678992298172575404697)
      ·
        refine ⟨1739009244223629431553523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2318678992298172575404697 1739009244223629431553523)
        ·
          refine ⟨2608513866335444147330285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739009244223629431553523 2608513866335444147330285)
          ·
            refine ⟨978192699875791555248857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2608513866335444147330285 978192699875791555248857)
            ·
              refine ⟨733644524906843666436643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978192699875791555248857 733644524906843666436643)
              ·
                refine ⟨1100466787360265499654965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733644524906843666436643 1100466787360265499654965)
                ·
                  refine ⟨103168761315024890592653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1100466787360265499654965 103168761315024890592653)
                  ·
                    rfl

theorem cell21_452071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 5].length) (baseStart_452071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452071 prefixEnd_452071 := by exact prefixLift 452071
  have htrace : WordTrace (prefixWord ++ tailWord_452071) baseStart_452071 baseEnd_452071 := by
    simpa [prefixWord, tailWord_452071, baseEnd_452071] using wordTrace_append hprefix tailTrace_452071
  have hstable : (prefixWord ++ tailWord_452071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452071).length < 2 ^ (prefixWord ++ tailWord_452071).sum := by decide
  have hdescent : baseEnd_452071 < baseStart_452071 := by decide
  rcases family_descends (prefixWord ++ tailWord_452071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452136 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_452136 : Nat := 118140960795 + 452136 * 2 ^ 59
def prefixEnd_452136 : Nat := 4983230072969 + 3 ^ 40 * 452136 * 2
def baseEnd_452136 : Nat := 103183595200599222009187

theorem tailTrace_452136 : CollatzResearch.WordTrace tailWord_452136 prefixEnd_452136 103183595200599222009187 := by
  unfold tailWord_452136
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245377344997982763108131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10993836459997310350810841 8245377344997982763108131)
  ·
    refine ⟨12368066017496974144662197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8245377344997982763108131 12368066017496974144662197)
    ·
      refine ⟨1159506189140341326062081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12368066017496974144662197 1159506189140341326062081)
      ·
        refine ⟨869629641855255994546561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1159506189140341326062081 869629641855255994546561)
        ·
          refine ⟨652222231391441995909921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 869629641855255994546561 652222231391441995909921)
          ·
            refine ⟨489166673543581496932441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652222231391441995909921 489166673543581496932441)
            ·
              refine ⟨366875005157686122699331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489166673543581496932441 366875005157686122699331)
              ·
                refine ⟨550312507736529184048997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366875005157686122699331 550312507736529184048997)
                ·
                  refine ⟨103183595200599222009187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550312507736529184048997 103183595200599222009187)
                  ·
                    rfl

theorem cell21_452136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_452136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452136 prefixEnd_452136 := by exact prefixLift 452136
  have htrace : WordTrace (prefixWord ++ tailWord_452136) baseStart_452136 baseEnd_452136 := by
    simpa [prefixWord, tailWord_452136, baseEnd_452136] using wordTrace_append hprefix tailTrace_452136
  have hstable : (prefixWord ++ tailWord_452136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452136).length < 2 ^ (prefixWord ++ tailWord_452136).sum := by decide
  have hdescent : baseEnd_452136 < baseStart_452136 := by decide
  rcases family_descends (prefixWord ++ tailWord_452136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452178 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_452178 : Nat := 118140960795 + 452178 * 2 ^ 59
def prefixEnd_452178 : Nat := 4983230072969 + 3 ^ 40 * 452178 * 2
def baseEnd_452178 : Nat := 103193180172816482309101

theorem tailTrace_452178 : CollatzResearch.WordTrace tailWord_452178 prefixEnd_452178 103193180172816482309101 := by
  unfold tailWord_452178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123071638960951674811297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10994857703895871132830125 4123071638960951674811297)
  ·
    refine ⟨3092303729220713756108473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4123071638960951674811297 3092303729220713756108473)
    ·
      refine ⟨2319227796915535317081355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3092303729220713756108473 2319227796915535317081355)
      ·
        refine ⟨3478841695373302975622033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319227796915535317081355 3478841695373302975622033)
        ·
          refine ⟨2609131271529977231716525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478841695373302975622033 2609131271529977231716525)
          ·
            refine ⟨978424226823741461893697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2609131271529977231716525 978424226823741461893697)
            ·
              refine ⟨733818170117806096420273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978424226823741461893697 733818170117806096420273)
              ·
                refine ⟨550363627588354572315205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733818170117806096420273 550363627588354572315205)
                ·
                  refine ⟨103193180172816482309101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550363627588354572315205 103193180172816482309101)
                  ·
                    rfl

theorem cell21_452178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_452178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452178 prefixEnd_452178 := by exact prefixLift 452178
  have htrace : WordTrace (prefixWord ++ tailWord_452178) baseStart_452178 baseEnd_452178 := by
    simpa [prefixWord, tailWord_452178, baseEnd_452178] using wordTrace_append hprefix tailTrace_452178
  have hstable : (prefixWord ++ tailWord_452178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452178).length < 2 ^ (prefixWord ++ tailWord_452178).sum := by decide
  have hdescent : baseEnd_452178 < baseStart_452178 := by decide
  rcases family_descends (prefixWord ++ tailWord_452178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452220 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_452220 : Nat := 118140960795 + 452220 * 2 ^ 59
def prefixEnd_452220 : Nat := 4983230072969 + 3 ^ 40 * 452220 * 2
def baseEnd_452220 : Nat := 103202765145033742609015

theorem tailTrace_452220 : CollatzResearch.WordTrace tailWord_452220 prefixEnd_452220 103202765145033742609015 := by
  unfold tailWord_452220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8246909210845823936137057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10995878947794431914849409 8246909210845823936137057)
  ·
    refine ⟨6185181908134367952102793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8246909210845823936137057 6185181908134367952102793)
    ·
      refine ⟨4638886431100775964077095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6185181908134367952102793 4638886431100775964077095)
      ·
        refine ⟨6958329646651163946115643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4638886431100775964077095 6958329646651163946115643)
        ·
          refine ⟨10437494469976745919173465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6958329646651163946115643 10437494469976745919173465)
          ·
            refine ⟨7828120852482559439380099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10437494469976745919173465 7828120852482559439380099)
            ·
              refine ⟨11742181278723839159070149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7828120852482559439380099 11742181278723839159070149)
              ·
                refine ⟨2201658989760719842325653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11742181278723839159070149 2201658989760719842325653)
                ·
                  refine ⟨103202765145033742609015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2201658989760719842325653 103202765145033742609015)
                  ·
                    rfl

theorem cell21_452220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_452220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452220 prefixEnd_452220 := by exact prefixLift 452220
  have htrace : WordTrace (prefixWord ++ tailWord_452220) baseStart_452220 baseEnd_452220 := by
    simpa [prefixWord, tailWord_452220, baseEnd_452220] using wordTrace_append hprefix tailTrace_452220
  have hstable : (prefixWord ++ tailWord_452220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452220).length < 2 ^ (prefixWord ++ tailWord_452220).sum := by decide
  have hdescent : baseEnd_452220 < baseStart_452220 := by decide
  rcases family_descends (prefixWord ++ tailWord_452220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452296 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_452296 : Nat := 118140960795 + 452296 * 2 ^ 59
def prefixEnd_452296 : Nat := 4983230072969 + 3 ^ 40 * 452296 * 2
def baseEnd_452296 : Nat := 103220109380474499342193

theorem tailTrace_452296 : CollatzResearch.WordTrace tailWord_452296 prefixEnd_452296 103220109380474499342193 := by
  unfold tailWord_452296
  simp only [CollatzResearch.WordTrace]
  refine ⟨8248295184708156426020371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10997726912944208568027161 8248295184708156426020371)
  ·
    refine ⟨12372442777062234639030557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8248295184708156426020371 12372442777062234639030557)
    ·
      refine ⟨4639666041398337989636459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12372442777062234639030557 4639666041398337989636459)
      ·
        refine ⟨6959499062097506984454689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639666041398337989636459 6959499062097506984454689)
        ·
          refine ⟨5219624296573130238341017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6959499062097506984454689 5219624296573130238341017)
          ·
            refine ⟨3914718222429847678755763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5219624296573130238341017 3914718222429847678755763)
            ·
              refine ⟨5872077333644771518133645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914718222429847678755763 5872077333644771518133645)
              ·
                refine ⟨2202029000116789319300117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872077333644771518133645 2202029000116789319300117)
                ·
                  refine ⟨103220109380474499342193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2202029000116789319300117 103220109380474499342193)
                  ·
                    rfl

theorem cell21_452296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_452296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452296 prefixEnd_452296 := by exact prefixLift 452296
  have htrace : WordTrace (prefixWord ++ tailWord_452296) baseStart_452296 baseEnd_452296 := by
    simpa [prefixWord, tailWord_452296, baseEnd_452296] using wordTrace_append hprefix tailTrace_452296
  have hstable : (prefixWord ++ tailWord_452296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452296).length < 2 ^ (prefixWord ++ tailWord_452296).sum := by decide
  have hdescent : baseEnd_452296 < baseStart_452296 := by decide
  rcases family_descends (prefixWord ++ tailWord_452296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452313 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 4]
def baseStart_452313 : Nat := 118140960795 + 452313 * 2 ^ 59
def prefixEnd_452313 : Nat := 4983230072969 + 3 ^ 40 * 452313 * 2
def baseEnd_452313 : Nat := 103223989012086247558825

theorem tailTrace_452313 : CollatzResearch.WordTrace tailWord_452313 prefixEnd_452313 103223989012086247558825 := by
  unfold tailWord_452313
  simp only [CollatzResearch.WordTrace]
  refine ⟨16497210410354724755409593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10998140273569816503606395 16497210410354724755409593)
  ·
    refine ⟨12372907807766043566557195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16497210410354724755409593 12372907807766043566557195)
    ·
      refine ⟨18559361711649065349835793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12372907807766043566557195 18559361711649065349835793)
      ·
        refine ⟨13919521283736799012376845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18559361711649065349835793 13919521283736799012376845)
        ·
          refine ⟨5219820481401299629641317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13919521283736799012376845 5219820481401299629641317)
          ·
            refine ⟨978716340262743680557747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5219820481401299629641317 978716340262743680557747)
            ·
              refine ⟨1468074510394115520836621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978716340262743680557747 1468074510394115520836621)
              ·
                refine ⟨550527941397793320313733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1468074510394115520836621 550527941397793320313733)
                ·
                  refine ⟨103223989012086247558825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550527941397793320313733 103223989012086247558825)
                  ·
                    rfl

theorem cell21_452313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_452313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452313 prefixEnd_452313 := by exact prefixLift 452313
  have htrace : WordTrace (prefixWord ++ tailWord_452313) baseStart_452313 baseEnd_452313 := by
    simpa [prefixWord, tailWord_452313, baseEnd_452313] using wordTrace_append hprefix tailTrace_452313
  have hstable : (prefixWord ++ tailWord_452313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452313).length < 2 ^ (prefixWord ++ tailWord_452313).sum := by decide
  have hdescent : baseEnd_452313 < baseStart_452313 := by decide
  rcases family_descends (prefixWord ++ tailWord_452313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452350 : List Nat := [4, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_452350 : Nat := 118140960795 + 452350 * 2 ^ 59
def prefixEnd_452350 : Nat := 4983230072969 + 3 ^ 40 * 452350 * 2
def baseEnd_452350 : Nat := 103232432916182405442083

theorem tailTrace_452350 : CollatzResearch.WordTrace tailWord_452350 prefixEnd_452350 103232432916182405442083 := by
  unfold tailWord_452350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062319988902585009313313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10999039940813786716337669 2062319988902585009313313)
  ·
    refine ⟨1546739991676938756984985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2062319988902585009313313 1546739991676938756984985)
    ·
      refine ⟨1160054993757704067738739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1546739991676938756984985 1160054993757704067738739)
      ·
        refine ⟨1740082490636556101608109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160054993757704067738739 1740082490636556101608109)
        ·
          refine ⟨652530933988708538103041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1740082490636556101608109 652530933988708538103041)
          ·
            refine ⟨489398200491531403577281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652530933988708538103041 489398200491531403577281)
            ·
              refine ⟨367048650368648552682961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489398200491531403577281 367048650368648552682961)
              ·
                refine ⟨275286487776486414512221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367048650368648552682961 275286487776486414512221)
                ·
                  refine ⟨103232432916182405442083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275286487776486414512221 103232432916182405442083)
                  ·
                    rfl

theorem cell21_452350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_452350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452350 prefixEnd_452350 := by exact prefixLift 452350
  have htrace : WordTrace (prefixWord ++ tailWord_452350) baseStart_452350 baseEnd_452350 := by
    simpa [prefixWord, tailWord_452350, baseEnd_452350] using wordTrace_append hprefix tailTrace_452350
  have hstable : (prefixWord ++ tailWord_452350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452350).length < 2 ^ (prefixWord ++ tailWord_452350).sum := by decide
  have hdescent : baseEnd_452350 < baseStart_452350 := by decide
  rcases family_descends (prefixWord ++ tailWord_452350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452392 : List Nat := [2, 1, 5, 1, 1, 3, 2, 3, 3]
def baseStart_452392 : Nat := 118140960795 + 452392 * 2 ^ 59
def prefixEnd_452392 : Nat := 4983230072969 + 3 ^ 40 * 452392 * 2
def baseEnd_452392 : Nat := 103242017888399665741997

theorem tailTrace_452392 : CollatzResearch.WordTrace tailWord_452392 prefixEnd_452392 103242017888399665741997 := by
  unfold tailWord_452392
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250045888534260623767715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11000061184712347498356953 8250045888534260623767715)
  ·
    refine ⟨12375068832801390935651573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8250045888534260623767715 12375068832801390935651573)
    ·
      refine ⟨1160162703075130400217335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12375068832801390935651573 1160162703075130400217335)
      ·
        refine ⟨1740244054612695600326003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160162703075130400217335 1740244054612695600326003)
        ·
          refine ⟨2610366081919043400489005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740244054612695600326003 2610366081919043400489005)
          ·
            refine ⟨978887280719641275183377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2610366081919043400489005 978887280719641275183377)
            ·
              refine ⟨734165460539730956387533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978887280719641275183377 734165460539730956387533)
              ·
                refine ⟨275312047702399108645325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 734165460539730956387533 275312047702399108645325)
                ·
                  refine ⟨103242017888399665741997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275312047702399108645325 103242017888399665741997)
                  ·
                    rfl

theorem cell21_452392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_452392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452392 prefixEnd_452392 := by exact prefixLift 452392
  have htrace : WordTrace (prefixWord ++ tailWord_452392) baseStart_452392 baseEnd_452392 := by
    simpa [prefixWord, tailWord_452392, baseEnd_452392] using wordTrace_append hprefix tailTrace_452392
  have hstable : (prefixWord ++ tailWord_452392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452392).length < 2 ^ (prefixWord ++ tailWord_452392).sum := by decide
  have hdescent : baseEnd_452392 < baseStart_452392 := by decide
  rcases family_descends (prefixWord ++ tailWord_452392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452403 : List Nat := [1, 1, 1, 2, 7, 1, 8]
def baseStart_452403 : Nat := 118140960795 + 452403 * 2 ^ 59
def prefixEnd_452403 : Nat := 4983230072969 + 3 ^ 40 * 452403 * 2
def baseEnd_452403 : Nat := 11471614248696232339849

theorem tailTrace_452403 : CollatzResearch.WordTrace tailWord_452403 prefixEnd_452403 11471614248696232339849 := by
  unfold tailWord_452403
  simp only [CollatzResearch.WordTrace]
  refine ⟨16500492980028670126185863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11000328653352446750790575 16500492980028670126185863)
  ·
    refine ⟨24750739470043005189278795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16500492980028670126185863 24750739470043005189278795)
    ·
      refine ⟨37126109205064507783918193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24750739470043005189278795 37126109205064507783918193)
      ·
        refine ⟨27844581903798380837938645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37126109205064507783918193 27844581903798380837938645)
        ·
          refine ⟨652607388370274550889187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27844581903798380837938645 652607388370274550889187)
          ·
            refine ⟨978911082555411826333781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652607388370274550889187 978911082555411826333781)
            ·
              refine ⟨11471614248696232339849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 978911082555411826333781 11471614248696232339849)
              ·
                rfl

theorem cell21_452403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 8].length) (baseStart_452403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452403 prefixEnd_452403 := by exact prefixLift 452403
  have htrace : WordTrace (prefixWord ++ tailWord_452403) baseStart_452403 baseEnd_452403 := by
    simpa [prefixWord, tailWord_452403, baseEnd_452403] using wordTrace_append hprefix tailTrace_452403
  have hstable : (prefixWord ++ tailWord_452403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452403).length < 2 ^ (prefixWord ++ tailWord_452403).sum := by decide
  have hdescent : baseEnd_452403 < baseStart_452403 := by decide
  rcases family_descends (prefixWord ++ tailWord_452403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452406 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_452406 : Nat := 118140960795 + 452406 * 2 ^ 59
def prefixEnd_452406 : Nat := 4983230072969 + 3 ^ 40 * 452406 * 2
def baseEnd_452406 : Nat := 103245212879138752508635

theorem tailTrace_452406 : CollatzResearch.WordTrace tailWord_452406 prefixEnd_452406 103245212879138752508635 := by
  unfold tailWord_452406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1031287649938612602409067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11000401599345201092363381 1031287649938612602409067)
  ·
    refine ⟨1546931474907918903613601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1031287649938612602409067 1546931474907918903613601)
    ·
      refine ⟨1160198606180939177710201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1546931474907918903613601 1160198606180939177710201)
      ·
        refine ⟨870148954635704383282651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1160198606180939177710201 870148954635704383282651)
        ·
          refine ⟨1305223431953556574923977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870148954635704383282651 1305223431953556574923977)
          ·
            refine ⟨978917573965167431192983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1305223431953556574923977 978917573965167431192983)
            ·
              refine ⟨1468376360947751146789475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978917573965167431192983 1468376360947751146789475)
              ·
                refine ⟨2202564541421626720184213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468376360947751146789475 2202564541421626720184213)
                ·
                  refine ⟨103245212879138752508635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2202564541421626720184213 103245212879138752508635)
                  ·
                    rfl

theorem cell21_452406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_452406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452406 prefixEnd_452406 := by exact prefixLift 452406
  have htrace : WordTrace (prefixWord ++ tailWord_452406) baseStart_452406 baseEnd_452406 := by
    simpa [prefixWord, tailWord_452406, baseEnd_452406] using wordTrace_append hprefix tailTrace_452406
  have hstable : (prefixWord ++ tailWord_452406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452406).length < 2 ^ (prefixWord ++ tailWord_452406).sum := by decide
  have hdescent : baseEnd_452406 < baseStart_452406 := by decide
  rcases family_descends (prefixWord ++ tailWord_452406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452434 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_452434 : Nat := 118140960795 + 452434 * 2 ^ 59
def prefixEnd_452434 : Nat := 4983230072969 + 3 ^ 40 * 452434 * 2
def baseEnd_452434 : Nat := 103251602860616926041911

theorem tailTrace_452434 : CollatzResearch.WordTrace tailWord_452434 prefixEnd_452434 103251602860616926041911 := by
  unfold tailWord_452434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125405910729090605141089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11001082428610908280376237 4125405910729090605141089)
  ·
    refine ⟨3094054433046817953855817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4125405910729090605141089 3094054433046817953855817)
    ·
      refine ⟨2320540824785113465391863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3094054433046817953855817 2320540824785113465391863)
      ·
        refine ⟨3480811237177670198087795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320540824785113465391863 3480811237177670198087795)
        ·
          refine ⟨5221216855766505297131693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480811237177670198087795 5221216855766505297131693)
          ·
            refine ⟨1957956320912439486424385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5221216855766505297131693 1957956320912439486424385)
            ·
              refine ⟨1468467240684329614818289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957956320912439486424385 1468467240684329614818289)
              ·
                refine ⟨1101350430513247211113717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468467240684329614818289 1101350430513247211113717)
                ·
                  refine ⟨103251602860616926041911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1101350430513247211113717 103251602860616926041911)
                  ·
                    rfl

theorem cell21_452434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_452434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452434 prefixEnd_452434 := by exact prefixLift 452434
  have htrace : WordTrace (prefixWord ++ tailWord_452434) baseStart_452434 baseEnd_452434 := by
    simpa [prefixWord, tailWord_452434, baseEnd_452434] using wordTrace_append hprefix tailTrace_452434
  have hstable : (prefixWord ++ tailWord_452434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452434).length < 2 ^ (prefixWord ++ tailWord_452434).sum := by decide
  have hdescent : baseEnd_452434 < baseStart_452434 := by decide
  rcases family_descends (prefixWord ++ tailWord_452434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452448 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_452448 : Nat := 118140960795 + 452448 * 2 ^ 59
def prefixEnd_452448 : Nat := 4983230072969 + 3 ^ 40 * 452448 * 2
def baseEnd_452448 : Nat := 103254797851356012808549

theorem tailTrace_452448 : CollatzResearch.WordTrace tailWord_452448 prefixEnd_452448 103254797851356012808549 := by
  unfold tailWord_452448
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251067132432821405786999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11001422843243761874382665 8251067132432821405786999)
  ·
    refine ⟨12376600698649232108680499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8251067132432821405786999 12376600698649232108680499)
    ·
      refine ⟨18564901047973848163020749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12376600698649232108680499 18564901047973848163020749)
      ·
        refine ⟨6961837892990193061132781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18564901047973848163020749 6961837892990193061132781)
        ·
          refine ⟨2610689209871322397924793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6961837892990193061132781 2610689209871322397924793)
          ·
            refine ⟨1958016907403491798443595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2610689209871322397924793 1958016907403491798443595)
            ·
              refine ⟨2937025361105237697665393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958016907403491798443595 2937025361105237697665393)
              ·
                refine ⟨2202769020828928273249045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937025361105237697665393 2202769020828928273249045)
                ·
                  refine ⟨103254797851356012808549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2202769020828928273249045 103254797851356012808549)
                  ·
                    rfl

theorem cell21_452448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_452448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452448 prefixEnd_452448 := by exact prefixLift 452448
  have htrace : WordTrace (prefixWord ++ tailWord_452448) baseStart_452448 baseEnd_452448 := by
    simpa [prefixWord, tailWord_452448, baseEnd_452448] using wordTrace_append hprefix tailTrace_452448
  have hstable : (prefixWord ++ tailWord_452448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452448).length < 2 ^ (prefixWord ++ tailWord_452448).sum := by decide
  have hdescent : baseEnd_452448 < baseStart_452448 := by decide
  rcases family_descends (prefixWord ++ tailWord_452448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452538 : List Nat := [3, 1, 1, 1, 2, 1, 2, 10]
def baseStart_452538 : Nat := 118140960795 + 452538 * 2 ^ 59
def prefixEnd_452538 : Nat := 4983230072969 + 3 ^ 40 * 452538 * 2
def baseEnd_452538 : Nat := 34425112359178618769455

theorem tailTrace_452538 : CollatzResearch.WordTrace tailWord_452538 prefixEnd_452538 34425112359178618769455 := by
  unfold tailWord_452538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126354208634897045587567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11003611223026392121566845 4126354208634897045587567)
  ·
    refine ⟨6189531312952345568381351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4126354208634897045587567 6189531312952345568381351)
    ·
      refine ⟨9284296969428518352572027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6189531312952345568381351 9284296969428518352572027)
      ·
        refine ⟨13926445454142777528858041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9284296969428518352572027 13926445454142777528858041)
        ·
          refine ⟨10444834090607083146643531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13926445454142777528858041 10444834090607083146643531)
          ·
            refine ⟨15667251135910624719965297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444834090607083146643531 15667251135910624719965297)
            ·
              refine ⟨11750438351932968539973973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15667251135910624719965297 11750438351932968539973973)
              ·
                refine ⟨34425112359178618769455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11750438351932968539973973 34425112359178618769455)
                ·
                  rfl

theorem cell21_452538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_452538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452538 prefixEnd_452538 := by exact prefixLift 452538
  have htrace : WordTrace (prefixWord ++ tailWord_452538) baseStart_452538 baseEnd_452538 := by
    simpa [prefixWord, tailWord_452538, baseEnd_452538] using wordTrace_append hprefix tailTrace_452538
  have hstable : (prefixWord ++ tailWord_452538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452538).length < 2 ^ (prefixWord ++ tailWord_452538).sum := by decide
  have hdescent : baseEnd_452538 < baseStart_452538 := by decide
  rcases family_descends (prefixWord ++ tailWord_452538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452541 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 4]
def baseStart_452541 : Nat := 118140960795 + 452541 * 2 ^ 59
def prefixEnd_452541 : Nat := 4983230072969 + 3 ^ 40 * 452541 * 2
def baseEnd_452541 : Nat := 103276021718408517758359

theorem tailTrace_452541 : CollatzResearch.WordTrace tailWord_452541 prefixEnd_452541 103276021718408517758359 := by
  unfold tailWord_452541
  simp only [CollatzResearch.WordTrace]
  refine ⟨16505526253528719694709477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11003684169019146463139651 16505526253528719694709477)
  ·
    refine ⟨3094786172536634942758027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16505526253528719694709477 3094786172536634942758027)
    ·
      refine ⟨4642179258804952414137041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094786172536634942758027 4642179258804952414137041)
      ·
        refine ⟨3481634444103714310602781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4642179258804952414137041 3481634444103714310602781)
        ·
          refine ⟨1305612916538892866476043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3481634444103714310602781 1305612916538892866476043)
          ·
            refine ⟨1958419374808339299714065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305612916538892866476043 1958419374808339299714065)
            ·
              refine ⟨1468814531106254474785549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958419374808339299714065 1468814531106254474785549)
              ·
                refine ⟨550805449164845428044581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1468814531106254474785549 550805449164845428044581)
                ·
                  refine ⟨103276021718408517758359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550805449164845428044581 103276021718408517758359)
                  ·
                    rfl

theorem cell21_452541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_452541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452541 prefixEnd_452541 := by exact prefixLift 452541
  have htrace : WordTrace (prefixWord ++ tailWord_452541) baseStart_452541 baseEnd_452541 := by
    simpa [prefixWord, tailWord_452541, baseEnd_452541] using wordTrace_append hprefix tailTrace_452541
  have hstable : (prefixWord ++ tailWord_452541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452541).length < 2 ^ (prefixWord ++ tailWord_452541).sum := by decide
  have hdescent : baseEnd_452541 < baseStart_452541 := by decide
  rcases family_descends (prefixWord ++ tailWord_452541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452555 : List Nat := [1, 1, 1, 1, 3, 4, 5, 5]
def baseStart_452555 : Nat := 118140960795 + 452555 * 2 ^ 59
def prefixEnd_452555 : Nat := 4983230072969 + 3 ^ 40 * 452555 * 2
def baseEnd_452555 : Nat := 34426405569715868174999

theorem tailTrace_452555 : CollatzResearch.WordTrace tailWord_452555 prefixEnd_452555 34426405569715868174999 := by
  unfold tailWord_452555
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506036875478000085719119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11004024583652000057146079 16506036875478000085719119)
  ·
    refine ⟨24759055313217000128578679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16506036875478000085719119 24759055313217000128578679)
    ·
      refine ⟨37138582969825500192868019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24759055313217000128578679 37138582969825500192868019)
      ·
        refine ⟨55707874454738250289302029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37138582969825500192868019 55707874454738250289302029)
        ·
          refine ⟨20890452920526843858488261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55707874454738250289302029 20890452920526843858488261)
          ·
            refine ⟨3916959922598783223466549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20890452920526843858488261 3916959922598783223466549)
            ·
              refine ⟨367214992743635927199989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3916959922598783223466549 367214992743635927199989)
              ·
                refine ⟨34426405569715868174999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367214992743635927199989 34426405569715868174999)
                ·
                  rfl

theorem cell21_452555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 5].length) (baseStart_452555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452555 prefixEnd_452555 := by exact prefixLift 452555
  have htrace : WordTrace (prefixWord ++ tailWord_452555) baseStart_452555 baseEnd_452555 := by
    simpa [prefixWord, tailWord_452555, baseEnd_452555] using wordTrace_append hprefix tailTrace_452555
  have hstable : (prefixWord ++ tailWord_452555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452555).length < 2 ^ (prefixWord ++ tailWord_452555).sum := by decide
  have hdescent : baseEnd_452555 < baseStart_452555 := by decide
  rcases family_descends (prefixWord ++ tailWord_452555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452586 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_452586 : Nat := 118140960795 + 452586 * 2 ^ 59
def prefixEnd_452586 : Nat := 4983230072969 + 3 ^ 40 * 452586 * 2
def baseEnd_452586 : Nat := 103286291331498439508267

theorem tailTrace_452586 : CollatzResearch.WordTrace tailWord_452586 prefixEnd_452586 103286291331498439508267 := by
  unfold tailWord_452586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126791884591423095024403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11004778358910461586731741 4126791884591423095024403)
  ·
    refine ⟨6190187826887134642536605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4126791884591423095024403 6190187826887134642536605)
    ·
      refine ⟨2321320435082675490951227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6190187826887134642536605 2321320435082675490951227)
      ·
        refine ⟨3481980652624013236426841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2321320435082675490951227 3481980652624013236426841)
        ·
          refine ⟨2611485489468009927320131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3481980652624013236426841 2611485489468009927320131)
          ·
            refine ⟨3917228234202014890980197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611485489468009927320131 3917228234202014890980197)
            ·
              refine ⟨734480293912877792058787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3917228234202014890980197 734480293912877792058787)
              ·
                refine ⟨1101720440869316688088181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734480293912877792058787 1101720440869316688088181)
                ·
                  refine ⟨103286291331498439508267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1101720440869316688088181 103286291331498439508267)
                  ·
                    rfl

theorem cell21_452586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_452586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452586 prefixEnd_452586 := by exact prefixLift 452586
  have htrace : WordTrace (prefixWord ++ tailWord_452586) baseStart_452586 baseEnd_452586 := by
    simpa [prefixWord, tailWord_452586, baseEnd_452586] using wordTrace_append hprefix tailTrace_452586
  have hstable : (prefixWord ++ tailWord_452586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452586).length < 2 ^ (prefixWord ++ tailWord_452586).sum := by decide
  have hdescent : baseEnd_452586 < baseStart_452586 := by decide
  rcases family_descends (prefixWord ++ tailWord_452586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452600 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_452600 : Nat := 118140960795 + 452600 * 2 ^ 59
def prefixEnd_452600 : Nat := 4983230072969 + 3 ^ 40 * 452600 * 2
def baseEnd_452600 : Nat := 103289486322237526274905

theorem tailTrace_452600 : CollatzResearch.WordTrace tailWord_452600 prefixEnd_452600 103289486322237526274905 := by
  unfold tailWord_452600
  simp only [CollatzResearch.WordTrace]
  refine ⟨8253839080157486385553627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11005118773543315180738169 8253839080157486385553627)
  ·
    refine ⟨12380758620236229578330441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8253839080157486385553627 12380758620236229578330441)
    ·
      refine ⟨9285568965177172183747831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12380758620236229578330441 9285568965177172183747831)
      ·
        refine ⟨13928353447765758275621747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9285568965177172183747831 13928353447765758275621747)
        ·
          refine ⟨20892530171648637413432621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13928353447765758275621747 20892530171648637413432621)
          ·
            refine ⟨7834698814368239030037233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20892530171648637413432621 7834698814368239030037233)
            ·
              refine ⟨5876024110776179272527925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7834698814368239030037233 5876024110776179272527925)
              ·
                refine ⟨550877260385266806799493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5876024110776179272527925 550877260385266806799493)
                ·
                  refine ⟨103289486322237526274905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550877260385266806799493 103289486322237526274905)
                  ·
                    rfl

theorem cell21_452600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_452600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452600 prefixEnd_452600 := by exact prefixLift 452600
  have htrace : WordTrace (prefixWord ++ tailWord_452600) baseStart_452600 baseEnd_452600 := by
    simpa [prefixWord, tailWord_452600, baseEnd_452600] using wordTrace_append hprefix tailTrace_452600
  have hstable : (prefixWord ++ tailWord_452600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452600).length < 2 ^ (prefixWord ++ tailWord_452600).sum := by decide
  have hdescent : baseEnd_452600 < baseStart_452600 := by decide
  rcases family_descends (prefixWord ++ tailWord_452600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452662 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_452662 : Nat := 118140960795 + 452662 * 2 ^ 59
def prefixEnd_452662 : Nat := 4983230072969 + 3 ^ 40 * 452662 * 2
def baseEnd_452662 : Nat := 103303635566939196241445

theorem tailTrace_452662 : CollatzResearch.WordTrace tailWord_452662 prefixEnd_452662 103303635566939196241445 := by
  unfold tailWord_452662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1031871217880647334991515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11006626324060238239909493 1031871217880647334991515)
  ·
    refine ⟨1547806826820971002487273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1031871217880647334991515 1547806826820971002487273)
    ·
      refine ⟨1160855120115728251865455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1547806826820971002487273 1160855120115728251865455)
      ·
        refine ⟨1741282680173592377798183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160855120115728251865455 1741282680173592377798183)
        ·
          refine ⟨2611924020260388566697275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741282680173592377798183 2611924020260388566697275)
          ·
            refine ⟨3917886030390582850045913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611924020260388566697275 3917886030390582850045913)
            ·
              refine ⟨2938414522792937137534435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917886030390582850045913 2938414522792937137534435)
              ·
                refine ⟨4407621784189405706301653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938414522792937137534435 4407621784189405706301653)
                ·
                  refine ⟨103303635566939196241445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4407621784189405706301653 103303635566939196241445)
                  ·
                    rfl

theorem cell21_452662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_452662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452662 prefixEnd_452662 := by exact prefixLift 452662
  have htrace : WordTrace (prefixWord ++ tailWord_452662) baseStart_452662 baseEnd_452662 := by
    simpa [prefixWord, tailWord_452662, baseEnd_452662] using wordTrace_append hprefix tailTrace_452662
  have hstable : (prefixWord ++ tailWord_452662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452662).length < 2 ^ (prefixWord ++ tailWord_452662).sum := by decide
  have hdescent : baseEnd_452662 < baseStart_452662 := by decide
  rcases family_descends (prefixWord ++ tailWord_452662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452690 : List Nat := [3, 2, 2, 1, 13]
def baseStart_452690 : Nat := 118140960795 + 452690 * 2 ^ 59
def prefixEnd_452690 : Nat := 4983230072969 + 3 ^ 40 * 452690 * 2
def baseEnd_452690 : Nat := 1275432414177992219441

theorem tailTrace_452690 : CollatzResearch.WordTrace tailWord_452690 prefixEnd_452690 1275432414177992219441 := by
  unfold tailWord_452690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4127740182497229535470881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11007307153325945427922349 4127740182497229535470881)
  ·
    refine ⟨3095805136872922151603161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4127740182497229535470881 3095805136872922151603161)
    ·
      refine ⟨2321853852654691613702371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3095805136872922151603161 2321853852654691613702371)
      ·
        refine ⟨3482780778982037420553557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2321853852654691613702371 3482780778982037420553557)
        ·
          refine ⟨1275432414177992219441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3482780778982037420553557 1275432414177992219441)
          ·
            rfl

theorem cell21_452690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 13].length) (baseStart_452690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452690 prefixEnd_452690 := by exact prefixLift 452690
  have htrace : WordTrace (prefixWord ++ tailWord_452690) baseStart_452690 baseEnd_452690 := by
    simpa [prefixWord, tailWord_452690, baseEnd_452690] using wordTrace_append hprefix tailTrace_452690
  have hstable : (prefixWord ++ tailWord_452690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452690).length < 2 ^ (prefixWord ++ tailWord_452690).sum := by decide
  have hdescent : baseEnd_452690 < baseStart_452690 := by decide
  rcases family_descends (prefixWord ++ tailWord_452690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452693 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 4]
def baseStart_452693 : Nat := 118140960795 + 452693 * 2 ^ 59
def prefixEnd_452693 : Nat := 4983230072969 + 3 ^ 40 * 452693 * 2
def baseEnd_452693 : Nat := 103310710189290031224715

theorem tailTrace_452693 : CollatzResearch.WordTrace tailWord_452693 prefixEnd_452693 103310710189290031224715 := by
  unfold tailWord_452693
  simp only [CollatzResearch.WordTrace]
  refine ⟨16511070148978049654242733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11007380099318699769495155 16511070148978049654242733)
  ·
    refine ⟨6191651305866768620341025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16511070148978049654242733 6191651305866768620341025)
    ·
      refine ⟨4643738479400076465255769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6191651305866768620341025 4643738479400076465255769)
      ·
        refine ⟨3482803859550057348941827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4643738479400076465255769 3482803859550057348941827)
        ·
          refine ⟨5224205789325086023412741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482803859550057348941827 5224205789325086023412741)
          ·
            refine ⟨979538585498453629389889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5224205789325086023412741 979538585498453629389889)
            ·
              refine ⟨734653939123840222042417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979538585498453629389889 734653939123840222042417)
              ·
                refine ⟨550990454342880166531813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734653939123840222042417 550990454342880166531813)
                ·
                  refine ⟨103310710189290031224715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550990454342880166531813 103310710189290031224715)
                  ·
                    rfl

theorem cell21_452693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_452693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452693 prefixEnd_452693 := by exact prefixLift 452693
  have htrace : WordTrace (prefixWord ++ tailWord_452693) baseStart_452693 baseEnd_452693 := by
    simpa [prefixWord, tailWord_452693, baseEnd_452693] using wordTrace_append hprefix tailTrace_452693
  have hstable : (prefixWord ++ tailWord_452693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452693).length < 2 ^ (prefixWord ++ tailWord_452693).sum := by decide
  have hdescent : baseEnd_452693 < baseStart_452693 := by decide
  rcases family_descends (prefixWord ++ tailWord_452693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452696 : List Nat := [2, 1, 2, 2, 1, 6, 2, 2, 3]
def baseStart_452696 : Nat := 118140960795 + 452696 * 2 ^ 59
def prefixEnd_452696 : Nat := 4983230072969 + 3 ^ 40 * 452696 * 2
def baseEnd_452696 : Nat := 103311394830162692674709

theorem tailTrace_452696 : CollatzResearch.WordTrace tailWord_452696 prefixEnd_452696 103311394830162692674709 := by
  unfold tailWord_452696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8255589783983590583300971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11007453045311454111067961 8255589783983590583300971)
  ·
    refine ⟨12383384675975385874951457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8255589783983590583300971 12383384675975385874951457)
    ·
      refine ⟨9287538506981539406213593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12383384675975385874951457 9287538506981539406213593)
      ·
        refine ⟨6965653880236154554660195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9287538506981539406213593 6965653880236154554660195)
        ·
          refine ⟨10448480820354231831990293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6965653880236154554660195 10448480820354231831990293)
          ·
            refine ⟨489772538454104617124545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10448480820354231831990293 489772538454104617124545)
            ·
              refine ⟨367329403840578462843409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489772538454104617124545 367329403840578462843409)
              ·
                refine ⟨275497052880433847132557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367329403840578462843409 275497052880433847132557)
                ·
                  refine ⟨103311394830162692674709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275497052880433847132557 103311394830162692674709)
                  ·
                    rfl

theorem cell21_452696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_452696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452696 prefixEnd_452696 := by exact prefixLift 452696
  have htrace : WordTrace (prefixWord ++ tailWord_452696) baseStart_452696 baseEnd_452696 := by
    simpa [prefixWord, tailWord_452696, baseEnd_452696] using wordTrace_append hprefix tailTrace_452696
  have hstable : (prefixWord ++ tailWord_452696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452696).length < 2 ^ (prefixWord ++ tailWord_452696).sum := by decide
  have hdescent : baseEnd_452696 < baseStart_452696 := by decide
  rcases family_descends (prefixWord ++ tailWord_452696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452721 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 5]
def baseStart_452721 : Nat := 118140960795 + 452721 * 2 ^ 59
def prefixEnd_452721 : Nat := 4983230072969 + 3 ^ 40 * 452721 * 2
def baseEnd_452721 : Nat := 103317100170768204757991

theorem tailTrace_452721 : CollatzResearch.WordTrace tailWord_452721 prefixEnd_452721 103317100170768204757991 := by
  unfold tailWord_452721
  simp only [CollatzResearch.WordTrace]
  refine ⟨16512091392876610436262017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11008060928584406957508011 16512091392876610436262017)
  ·
    refine ⟨12384068544657457827196513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16512091392876610436262017 12384068544657457827196513)
    ·
      refine ⟨9288051408493093370397385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12384068544657457827196513 9288051408493093370397385)
      ·
        refine ⟨6966038556369820027798039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9288051408493093370397385 6966038556369820027798039)
        ·
          refine ⟨10449057834554730041697059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6966038556369820027798039 10449057834554730041697059)
          ·
            refine ⟨15673586751832095062545589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10449057834554730041697059 15673586751832095062545589)
            ·
              refine ⟨1469398757984258912113649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15673586751832095062545589 1469398757984258912113649)
              ·
                refine ⟨1102049068488194184085237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469398757984258912113649 1102049068488194184085237)
                ·
                  refine ⟨103317100170768204757991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1102049068488194184085237 103317100170768204757991)
                  ·
                    rfl

theorem cell21_452721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_452721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452721 prefixEnd_452721 := by exact prefixLift 452721
  have htrace : WordTrace (prefixWord ++ tailWord_452721) baseStart_452721 baseEnd_452721 := by
    simpa [prefixWord, tailWord_452721, baseEnd_452721] using wordTrace_append hprefix tailTrace_452721
  have hstable : (prefixWord ++ tailWord_452721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452721).length < 2 ^ (prefixWord ++ tailWord_452721).sum := by decide
  have hdescent : baseEnd_452721 < baseStart_452721 := by decide
  rcases family_descends (prefixWord ++ tailWord_452721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452789 : List Nat := [1, 3, 3, 4, 1, 2, 1, 3, 3]
def baseStart_452789 : Nat := 118140960795 + 452789 * 2 ^ 59
def prefixEnd_452789 : Nat := 4983230072969 + 3 ^ 40 * 452789 * 2
def baseEnd_452789 : Nat := 103332618697215197624519

theorem tailTrace_452789 : CollatzResearch.WordTrace tailWord_452789 prefixEnd_452789 103332618697215197624519 := by
  unfold tailWord_452789
  simp only [CollatzResearch.WordTrace]
  refine ⟨16514571556630258049737421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11009714371086838699824947 16514571556630258049737421)
  ·
    refine ⟨6192964333736346768651533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16514571556630258049737421 6192964333736346768651533)
    ·
      refine ⟨2322361625151130038244325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6192964333736346768651533 2322361625151130038244325)
      ·
        refine ⟨435442804715836882170811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2322361625151130038244325 435442804715836882170811)
        ·
          refine ⟨653164207073755323256217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435442804715836882170811 653164207073755323256217)
          ·
            refine ⟨489873155305316492442163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653164207073755323256217 489873155305316492442163)
            ·
              refine ⟨734809732957974738663245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489873155305316492442163 734809732957974738663245)
              ·
                refine ⟨275553649859240526998717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 734809732957974738663245 275553649859240526998717)
                ·
                  refine ⟨103332618697215197624519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275553649859240526998717 103332618697215197624519)
                  ·
                    rfl

theorem cell21_452789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_452789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452789 prefixEnd_452789 := by exact prefixLift 452789
  have htrace : WordTrace (prefixWord ++ tailWord_452789) baseStart_452789 baseEnd_452789 := by
    simpa [prefixWord, tailWord_452789, baseEnd_452789] using wordTrace_append hprefix tailTrace_452789
  have hstable : (prefixWord ++ tailWord_452789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452789).length < 2 ^ (prefixWord ++ tailWord_452789).sum := by decide
  have hdescent : baseEnd_452789 < baseStart_452789 := by decide
  rcases family_descends (prefixWord ++ tailWord_452789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452811 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 6]
def baseStart_452811 : Nat := 118140960795 + 452811 * 2 ^ 59
def prefixEnd_452811 : Nat := 4983230072969 + 3 ^ 40 * 452811 * 2
def baseEnd_452811 : Nat := 103337639396948048257807

theorem tailTrace_452811 : CollatzResearch.WordTrace tailWord_452811 prefixEnd_452811 103337639396948048257807 := by
  unfold tailWord_452811
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515373962550555807038287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11010249308367037204692191 16515373962550555807038287)
  ·
    refine ⟨24773060943825833710557431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16515373962550555807038287 24773060943825833710557431)
    ·
      refine ⟨37159591415738750565836147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24773060943825833710557431 37159591415738750565836147)
      ·
        refine ⟨55739387123608125848754221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37159591415738750565836147 55739387123608125848754221)
        ·
          refine ⟨20902270171353047193282833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55739387123608125848754221 20902270171353047193282833)
          ·
            refine ⟨15676702628514785394962125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20902270171353047193282833 15676702628514785394962125)
            ·
              refine ⟨5878763485693044523110797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15676702628514785394962125 5878763485693044523110797)
              ·
                refine ⟨2204536307134891696166549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5878763485693044523110797 2204536307134891696166549)
                ·
                  refine ⟨103337639396948048257807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2204536307134891696166549 103337639396948048257807)
                  ·
                    rfl

theorem cell21_452811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_452811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452811 prefixEnd_452811 := by exact prefixLift 452811
  have htrace : WordTrace (prefixWord ++ tailWord_452811) baseStart_452811 baseEnd_452811 := by
    simpa [prefixWord, tailWord_452811, baseEnd_452811] using wordTrace_append hprefix tailTrace_452811
  have hstable : (prefixWord ++ tailWord_452811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452811).length < 2 ^ (prefixWord ++ tailWord_452811).sum := by decide
  have hdescent : baseEnd_452811 < baseStart_452811 := by decide
  rcases family_descends (prefixWord ++ tailWord_452811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452814 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_452814 : Nat := 118140960795 + 452814 * 2 ^ 59
def prefixEnd_452814 : Nat := 4983230072969 + 3 ^ 40 * 452814 * 2
def baseEnd_452814 : Nat := 103338324037820709707801

theorem tailTrace_452814 : CollatzResearch.WordTrace tailWord_452814 prefixEnd_452814 103338324037820709707801 := by
  unfold tailWord_452814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064435422692460914924687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11010322254359791546264997 2064435422692460914924687)
  ·
    refine ⟨3096653134038691372387031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2064435422692460914924687 3096653134038691372387031)
    ·
      refine ⟨4644979701058037058580547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3096653134038691372387031 4644979701058037058580547)
      ·
        refine ⟨6967469551587055587870821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4644979701058037058580547 6967469551587055587870821)
        ·
          refine ⟨1306400540922572922725779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6967469551587055587870821 1306400540922572922725779)
          ·
            refine ⟨1959600811383859384088669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306400540922572922725779 1959600811383859384088669)
            ·
              refine ⟨734850304268947269033251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1959600811383859384088669 734850304268947269033251)
              ·
                refine ⟨1102275456403420903549877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734850304268947269033251 1102275456403420903549877)
                ·
                  refine ⟨103338324037820709707801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1102275456403420903549877 103338324037820709707801)
                  ·
                    rfl

theorem cell21_452814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_452814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452814 prefixEnd_452814 := by exact prefixLift 452814
  have htrace : WordTrace (prefixWord ++ tailWord_452814) baseStart_452814 baseEnd_452814 := by
    simpa [prefixWord, tailWord_452814, baseEnd_452814] using wordTrace_append hprefix tailTrace_452814
  have hstable : (prefixWord ++ tailWord_452814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452814).length < 2 ^ (prefixWord ++ tailWord_452814).sum := by decide
  have hdescent : baseEnd_452814 < baseStart_452814 := by decide
  rcases family_descends (prefixWord ++ tailWord_452814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452842 : List Nat := [3, 1, 3, 1, 1, 2, 1, 9]
def baseStart_452842 : Nat := 118140960795 + 452842 * 2 ^ 59
def prefixEnd_452842 : Nat := 4983230072969 + 3 ^ 40 * 452842 * 2
def baseEnd_452842 : Nat := 34448238006432961080359

theorem tailTrace_452842 : CollatzResearch.WordTrace tailWord_452842 prefixEnd_452842 34448238006432961080359 := by
  unfold tailWord_452842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4129126156359562025354195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11011003083625498734277853 4129126156359562025354195)
  ·
    refine ⟨6193689234539343038031293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4129126156359562025354195 6193689234539343038031293)
    ·
      refine ⟨2322633462952253639261735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6193689234539343038031293 2322633462952253639261735)
      ·
        refine ⟨3483950194428380458892603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322633462952253639261735 3483950194428380458892603)
        ·
          refine ⟨5225925291642570688338905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483950194428380458892603 5225925291642570688338905)
          ·
            refine ⟨3919443968731928016254179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5225925291642570688338905 3919443968731928016254179)
            ·
              refine ⟨5879165953097892024381269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3919443968731928016254179 5879165953097892024381269)
              ·
                refine ⟨34448238006432961080359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5879165953097892024381269 34448238006432961080359)
                ·
                  rfl

theorem cell21_452842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_452842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452842 prefixEnd_452842 := by exact prefixLift 452842
  have htrace : WordTrace (prefixWord ++ tailWord_452842) baseStart_452842 baseEnd_452842 := by
    simpa [prefixWord, tailWord_452842, baseEnd_452842] using wordTrace_append hprefix tailTrace_452842
  have hstable : (prefixWord ++ tailWord_452842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452842).length < 2 ^ (prefixWord ++ tailWord_452842).sum := by decide
  have hdescent : baseEnd_452842 < baseStart_452842 := by decide
  rcases family_descends (prefixWord ++ tailWord_452842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452890 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_452890 : Nat := 118140960795 + 452890 * 2 ^ 59
def prefixEnd_452890 : Nat := 4983230072969 + 3 ^ 40 * 452890 * 2
def baseEnd_452890 : Nat := 103355668273261466440979

theorem tailTrace_452890 : CollatzResearch.WordTrace tailWord_452890 prefixEnd_452890 103355668273261466440979 := by
  unfold tailWord_452890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4129563832316088074791031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11012170219509568199442749 4129563832316088074791031)
  ·
    refine ⟨6194345748474132112186547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4129563832316088074791031 6194345748474132112186547)
    ·
      refine ⟨9291518622711198168279821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194345748474132112186547 9291518622711198168279821)
      ·
        refine ⟨3484319483516699313104933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9291518622711198168279821 3484319483516699313104933)
        ·
          refine ⟨653309903159381121207175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3484319483516699313104933 653309903159381121207175)
          ·
            refine ⟨979964854739071681810763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653309903159381121207175 979964854739071681810763)
            ·
              refine ⟨1469947282108607522716145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979964854739071681810763 1469947282108607522716145)
              ·
                refine ⟨1102460461581455642037109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469947282108607522716145 1102460461581455642037109)
                ·
                  refine ⟨103355668273261466440979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1102460461581455642037109 103355668273261466440979)
                  ·
                    rfl

theorem cell21_452890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_452890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452890 prefixEnd_452890 := by exact prefixLift 452890
  have htrace : WordTrace (prefixWord ++ tailWord_452890) baseStart_452890 baseEnd_452890 := by
    simpa [prefixWord, tailWord_452890, baseEnd_452890] using wordTrace_append hprefix tailTrace_452890
  have hstable : (prefixWord ++ tailWord_452890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452890).length < 2 ^ (prefixWord ++ tailWord_452890).sum := by decide
  have hdescent : baseEnd_452890 < baseStart_452890 := by decide
  rcases family_descends (prefixWord ++ tailWord_452890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452921 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 4]
def baseStart_452921 : Nat := 118140960795 + 452921 * 2 ^ 59
def prefixEnd_452921 : Nat := 4983230072969 + 3 ^ 40 * 452921 * 2
def baseEnd_452921 : Nat := 103362742895612301424249

theorem tailTrace_452921 : CollatzResearch.WordTrace tailWord_452921 prefixEnd_452921 103362742895612301424249 := by
  unfold tailWord_452921
  simp only [CollatzResearch.WordTrace]
  refine ⟨16519385992152044593542617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11012923994768029729028411 16519385992152044593542617)
  ·
    refine ⟨12389539494114033445156963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16519385992152044593542617 12389539494114033445156963)
    ·
      refine ⟨18584309241171050167735445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12389539494114033445156963 18584309241171050167735445)
      ·
        refine ⟨871139495679892976612599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18584309241171050167735445 871139495679892976612599)
        ·
          refine ⟨1306709243519839464918899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871139495679892976612599 1306709243519839464918899)
          ·
            refine ⟨1960063865279759197378349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306709243519839464918899 1960063865279759197378349)
            ·
              refine ⟨735023949479909699016881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1960063865279759197378349 735023949479909699016881)
              ·
                refine ⟨551267962109932274262661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735023949479909699016881 551267962109932274262661)
                ·
                  refine ⟨103362742895612301424249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 551267962109932274262661 103362742895612301424249)
                  ·
                    rfl

theorem cell21_452921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_452921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452921 prefixEnd_452921 := by exact prefixLift 452921
  have htrace : WordTrace (prefixWord ++ tailWord_452921) baseStart_452921 baseEnd_452921 := by
    simpa [prefixWord, tailWord_452921, baseEnd_452921] using wordTrace_append hprefix tailTrace_452921
  have hstable : (prefixWord ++ tailWord_452921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452921).length < 2 ^ (prefixWord ++ tailWord_452921).sum := by decide
  have hdescent : baseEnd_452921 < baseStart_452921 := by decide
  rcases family_descends (prefixWord ++ tailWord_452921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452963 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 8]
def baseStart_452963 : Nat := 118140960795 + 452963 * 2 ^ 59
def prefixEnd_452963 : Nat := 4983230072969 + 3 ^ 40 * 452963 * 2
def baseEnd_452963 : Nat := 103372327867829561724163

theorem tailTrace_452963 : CollatzResearch.WordTrace tailWord_452963 prefixEnd_452963 103372327867829561724163 := by
  unfold tailWord_452963
  simp only [CollatzResearch.WordTrace]
  refine ⟨16520917857999885766571543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11013945238666590511047695 16520917857999885766571543)
  ·
    refine ⟨24781376786999828649857315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16520917857999885766571543 24781376786999828649857315)
    ·
      refine ⟨37172065180499742974785973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24781376786999828649857315 37172065180499742974785973)
      ·
        refine ⟨3484881110671850903886185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37172065180499742974785973 3484881110671850903886185)
        ·
          refine ⟨2613660833003888177914639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3484881110671850903886185 2613660833003888177914639)
          ·
            refine ⟨3920491249505832266871959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613660833003888177914639 3920491249505832266871959)
            ·
              refine ⟨5880736874258748400307939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920491249505832266871959 5880736874258748400307939)
              ·
                refine ⟨8821105311388122600461909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5880736874258748400307939 8821105311388122600461909)
                ·
                  refine ⟨103372327867829561724163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8821105311388122600461909 103372327867829561724163)
                  ·
                    rfl

theorem cell21_452963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_452963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_452963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_452963 prefixEnd_452963 := by exact prefixLift 452963
  have htrace : WordTrace (prefixWord ++ tailWord_452963) baseStart_452963 baseEnd_452963 := by
    simpa [prefixWord, tailWord_452963, baseEnd_452963] using wordTrace_append hprefix tailTrace_452963
  have hstable : (prefixWord ++ tailWord_452963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452963).length < 2 ^ (prefixWord ++ tailWord_452963).sum := by decide
  have hdescent : baseEnd_452963 < baseStart_452963 := by decide
  rcases family_descends (prefixWord ++ tailWord_452963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453042 : List Nat := [3, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_453042 : Nat := 118140960795 + 453042 * 2 ^ 59
def prefixEnd_453042 : Nat := 4983230072969 + 3 ^ 40 * 453042 * 2
def baseEnd_453042 : Nat := 103390356744142979907335

theorem tailTrace_453042 : CollatzResearch.WordTrace tailWord_453042 prefixEnd_453042 103390356744142979907335 := by
  unfold tailWord_453042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4130949806178420564674345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11015866149809121505798253 4130949806178420564674345)
  ·
    refine ⟨3098212354633815423505759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4130949806178420564674345 3098212354633815423505759)
    ·
      refine ⟨4647318531950723135258639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3098212354633815423505759 4647318531950723135258639)
      ·
        refine ⟨6970977797926084702887959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4647318531950723135258639 6970977797926084702887959)
        ·
          refine ⟨10456466696889127054331939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6970977797926084702887959 10456466696889127054331939)
          ·
            refine ⟨15684700045333690581497909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10456466696889127054331939 15684700045333690581497909)
            ·
              refine ⟨1470440629250033492015429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15684700045333690581497909 1470440629250033492015429)
              ·
                refine ⟨275707617984381279752893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1470440629250033492015429 275707617984381279752893)
                ·
                  refine ⟨103390356744142979907335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275707617984381279752893 103390356744142979907335)
                  ·
                    rfl

theorem cell21_453042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_453042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453042 prefixEnd_453042 := by exact prefixLift 453042
  have htrace : WordTrace (prefixWord ++ tailWord_453042) baseStart_453042 baseEnd_453042 := by
    simpa [prefixWord, tailWord_453042, baseEnd_453042] using wordTrace_append hprefix tailTrace_453042
  have hstable : (prefixWord ++ tailWord_453042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453042).length < 2 ^ (prefixWord ++ tailWord_453042).sum := by decide
  have hdescent : baseEnd_453042 < baseStart_453042 := by decide
  rcases family_descends (prefixWord ++ tailWord_453042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453090 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_453090 : Nat := 118140960795 + 453090 * 2 ^ 59
def prefixEnd_453090 : Nat := 4983230072969 + 3 ^ 40 * 453090 * 2
def baseEnd_453090 : Nat := 103401310998105563107237

theorem tailTrace_453090 : CollatzResearch.WordTrace tailWord_453090 prefixEnd_453090 103401310998105563107237 := by
  unfold tailWord_453090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4131387482134946614111181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11017033285693190970963149 4131387482134946614111181)
  ·
    refine ⟨1549270305800604980291693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4131387482134946614111181 1549270305800604980291693)
    ·
      refine ⟨580976364675226867609385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1549270305800604980291693 580976364675226867609385)
      ·
        refine ⟨435732273506420150707039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580976364675226867609385 435732273506420150707039)
        ·
          refine ⟨653598410259630226060559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435732273506420150707039 653598410259630226060559)
          ·
            refine ⟨980397615389445339090839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653598410259630226060559 980397615389445339090839)
            ·
              refine ⟨1470596423084168008636259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980397615389445339090839 1470596423084168008636259)
              ·
                refine ⟨2205894634626252012954389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470596423084168008636259 2205894634626252012954389)
                ·
                  refine ⟨103401310998105563107237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2205894634626252012954389 103401310998105563107237)
                  ·
                    rfl

theorem cell21_453090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_453090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453090 prefixEnd_453090 := by exact prefixLift 453090
  have htrace : WordTrace (prefixWord ++ tailWord_453090) baseStart_453090 baseEnd_453090 := by
    simpa [prefixWord, tailWord_453090, baseEnd_453090] using wordTrace_append hprefix tailTrace_453090
  have hstable : (prefixWord ++ tailWord_453090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453090).length < 2 ^ (prefixWord ++ tailWord_453090).sum := by decide
  have hdescent : baseEnd_453090 < baseStart_453090 := by decide
  rcases family_descends (prefixWord ++ tailWord_453090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453152 : List Nat := [2, 1, 1, 6, 2, 1, 3, 2, 3]
def baseStart_453152 : Nat := 118140960795 + 453152 * 2 ^ 59
def prefixEnd_453152 : Nat := 4983230072969 + 3 ^ 40 * 453152 * 2
def baseEnd_453152 : Nat := 103415460242807233073777

theorem tailTrace_453152 : CollatzResearch.WordTrace tailWord_453152 prefixEnd_453152 103415460242807233073777 := by
  unfold tailWord_453152
  simp only [CollatzResearch.WordTrace]
  refine ⟨8263905627157585522600855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11018540836210114030134473 8263905627157585522600855)
  ·
    refine ⟨12395858440736378283901283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8263905627157585522600855 12395858440736378283901283)
    ·
      refine ⟨18593787661104567425851925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12395858440736378283901283 18593787661104567425851925)
      ·
        refine ⟨871583796614276598086809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18593787661104567425851925 871583796614276598086809)
        ·
          refine ⟨653687847460707448565107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871583796614276598086809 653687847460707448565107)
          ·
            refine ⟨980531771191061172847661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653687847460707448565107 980531771191061172847661)
            ·
              refine ⟨367699414196647939817873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 980531771191061172847661 367699414196647939817873)
              ·
                refine ⟨275774560647485954863405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367699414196647939817873 275774560647485954863405)
                ·
                  refine ⟨103415460242807233073777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275774560647485954863405 103415460242807233073777)
                  ·
                    rfl

theorem cell21_453152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_453152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453152 prefixEnd_453152 := by exact prefixLift 453152
  have htrace : WordTrace (prefixWord ++ tailWord_453152) baseStart_453152 baseEnd_453152 := by
    simpa [prefixWord, tailWord_453152, baseEnd_453152] using wordTrace_append hprefix tailTrace_453152
  have hstable : (prefixWord ++ tailWord_453152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453152).length < 2 ^ (prefixWord ++ tailWord_453152).sum := by decide
  have hdescent : baseEnd_453152 < baseStart_453152 := by decide
  rcases family_descends (prefixWord ++ tailWord_453152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453214 : List Nat := [4, 4, 1, 2, 1, 2, 1, 6]
def baseStart_453214 : Nat := 118140960795 + 453214 * 2 ^ 59
def prefixEnd_453214 : Nat := 4983230072969 + 3 ^ 40 * 453214 * 2
def baseEnd_453214 : Nat := 34476536495836301013439

theorem tailTrace_453214 : CollatzResearch.WordTrace tailWord_453214 prefixEnd_453214 34476536495836301013439 := by
  unfold tailWord_453214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066259072511319454244837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11020048386727037089305797 2066259072511319454244837)
  ·
    refine ⟨387423576095872397670907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2066259072511319454244837 387423576095872397670907)
    ·
      refine ⟨581135364143808596506361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387423576095872397670907 581135364143808596506361)
      ·
        refine ⟨435851523107856447379771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581135364143808596506361 435851523107856447379771)
        ·
          refine ⟨653777284661784671069657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435851523107856447379771 653777284661784671069657)
          ·
            refine ⟨490332963496338503302243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653777284661784671069657 490332963496338503302243)
            ·
              refine ⟨735499445244507754953365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490332963496338503302243 735499445244507754953365)
              ·
                refine ⟨34476536495836301013439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 735499445244507754953365 34476536495836301013439)
                ·
                  rfl

theorem cell21_453214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_453214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453214 prefixEnd_453214 := by exact prefixLift 453214
  have htrace : WordTrace (prefixWord ++ tailWord_453214) baseStart_453214 baseEnd_453214 := by
    simpa [prefixWord, tailWord_453214, baseEnd_453214] using wordTrace_append hprefix tailTrace_453214
  have hstable : (prefixWord ++ tailWord_453214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453214).length < 2 ^ (prefixWord ++ tailWord_453214).sum := by decide
  have hdescent : baseEnd_453214 < baseStart_453214 := by decide
  rcases family_descends (prefixWord ++ tailWord_453214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453290 : List Nat := [3, 1, 5, 2, 2, 1, 2, 5]
def baseStart_453290 : Nat := 118140960795 + 453290 * 2 ^ 59
def prefixEnd_453290 : Nat := 4983230072969 + 3 ^ 40 * 453290 * 2
def baseEnd_453290 : Nat := 34482317907649886591165

theorem tailTrace_453290 : CollatzResearch.WordTrace tailWord_453290 prefixEnd_453290 34482317907649886591165 := by
  unfold tailWord_453290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133211131953805153431331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11021896351876813742483549 4133211131953805153431331)
  ·
    refine ⟨6199816697930707730146997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4133211131953805153431331 6199816697930707730146997)
    ·
      refine ⟨581232815431003849701281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6199816697930707730146997 581232815431003849701281)
      ·
        refine ⟨435924611573252887275961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581232815431003849701281 435924611573252887275961)
        ·
          refine ⟨326943458679939665456971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435924611573252887275961 326943458679939665456971)
          ·
            refine ⟨490415188019909498185457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326943458679939665456971 490415188019909498185457)
            ·
              refine ⟨367811391014932123639093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490415188019909498185457 367811391014932123639093)
              ·
                refine ⟨34482317907649886591165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367811391014932123639093 34482317907649886591165)
                ·
                  rfl

theorem cell21_453290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_453290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453290 prefixEnd_453290 := by exact prefixLift 453290
  have htrace : WordTrace (prefixWord ++ tailWord_453290) baseStart_453290 baseEnd_453290 := by
    simpa [prefixWord, tailWord_453290, baseEnd_453290] using wordTrace_append hprefix tailTrace_453290
  have hstable : (prefixWord ++ tailWord_453290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453290).length < 2 ^ (prefixWord ++ tailWord_453290).sum := by decide
  have hdescent : baseEnd_453290 < baseStart_453290 := by decide
  rcases family_descends (prefixWord ++ tailWord_453290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453374 : List Nat := [4, 2, 2, 1, 2, 10]
def baseStart_453374 : Nat := 118140960795 + 453374 * 2 ^ 59
def prefixEnd_453374 : Nat := 4983230072969 + 3 ^ 40 * 453374 * 2
def baseEnd_453374 : Nat := 3832078654347562236049

theorem tailTrace_453374 : CollatzResearch.WordTrace tailWord_453374 prefixEnd_453374 3832078654347562236049 := by
  unfold tailWord_453374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066988532438862869972897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11023938839673935306522117 2066988532438862869972897)
  ·
    refine ⟨1550241399329147152479673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2066988532438862869972897 1550241399329147152479673)
    ·
      refine ⟨1162681049496860364359755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1550241399329147152479673 1162681049496860364359755)
      ·
        refine ⟨1744021574245290546539633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162681049496860364359755 1744021574245290546539633)
        ·
          refine ⟨1308016180683967909904725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744021574245290546539633 1308016180683967909904725)
          ·
            refine ⟨3832078654347562236049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1308016180683967909904725 3832078654347562236049)
            ·
              rfl

theorem cell21_453374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 10].length) (baseStart_453374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453374 prefixEnd_453374 := by exact prefixLift 453374
  have htrace : WordTrace (prefixWord ++ tailWord_453374) baseStart_453374 baseEnd_453374 := by
    simpa [prefixWord, tailWord_453374, baseEnd_453374] using wordTrace_append hprefix tailTrace_453374
  have hstable : (prefixWord ++ tailWord_453374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453374).length < 2 ^ (prefixWord ++ tailWord_453374).sum := by decide
  have hdescent : baseEnd_453374 < baseStart_453374 := by decide
  rcases family_descends (prefixWord ++ tailWord_453374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453388 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_453388 : Nat := 118140960795 + 453388 * 2 ^ 59
def prefixEnd_453388 : Nat := 4983230072969 + 3 ^ 40 * 453388 * 2
def baseEnd_453388 : Nat := 103469318658123267139961

theorem tailTrace_453388 : CollatzResearch.WordTrace tailWord_453388 prefixEnd_453388 103469318658123267139961 := by
  unfold tailWord_453388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8268209440730091675396409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11024279254306788900528545 8268209440730091675396409)
  ·
    refine ⟨6201157080547568756547307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8268209440730091675396409 6201157080547568756547307)
    ·
      refine ⟨9301735620821353134820961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6201157080547568756547307 9301735620821353134820961)
      ·
        refine ⟨6976301715616014851115721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9301735620821353134820961 6976301715616014851115721)
        ·
          refine ⟨5232226286712011138336791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6976301715616014851115721 5232226286712011138336791)
          ·
            refine ⟨7848339430068016707505187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5232226286712011138336791 7848339430068016707505187)
            ·
              refine ⟨11772509145102025061257781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848339430068016707505187 11772509145102025061257781)
              ·
                refine ⟨1103672732353314849492917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11772509145102025061257781 1103672732353314849492917)
                ·
                  refine ⟨103469318658123267139961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1103672732353314849492917 103469318658123267139961)
                  ·
                    rfl

theorem cell21_453388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_453388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453388 prefixEnd_453388 := by exact prefixLift 453388
  have htrace : WordTrace (prefixWord ++ tailWord_453388) baseStart_453388 baseEnd_453388 := by
    simpa [prefixWord, tailWord_453388, baseEnd_453388] using wordTrace_append hprefix tailTrace_453388
  have hstable : (prefixWord ++ tailWord_453388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453388).length < 2 ^ (prefixWord ++ tailWord_453388).sum := by decide
  have hdescent : baseEnd_453388 < baseStart_453388 := by decide
  rcases family_descends (prefixWord ++ tailWord_453388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453509 : List Nat := [1, 3, 1, 1, 3, 3, 1, 8]
def baseStart_453509 : Nat := 118140960795 + 453509 * 2 ^ 59
def prefixEnd_453509 : Nat := 4983230072969 + 3 ^ 40 * 453509 * 2
def baseEnd_453509 : Nat := 34498977502217981874349

theorem tailTrace_453509 : CollatzResearch.WordTrace tailWord_453509 prefixEnd_453509 34498977502217981874349 := by
  unfold tailWord_453509
  simp only [CollatzResearch.WordTrace]
  refine ⟨16540832114021821015947581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11027221409347880677298387 16540832114021821015947581)
  ·
    refine ⟨6202812042758182880980343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16540832114021821015947581 6202812042758182880980343)
    ·
      refine ⟨9304218064137274321470515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6202812042758182880980343 9304218064137274321470515)
      ·
        refine ⟨13956327096205911482205773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9304218064137274321470515 13956327096205911482205773)
        ·
          refine ⟨5233622661077216805827165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13956327096205911482205773 5233622661077216805827165)
          ·
            refine ⟨1962608497903956302185187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5233622661077216805827165 1962608497903956302185187)
            ·
              refine ⟨2943912746855934453277781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962608497903956302185187 2943912746855934453277781)
              ·
                refine ⟨34498977502217981874349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2943912746855934453277781 34498977502217981874349)
                ·
                  rfl

theorem cell21_453509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 8].length) (baseStart_453509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453509 prefixEnd_453509 := by exact prefixLift 453509
  have htrace : WordTrace (prefixWord ++ tailWord_453509) baseStart_453509 baseEnd_453509 := by
    simpa [prefixWord, tailWord_453509, baseEnd_453509] using wordTrace_append hprefix tailTrace_453509
  have hstable : (prefixWord ++ tailWord_453509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453509).length < 2 ^ (prefixWord ++ tailWord_453509).sum := by decide
  have hdescent : baseEnd_453509 < baseStart_453509 := by decide
  rcases family_descends (prefixWord ++ tailWord_453509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453512 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_453512 : Nat := 118140960795 + 453512 * 2 ^ 59
def prefixEnd_453512 : Nat := 4983230072969 + 3 ^ 40 * 453512 * 2
def baseEnd_453512 : Nat := 103497617147526607073041

theorem tailTrace_453512 : CollatzResearch.WordTrace tailWord_453512 prefixEnd_453512 103497617147526607073041 := by
  unfold tailWord_453512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8270470766505476264153395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11027294355340635018871193 8270470766505476264153395)
  ·
    refine ⟨12405706149758214396230093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8270470766505476264153395 12405706149758214396230093)
    ·
      refine ⟨4652139806159330398586285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12405706149758214396230093 4652139806159330398586285)
      ·
        refine ⟨1744552427309748899469857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4652139806159330398586285 1744552427309748899469857)
        ·
          refine ⟨1308414320482311674602393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744552427309748899469857 1308414320482311674602393)
          ·
            refine ⟨981310740361733755951795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308414320482311674602393 981310740361733755951795)
            ·
              refine ⟨1471966110542600633927693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981310740361733755951795 1471966110542600633927693)
              ·
                refine ⟨551987291453475237722885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1471966110542600633927693 551987291453475237722885)
                ·
                  refine ⟨103497617147526607073041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 551987291453475237722885 103497617147526607073041)
                  ·
                    rfl

theorem cell21_453512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_453512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453512 prefixEnd_453512 := by exact prefixLift 453512
  have htrace : WordTrace (prefixWord ++ tailWord_453512) baseStart_453512 baseEnd_453512 := by
    simpa [prefixWord, tailWord_453512, baseEnd_453512] using wordTrace_append hprefix tailTrace_453512
  have hstable : (prefixWord ++ tailWord_453512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453512).length < 2 ^ (prefixWord ++ tailWord_453512).sum := by decide
  have hdescent : baseEnd_453512 < baseStart_453512 := by decide
  rcases family_descends (prefixWord ++ tailWord_453512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453549 : List Nat := [1, 5, 2, 3, 1, 2, 2, 2, 3]
def baseStart_453549 : Nat := 118140960795 + 453549 * 2 ^ 59
def prefixEnd_453549 : Nat := 4983230072969 + 3 ^ 40 * 453549 * 2
def baseEnd_453549 : Nat := 103506061051622764956299

theorem tailTrace_453549 : CollatzResearch.WordTrace tailWord_453549 prefixEnd_453549 103506061051622764956299 := by
  unfold tailWord_453549
  simp only [CollatzResearch.WordTrace]
  refine ⟨16542291033876907847403701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11028194022584605231602467 16542291033876907847403701)
  ·
    refine ⟨1550839784425960110694097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16542291033876907847403701 1550839784425960110694097)
    ·
      refine ⟨1163129838319470083020573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1550839784425960110694097 1163129838319470083020573)
      ·
        refine ⟨436173689369801281132715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1163129838319470083020573 436173689369801281132715)
        ·
          refine ⟨654260534054701921699073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436173689369801281132715 654260534054701921699073)
          ·
            refine ⟨490695400541026441274305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654260534054701921699073 490695400541026441274305)
            ·
              refine ⟨368021550405769830955729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490695400541026441274305 368021550405769830955729)
              ·
                refine ⟨276016162804327373216797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368021550405769830955729 276016162804327373216797)
                ·
                  refine ⟨103506061051622764956299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276016162804327373216797 103506061051622764956299)
                  ·
                    rfl

theorem cell21_453549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_453549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453549 prefixEnd_453549 := by exact prefixLift 453549
  have htrace : WordTrace (prefixWord ++ tailWord_453549) baseStart_453549 baseEnd_453549 := by
    simpa [prefixWord, tailWord_453549, baseEnd_453549] using wordTrace_append hprefix tailTrace_453549
  have hstable : (prefixWord ++ tailWord_453549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453549).length < 2 ^ (prefixWord ++ tailWord_453549).sum := by decide
  have hdescent : baseEnd_453549 < baseStart_453549 := by decide
  rcases family_descends (prefixWord ++ tailWord_453549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453678 : List Nat := [4, 1, 3, 1, 1, 1, 4, 6]
def baseStart_453678 : Nat := 118140960795 + 453678 * 2 ^ 59
def prefixEnd_453678 : Nat := 4983230072969 + 3 ^ 40 * 453678 * 2
def baseEnd_453678 : Nat := 34511833536382402435345

theorem tailTrace_453678 : CollatzResearch.WordTrace tailWord_453678 prefixEnd_453678 34511833536382402435345 := by
  unfold tailWord_453678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2068374506301195359856211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11031330700273041919233125 2068374506301195359856211)
  ·
    refine ⟨3102561759451793039784317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2068374506301195359856211 3102561759451793039784317)
    ·
      refine ⟨1163460659794422389919119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3102561759451793039784317 1163460659794422389919119)
      ·
        refine ⟨1745190989691633584878679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1163460659794422389919119 1745190989691633584878679)
        ·
          refine ⟨2617786484537450377318019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745190989691633584878679 2617786484537450377318019)
          ·
            refine ⟨3926679726806175565977029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617786484537450377318019 3926679726806175565977029)
            ·
              refine ⟨736252448776157918620693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3926679726806175565977029 736252448776157918620693)
              ·
                refine ⟨34511833536382402435345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 736252448776157918620693 34511833536382402435345)
                ·
                  rfl

theorem cell21_453678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_453678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453678 prefixEnd_453678 := by exact prefixLift 453678
  have htrace : WordTrace (prefixWord ++ tailWord_453678) baseStart_453678 baseEnd_453678 := by
    simpa [prefixWord, tailWord_453678, baseEnd_453678] using wordTrace_append hprefix tailTrace_453678
  have hstable : (prefixWord ++ tailWord_453678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453678).length < 2 ^ (prefixWord ++ tailWord_453678).sum := by decide
  have hdescent : baseEnd_453678 < baseStart_453678 := by decide
  rcases family_descends (prefixWord ++ tailWord_453678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453706 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_453706 : Nat := 118140960795 + 453706 * 2 ^ 59
def prefixEnd_453706 : Nat := 4983230072969 + 3 ^ 40 * 453706 * 2
def baseEnd_453706 : Nat := 103541890590625380839311

theorem tailTrace_453706 : CollatzResearch.WordTrace tailWord_453706 prefixEnd_453706 103541890590625380839311 := by
  unfold tailWord_453706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137004323577030915217243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11032011529538749107245981 4137004323577030915217243)
  ·
    refine ⟨6205506485365546372825865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4137004323577030915217243 6205506485365546372825865)
    ·
      refine ⟨4654129864024159779619399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6205506485365546372825865 4654129864024159779619399)
      ·
        refine ⟨6981194796036239669429099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4654129864024159779619399 6981194796036239669429099)
        ·
          refine ⟨10471792194054359504143649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6981194796036239669429099 10471792194054359504143649)
          ·
            refine ⟨7853844145540769628107737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10471792194054359504143649 7853844145540769628107737)
            ·
              refine ⟨5890383109155577221080803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7853844145540769628107737 5890383109155577221080803)
              ·
                refine ⟨8835574663733365831621205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5890383109155577221080803 8835574663733365831621205)
                ·
                  refine ⟨103541890590625380839311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8835574663733365831621205 103541890590625380839311)
                  ·
                    rfl

theorem cell21_453706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_453706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453706 prefixEnd_453706 := by exact prefixLift 453706
  have htrace : WordTrace (prefixWord ++ tailWord_453706) baseStart_453706 baseEnd_453706 := by
    simpa [prefixWord, tailWord_453706, baseEnd_453706] using wordTrace_append hprefix tailTrace_453706
  have hstable : (prefixWord ++ tailWord_453706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453706).length < 2 ^ (prefixWord ++ tailWord_453706).sum := by decide
  have hdescent : baseEnd_453706 < baseStart_453706 := by decide
  rcases family_descends (prefixWord ++ tailWord_453706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453718 : List Nat := [5, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_453718 : Nat := 118140960795 + 453718 * 2 ^ 59
def prefixEnd_453718 : Nat := 4983230072969 + 3 ^ 40 * 453718 * 2
def baseEnd_453718 : Nat := 103544629154116026639287

theorem tailTrace_453718 : CollatzResearch.WordTrace tailWord_453718 prefixEnd_453718 103544629154116026639287 := by
  unfold tailWord_453718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034278435641540606894113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11032303313509766473537205 1034278435641540606894113)
  ·
    refine ⟨775708826731155455170585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1034278435641540606894113 775708826731155455170585)
    ·
      refine ⟨581781620048366591377939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 775708826731155455170585 581781620048366591377939)
      ·
        refine ⟨872672430072549887066909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581781620048366591377939 872672430072549887066909)
        ·
          refine ⟨327252161277206207650091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 872672430072549887066909 327252161277206207650091)
          ·
            refine ⟨490878241915809311475137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327252161277206207650091 490878241915809311475137)
            ·
              refine ⟨368158681436856983606353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490878241915809311475137 368158681436856983606353)
              ·
                refine ⟨276119011077642737704765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368158681436856983606353 276119011077642737704765)
                ·
                  refine ⟨103544629154116026639287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276119011077642737704765 103544629154116026639287)
                  ·
                    rfl

theorem cell21_453718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_453718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453718 prefixEnd_453718 := by exact prefixLift 453718
  have htrace : WordTrace (prefixWord ++ tailWord_453718) baseStart_453718 baseEnd_453718 := by
    simpa [prefixWord, tailWord_453718, baseEnd_453718] using wordTrace_append hprefix tailTrace_453718
  have hstable : (prefixWord ++ tailWord_453718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453718).length < 2 ^ (prefixWord ++ tailWord_453718).sum := by decide
  have hdescent : baseEnd_453718 < baseStart_453718 := by decide
  rcases family_descends (prefixWord ++ tailWord_453718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453737 : List Nat := [1, 2, 1, 1, 1, 6, 3, 6]
def baseStart_453737 : Nat := 118140960795 + 453737 * 2 ^ 59
def prefixEnd_453737 : Nat := 4983230072969 + 3 ^ 40 * 453737 * 2
def baseEnd_453737 : Nat := 34516321737658738607527

theorem tailTrace_453737 : CollatzResearch.WordTrace tailWord_453737 prefixEnd_453737 34516321737658738607527 := by
  unfold tailWord_453737
  simp only [CollatzResearch.WordTrace]
  refine ⟨16549147957195815955247465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11032765304797210636831643 16549147957195815955247465)
  ·
    refine ⟨12411860967896861966435599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16549147957195815955247465 12411860967896861966435599)
    ·
      refine ⟨18617791451845292949653399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12411860967896861966435599 18617791451845292949653399)
      ·
        refine ⟨27926687177767939424480099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18617791451845292949653399 27926687177767939424480099)
        ·
          refine ⟨41890030766651909136720149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27926687177767939424480099 41890030766651909136720149)
          ·
            refine ⟨1963595192186808240783757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41890030766651909136720149 1963595192186808240783757)
            ·
              refine ⟨736348197070053090293909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1963595192186808240783757 736348197070053090293909)
              ·
                refine ⟨34516321737658738607527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 736348197070053090293909 34516321737658738607527)
                ·
                  rfl

theorem cell21_453737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 6].length) (baseStart_453737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453737 prefixEnd_453737 := by exact prefixLift 453737
  have htrace : WordTrace (prefixWord ++ tailWord_453737) baseStart_453737 baseEnd_453737 := by
    simpa [prefixWord, tailWord_453737, baseEnd_453737] using wordTrace_append hprefix tailTrace_453737
  have hstable : (prefixWord ++ tailWord_453737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453737).length < 2 ^ (prefixWord ++ tailWord_453737).sum := by decide
  have hdescent : baseEnd_453737 < baseStart_453737 := by decide
  rcases family_descends (prefixWord ++ tailWord_453737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453892 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_453892 : Nat := 118140960795 + 453892 * 2 ^ 59
def prefixEnd_453892 : Nat := 4983230072969 + 3 ^ 40 * 453892 * 2
def baseEnd_453892 : Nat := 103584338324730390738931

theorem tailTrace_453892 : CollatzResearch.WordTrace tailWord_453892 prefixEnd_453892 103584338324730390738931 := by
  unfold tailWord_453892
  simp only [CollatzResearch.WordTrace]
  refine ⟨8277400635817138713569965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11036534181089518284759953 8277400635817138713569965)
  ·
    refine ⟨3104025238431427017588737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8277400635817138713569965 3104025238431427017588737)
    ·
      refine ⟨2328018928823570263191553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3104025238431427017588737 2328018928823570263191553)
      ·
        refine ⟨1746014196617677697393665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2328018928823570263191553 1746014196617677697393665)
        ·
          refine ⟨1309510647463258273045249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746014196617677697393665 1309510647463258273045249)
          ·
            refine ⟨982132985597443704783937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309510647463258273045249 982132985597443704783937)
            ·
              refine ⟨736599739198082778587953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982132985597443704783937 736599739198082778587953)
              ·
                refine ⟨552449804398562083940965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736599739198082778587953 552449804398562083940965)
                ·
                  refine ⟨103584338324730390738931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552449804398562083940965 103584338324730390738931)
                  ·
                    rfl

theorem cell21_453892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_453892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453892 prefixEnd_453892 := by exact prefixLift 453892
  have htrace : WordTrace (prefixWord ++ tailWord_453892) baseStart_453892 baseEnd_453892 := by
    simpa [prefixWord, tailWord_453892, baseEnd_453892] using wordTrace_append hprefix tailTrace_453892
  have hstable : (prefixWord ++ tailWord_453892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453892).length < 2 ^ (prefixWord ++ tailWord_453892).sum := by decide
  have hdescent : baseEnd_453892 < baseStart_453892 := by decide
  rcases family_descends (prefixWord ++ tailWord_453892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453937 : List Nat := [1, 2, 2, 3, 3, 1, 1, 5, 3]
def baseStart_453937 : Nat := 118140960795 + 453937 * 2 ^ 59
def prefixEnd_453937 : Nat := 4983230072969 + 3 ^ 40 * 453937 * 2
def baseEnd_453937 : Nat := 103594607937820312488839

theorem tailTrace_453937 : CollatzResearch.WordTrace tailWord_453937 prefixEnd_453937 103594607937820312488839 := by
  unfold tailWord_453937
  simp only [CollatzResearch.WordTrace]
  refine ⟨16556442556471250112528065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11037628370980833408352043 16556442556471250112528065)
  ·
    refine ⟨12417331917353437584396049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16556442556471250112528065 12417331917353437584396049)
    ·
      refine ⟨9312998938015078188297037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12417331917353437584396049 9312998938015078188297037)
      ·
        refine ⟨3492374601755654320611389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9312998938015078188297037 3492374601755654320611389)
        ·
          refine ⟨1309640475658370370229271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3492374601755654320611389 1309640475658370370229271)
          ·
            refine ⟨1964460713487555555343907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309640475658370370229271 1964460713487555555343907)
            ·
              refine ⟨2946691070231333333015861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964460713487555555343907 2946691070231333333015861)
              ·
                refine ⟨276252287834187499970237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2946691070231333333015861 276252287834187499970237)
                ·
                  refine ⟨103594607937820312488839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276252287834187499970237 103594607937820312488839)
                  ·
                    rfl

theorem cell21_453937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_453937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453937 prefixEnd_453937 := by exact prefixLift 453937
  have htrace : WordTrace (prefixWord ++ tailWord_453937) baseStart_453937 baseEnd_453937 := by
    simpa [prefixWord, tailWord_453937, baseEnd_453937] using wordTrace_append hprefix tailTrace_453937
  have hstable : (prefixWord ++ tailWord_453937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453937).length < 2 ^ (prefixWord ++ tailWord_453937).sum := by decide
  have hdescent : baseEnd_453937 < baseStart_453937 := by decide
  rcases family_descends (prefixWord ++ tailWord_453937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453951 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 4]
def baseStart_453951 : Nat := 118140960795 + 453951 * 2 ^ 59
def prefixEnd_453951 : Nat := 4983230072969 + 3 ^ 40 * 453951 * 2
def baseEnd_453951 : Nat := 103597802928559399255477

theorem tailTrace_453951 : CollatzResearch.WordTrace tailWord_453951 prefixEnd_453951 103597802928559399255477 := by
  unfold tailWord_453951
  simp only [CollatzResearch.WordTrace]
  refine ⟨16556953178420530503537707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11037968785613687002358471 16556953178420530503537707)
  ·
    refine ⟨24835429767630795755306561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16556953178420530503537707 24835429767630795755306561)
    ·
      refine ⟨18626572325723096816479921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24835429767630795755306561 18626572325723096816479921)
      ·
        refine ⟨13969929244292322612359941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18626572325723096816479921 13969929244292322612359941)
        ·
          refine ⟨2619361733304810489817489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13969929244292322612359941 2619361733304810489817489)
          ·
            refine ⟨1964521299978607867363117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2619361733304810489817489 1964521299978607867363117)
            ·
              refine ⟨736695487491977950261169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1964521299978607867363117 736695487491977950261169)
              ·
                refine ⟨552521615618983462695877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736695487491977950261169 552521615618983462695877)
                ·
                  refine ⟨103597802928559399255477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552521615618983462695877 103597802928559399255477)
                  ·
                    rfl

theorem cell21_453951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 4].length) (baseStart_453951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453951 prefixEnd_453951 := by exact prefixLift 453951
  have htrace : WordTrace (prefixWord ++ tailWord_453951) baseStart_453951 baseEnd_453951 := by
    simpa [prefixWord, tailWord_453951, baseEnd_453951] using wordTrace_append hprefix tailTrace_453951
  have hstable : (prefixWord ++ tailWord_453951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453951).length < 2 ^ (prefixWord ++ tailWord_453951).sum := by decide
  have hdescent : baseEnd_453951 < baseStart_453951 := by decide
  rcases family_descends (prefixWord ++ tailWord_453951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453974 : List Nat := [5, 2, 3, 1, 1, 2, 2, 5]
def baseStart_453974 : Nat := 118140960795 + 453974 * 2 ^ 59
def prefixEnd_453974 : Nat := 4983230072969 + 3 ^ 40 * 453974 * 2
def baseEnd_453974 : Nat := 34534350613972156790699

theorem tailTrace_453974 : CollatzResearch.WordTrace tailWord_453974 prefixEnd_453974 34534350613972156790699 := by
  unfold tailWord_453974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034862003583575339476561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11038528038224803621083317 1034862003583575339476561)
  ·
    refine ⟨776146502687681504607421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1034862003583575339476561 776146502687681504607421)
    ·
      refine ⟨291054938507880564227783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 776146502687681504607421 291054938507880564227783)
      ·
        refine ⟨436582407761820846341675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291054938507880564227783 436582407761820846341675)
        ·
          refine ⟨654873611642731269512513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436582407761820846341675 654873611642731269512513)
          ·
            refine ⟨491155208732048452134385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654873611642731269512513 491155208732048452134385)
            ·
              refine ⟨368366406549036339100789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491155208732048452134385 368366406549036339100789)
              ·
                refine ⟨34534350613972156790699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368366406549036339100789 34534350613972156790699)
                ·
                  rfl

theorem cell21_453974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_453974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_453974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_453974 prefixEnd_453974 := by exact prefixLift 453974
  have htrace : WordTrace (prefixWord ++ tailWord_453974) baseStart_453974 baseEnd_453974 := by
    simpa [prefixWord, tailWord_453974, baseEnd_453974] using wordTrace_append hprefix tailTrace_453974
  have hstable : (prefixWord ++ tailWord_453974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453974).length < 2 ^ (prefixWord ++ tailWord_453974).sum := by decide
  have hdescent : baseEnd_453974 < baseStart_453974 := by decide
  rcases family_descends (prefixWord ++ tailWord_453974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454117 : List Nat := [1, 3, 1, 5, 1, 2, 8]
def baseStart_454117 : Nat := 118140960795 + 454117 * 2 ^ 59
def prefixEnd_454117 : Nat := 4983230072969 + 3 ^ 40 * 454117 * 2
def baseEnd_454117 : Nat := 11515076265575555498719

theorem tailTrace_454117 : CollatzResearch.WordTrace tailWord_454117 prefixEnd_454117 11515076265575555498719 := by
  unfold tailWord_454117
  simp only [CollatzResearch.WordTrace]
  refine ⟨16563007695819140854080605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11042005130546093902720403 16563007695819140854080605)
  ·
    refine ⟨6211127885932177820280227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16563007695819140854080605 6211127885932177820280227)
    ·
      refine ⟨9316691828898266730420341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6211127885932177820280227 9316691828898266730420341)
      ·
        refine ⟨873439858959212505976907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9316691828898266730420341 873439858959212505976907)
        ·
          refine ⟨1310159788438818758965361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873439858959212505976907 1310159788438818758965361)
          ·
            refine ⟨982619841329114069224021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1310159788438818758965361 982619841329114069224021)
            ·
              refine ⟨11515076265575555498719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 982619841329114069224021 11515076265575555498719)
              ·
                rfl

theorem cell21_454117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 8].length) (baseStart_454117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454117 prefixEnd_454117 := by exact prefixLift 454117
  have htrace : WordTrace (prefixWord ++ tailWord_454117) baseStart_454117 baseEnd_454117 := by
    simpa [prefixWord, tailWord_454117, baseEnd_454117] using wordTrace_append hprefix tailTrace_454117
  have hstable : (prefixWord ++ tailWord_454117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454117).length < 2 ^ (prefixWord ++ tailWord_454117).sum := by decide
  have hdescent : baseEnd_454117 < baseStart_454117 := by decide
  rcases family_descends (prefixWord ++ tailWord_454117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454157 : List Nat := [1, 7, 1, 1, 3, 1, 1, 3, 3]
def baseStart_454157 : Nat := 118140960795 + 454157 * 2 ^ 59
def prefixEnd_454157 : Nat := 4983230072969 + 3 ^ 40 * 454157 * 2
def baseEnd_454157 : Nat := 103644814935148818821723

theorem tailTrace_454157 : CollatzResearch.WordTrace tailWord_454157 prefixEnd_454157 103644814935148818821723 := by
  unfold tailWord_454157
  simp only [CollatzResearch.WordTrace]
  refine ⟨16564466615674227685536725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11042977743782818457024483 16564466615674227685536725)
  ·
    refine ⟨388229686304864711379767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16564466615674227685536725 388229686304864711379767)
    ·
      refine ⟨582344529457297067069651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388229686304864711379767 582344529457297067069651)
      ·
        refine ⟨873516794185945600604477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582344529457297067069651 873516794185945600604477)
        ·
          refine ⟨327568797819729600226679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 873516794185945600604477 327568797819729600226679)
          ·
            refine ⟨491353196729594400340019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327568797819729600226679 491353196729594400340019)
            ·
              refine ⟨737029795094391600510029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491353196729594400340019 737029795094391600510029)
              ·
                refine ⟨276386173160396850191261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737029795094391600510029 276386173160396850191261)
                ·
                  refine ⟨103644814935148818821723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276386173160396850191261 103644814935148818821723)
                  ·
                    rfl

theorem cell21_454157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_454157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454157 prefixEnd_454157 := by exact prefixLift 454157
  have htrace : WordTrace (prefixWord ++ tailWord_454157) baseStart_454157 baseEnd_454157 := by
    simpa [prefixWord, tailWord_454157, baseEnd_454157] using wordTrace_append hprefix tailTrace_454157
  have hstable : (prefixWord ++ tailWord_454157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454157).length < 2 ^ (prefixWord ++ tailWord_454157).sum := by decide
  have hdescent : baseEnd_454157 < baseStart_454157 := by decide
  rcases family_descends (prefixWord ++ tailWord_454157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454165 : List Nat := [1, 3, 2, 1, 3, 2, 3, 3, 3]
def baseStart_454165 : Nat := 118140960795 + 454165 * 2 ^ 59
def prefixEnd_454165 : Nat := 4983230072969 + 3 ^ 40 * 454165 * 2
def baseEnd_454165 : Nat := 103646640644142582688373

theorem tailTrace_454165 : CollatzResearch.WordTrace tailWord_454165 prefixEnd_454165 103646640644142582688373 := by
  unfold tailWord_454165
  simp only [CollatzResearch.WordTrace]
  refine ⟨16564758399645245051827949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11043172266430163367885299 16564758399645245051827949)
  ·
    refine ⟨6211784399866966894435481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16564758399645245051827949 6211784399866966894435481)
    ·
      refine ⟨4658838299900225170826611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6211784399866966894435481 4658838299900225170826611)
      ·
        refine ⟨6988257449850337756239917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658838299900225170826611 6988257449850337756239917)
        ·
          refine ⟨2620596543693876658589969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6988257449850337756239917 2620596543693876658589969)
          ·
            refine ⟨1965447407770407493942477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620596543693876658589969 1965447407770407493942477)
            ·
              refine ⟨737042777913902810228429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1965447407770407493942477 737042777913902810228429)
              ·
                refine ⟨276391041717713553835661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737042777913902810228429 276391041717713553835661)
                ·
                  refine ⟨103646640644142582688373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276391041717713553835661 103646640644142582688373)
                  ·
                    rfl

theorem cell21_454165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_454165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454165 prefixEnd_454165 := by exact prefixLift 454165
  have htrace : WordTrace (prefixWord ++ tailWord_454165) baseStart_454165 baseEnd_454165 := by
    simpa [prefixWord, tailWord_454165, baseEnd_454165] using wordTrace_append hprefix tailTrace_454165
  have hstable : (prefixWord ++ tailWord_454165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454165).length < 2 ^ (prefixWord ++ tailWord_454165).sum := by decide
  have hdescent : baseEnd_454165 < baseStart_454165 := by decide
  rcases family_descends (prefixWord ++ tailWord_454165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454224 : List Nat := [2, 1, 1, 1, 1, 3, 4, 5, 3]
def baseStart_454224 : Nat := 118140960795 + 454224 * 2 ^ 59
def prefixEnd_454224 : Nat := 4983230072969 + 3 ^ 40 * 454224 * 2
def baseEnd_454224 : Nat := 103660105247971591204919

theorem tailTrace_454224 : CollatzResearch.WordTrace tailWord_454224 prefixEnd_454224 103660105247971591204919 := by
  unfold tailWord_454224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8283455153215749064112863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11044606870954332085483817 8283455153215749064112863)
  ·
    refine ⟨12425182729823623596169295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8283455153215749064112863 12425182729823623596169295)
    ·
      refine ⟨18637774094735435394253943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12425182729823623596169295 18637774094735435394253943)
      ·
        refine ⟨27956661142103153091380915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18637774094735435394253943 27956661142103153091380915)
        ·
          refine ⟨41934991713154729637071373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27956661142103153091380915 41934991713154729637071373)
          ·
            refine ⟨15725621892433023613901765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41934991713154729637071373 15725621892433023613901765)
            ·
              refine ⟨2948554104831191927606581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15725621892433023613901765 2948554104831191927606581)
              ·
                refine ⟨276426947327924243213117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2948554104831191927606581 276426947327924243213117)
                ·
                  refine ⟨103660105247971591204919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276426947327924243213117 103660105247971591204919)
                  ·
                    rfl

theorem cell21_454224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_454224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454224 prefixEnd_454224 := by exact prefixLift 454224
  have htrace : WordTrace (prefixWord ++ tailWord_454224) baseStart_454224 baseEnd_454224 := by
    simpa [prefixWord, tailWord_454224, baseEnd_454224] using wordTrace_append hprefix tailTrace_454224
  have hstable : (prefixWord ++ tailWord_454224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454224).length < 2 ^ (prefixWord ++ tailWord_454224).sum := by decide
  have hdescent : baseEnd_454224 < baseStart_454224 := by decide
  rcases family_descends (prefixWord ++ tailWord_454224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454230 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_454230 : Nat := 118140960795 + 454230 * 2 ^ 59
def prefixEnd_454230 : Nat := 4983230072969 + 3 ^ 40 * 454230 * 2
def baseEnd_454230 : Nat := 103661474529716914104907

theorem tailTrace_454230 : CollatzResearch.WordTrace tailWord_454230 prefixEnd_454230 103661474529716914104907 := by
  unfold tailWord_454230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035445571525610072059009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11044752762939840768629429 1035445571525610072059009)
  ·
    refine ⟨776584178644207554044257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1035445571525610072059009 776584178644207554044257)
    ·
      refine ⟨582438133983155665533193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 776584178644207554044257 582438133983155665533193)
      ·
        refine ⟨436828600487366749149895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582438133983155665533193 436828600487366749149895)
        ·
          refine ⟨655242900731050123724843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436828600487366749149895 655242900731050123724843)
          ·
            refine ⟨982864351096575185587265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655242900731050123724843 982864351096575185587265)
            ·
              refine ⟨737148263322431389190449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982864351096575185587265 737148263322431389190449)
              ·
                refine ⟨552861197491823541892837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737148263322431389190449 552861197491823541892837)
                ·
                  refine ⟨103661474529716914104907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552861197491823541892837 103661474529716914104907)
                  ·
                    rfl

theorem cell21_454230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_454230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454230 prefixEnd_454230 := by exact prefixLift 454230
  have htrace : WordTrace (prefixWord ++ tailWord_454230) baseStart_454230 baseEnd_454230 := by
    simpa [prefixWord, tailWord_454230, baseEnd_454230] using wordTrace_append hprefix tailTrace_454230
  have hstable : (prefixWord ++ tailWord_454230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454230).length < 2 ^ (prefixWord ++ tailWord_454230).sum := by decide
  have hdescent : baseEnd_454230 < baseStart_454230 := by decide
  rcases family_descends (prefixWord ++ tailWord_454230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454334 : List Nat := [4, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_454334 : Nat := 118140960795 + 454334 * 2 ^ 59
def prefixEnd_454334 : Nat := 4983230072969 + 3 ^ 40 * 454334 * 2
def baseEnd_454334 : Nat := 103685208746635844371361

theorem tailTrace_454334 : CollatzResearch.WordTrace tailWord_454334 prefixEnd_454334 103685208746635844371361 := by
  unfold tailWord_454334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2071365292004123364341257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11047281557355324609820037 2071365292004123364341257)
  ·
    refine ⟨1553523969003092523255943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2071365292004123364341257 1553523969003092523255943)
    ·
      refine ⟨2330285953504638784883915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1553523969003092523255943 2330285953504638784883915)
      ·
        refine ⟨3495428930256958177325873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330285953504638784883915 3495428930256958177325873)
        ·
          refine ⟨2621571697692718632994405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3495428930256958177325873 2621571697692718632994405)
          ·
            refine ⟨491544693317384743686451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2621571697692718632994405 491544693317384743686451)
            ·
              refine ⟨737317039976077115529677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491544693317384743686451 737317039976077115529677)
              ·
                refine ⟨276493889991028918323629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737317039976077115529677 276493889991028918323629)
                ·
                  refine ⟨103685208746635844371361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276493889991028918323629 103685208746635844371361)
                  ·
                    rfl

theorem cell21_454334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_454334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454334 prefixEnd_454334 := by exact prefixLift 454334
  have htrace : WordTrace (prefixWord ++ tailWord_454334) baseStart_454334 baseEnd_454334 := by
    simpa [prefixWord, tailWord_454334, baseEnd_454334] using wordTrace_append hprefix tailTrace_454334
  have hstable : (prefixWord ++ tailWord_454334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454334).length < 2 ^ (prefixWord ++ tailWord_454334).sum := by decide
  have hdescent : baseEnd_454334 < baseStart_454334 := by decide
  rcases family_descends (prefixWord ++ tailWord_454334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454404 : List Nat := [2, 3, 2, 2, 1, 11]
def baseStart_454404 : Nat := 118140960795 + 454404 * 2 ^ 59
def prefixEnd_454404 : Nat := 4983230072969 + 3 ^ 40 * 454404 * 2
def baseEnd_454404 : Nat := 3840784581493751044613

theorem tailTrace_454404 : CollatzResearch.WordTrace tailWord_454404 prefixEnd_454404 3840784581493751044613 := by
  unfold tailWord_454404
  simp only [CollatzResearch.WordTrace]
  refine ⟨8286737722889694434889133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11048983630519592579852177 8286737722889694434889133)
  ·
    refine ⟨3107526646083635413083425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8286737722889694434889133 3107526646083635413083425)
    ·
      refine ⟨2330644984562726559812569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3107526646083635413083425 2330644984562726559812569)
      ·
        refine ⟨1747983738422044919859427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2330644984562726559812569 1747983738422044919859427)
        ·
          refine ⟨2621975607633067379789141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747983738422044919859427 2621975607633067379789141)
          ·
            refine ⟨3840784581493751044613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2621975607633067379789141 3840784581493751044613)
            ·
              rfl

theorem cell21_454404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 11].length) (baseStart_454404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454404 prefixEnd_454404 := by exact prefixLift 454404
  have htrace : WordTrace (prefixWord ++ tailWord_454404) baseStart_454404 baseEnd_454404 := by
    simpa [prefixWord, tailWord_454404, baseEnd_454404] using wordTrace_append hprefix tailTrace_454404
  have hstable : (prefixWord ++ tailWord_454404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454404).length < 2 ^ (prefixWord ++ tailWord_454404).sum := by decide
  have hdescent : baseEnd_454404 < baseStart_454404 := by decide
  rcases family_descends (prefixWord ++ tailWord_454404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454410 : List Nat := [3, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_454410 : Nat := 118140960795 + 454410 * 2 ^ 59
def prefixEnd_454410 : Nat := 4983230072969 + 3 ^ 40 * 454410 * 2
def baseEnd_454410 : Nat := 103702552982076601104539

theorem tailTrace_454410 : CollatzResearch.WordTrace tailWord_454410 prefixEnd_454410 103702552982076601104539 := by
  unfold tailWord_454410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143423570939412973624171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11049129522505101262997789 4143423570939412973624171)
  ·
    refine ⟨6215135356409119460436257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4143423570939412973624171 6215135356409119460436257)
    ·
      refine ⟨4661351517306839595327193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6215135356409119460436257 4661351517306839595327193)
      ·
        refine ⟨3496013637980129696495395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4661351517306839595327193 3496013637980129696495395)
        ·
          refine ⟨5244020456970194544743093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496013637980129696495395 5244020456970194544743093)
          ·
            refine ⟨491626917840955738569665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5244020456970194544743093 491626917840955738569665)
            ·
              refine ⟨368720188380716803927249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491626917840955738569665 368720188380716803927249)
              ·
                refine ⟨276540141285537602945437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368720188380716803927249 276540141285537602945437)
                ·
                  refine ⟨103702552982076601104539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276540141285537602945437 103702552982076601104539)
                  ·
                    rfl

theorem cell21_454410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_454410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454410 prefixEnd_454410 := by exact prefixLift 454410
  have htrace : WordTrace (prefixWord ++ tailWord_454410) baseStart_454410 baseEnd_454410 := by
    simpa [prefixWord, tailWord_454410, baseEnd_454410] using wordTrace_append hprefix tailTrace_454410
  have hstable : (prefixWord ++ tailWord_454410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454410).length < 2 ^ (prefixWord ++ tailWord_454410).sum := by decide
  have hdescent : baseEnd_454410 < baseStart_454410 := by decide
  rcases family_descends (prefixWord ++ tailWord_454410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454413 : List Nat := [1, 7, 2, 1, 1, 2, 1, 6]
def baseStart_454413 : Nat := 118140960795 + 454413 * 2 ^ 59
def prefixEnd_454413 : Nat := 4983230072969 + 3 ^ 40 * 454413 * 2
def baseEnd_454413 : Nat := 34567745874316420851511

theorem tailTrace_454413 : CollatzResearch.WordTrace tailWord_454413 prefixEnd_454413 34567745874316420851511 := by
  unfold tailWord_454413
  simp only [CollatzResearch.WordTrace]
  refine ⟨16573803702746783406855893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11049202468497855604570595 16573803702746783406855893)
  ·
    refine ⟨388448524283127736098185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16573803702746783406855893 388448524283127736098185)
    ·
      refine ⟨291336393212345802073639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388448524283127736098185 291336393212345802073639)
      ·
        refine ⟨437004589818518703110459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291336393212345802073639 437004589818518703110459)
        ·
          refine ⟨655506884727778054665689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437004589818518703110459 655506884727778054665689)
          ·
            refine ⟨491630163545833540999267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655506884727778054665689 491630163545833540999267)
            ·
              refine ⟨737445245318750311498901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491630163545833540999267 737445245318750311498901)
              ·
                refine ⟨34567745874316420851511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 737445245318750311498901 34567745874316420851511)
                ·
                  rfl

theorem cell21_454413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 6].length) (baseStart_454413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454413 prefixEnd_454413 := by exact prefixLift 454413
  have htrace : WordTrace (prefixWord ++ tailWord_454413) baseStart_454413 baseEnd_454413 := by
    simpa [prefixWord, tailWord_454413, baseEnd_454413] using wordTrace_append hprefix tailTrace_454413
  have hstable : (prefixWord ++ tailWord_454413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454413).length < 2 ^ (prefixWord ++ tailWord_454413).sum := by decide
  have hdescent : baseEnd_454413 < baseStart_454413 := by decide
  rcases family_descends (prefixWord ++ tailWord_454413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454421 : List Nat := [1, 3, 2, 1, 2, 5, 1, 6]
def baseStart_454421 : Nat := 118140960795 + 454421 * 2 ^ 59
def prefixEnd_454421 : Nat := 4983230072969 + 3 ^ 40 * 454421 * 2
def baseEnd_454421 : Nat := 34568354443981008807061

theorem tailTrace_454421 : CollatzResearch.WordTrace tailWord_454421 prefixEnd_454421 34568354443981008807061 := by
  unfold tailWord_454421
  simp only [CollatzResearch.WordTrace]
  refine ⟨16574095486717800773147117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11049396991145200515431411 16574095486717800773147117)
  ·
    refine ⟨6215285807519175289930169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16574095486717800773147117 6215285807519175289930169)
    ·
      refine ⟨4661464355639381467447627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6215285807519175289930169 4661464355639381467447627)
      ·
        refine ⟨6992196533459072201171441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661464355639381467447627 6992196533459072201171441)
        ·
          refine ⟨5244147400094304150878581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6992196533459072201171441 5244147400094304150878581)
          ·
            refine ⟨491638818758841014144867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5244147400094304150878581 491638818758841014144867)
            ·
              refine ⟨737458228138261521217301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491638818758841014144867 737458228138261521217301)
              ·
                refine ⟨34568354443981008807061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 737458228138261521217301 34568354443981008807061)
                ·
                  rfl

theorem cell21_454421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 6].length) (baseStart_454421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454421 prefixEnd_454421 := by exact prefixLift 454421
  have htrace : WordTrace (prefixWord ++ tailWord_454421) baseStart_454421 baseEnd_454421 := by
    simpa [prefixWord, tailWord_454421, baseEnd_454421] using wordTrace_append hprefix tailTrace_454421
  have hstable : (prefixWord ++ tailWord_454421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454421).length < 2 ^ (prefixWord ++ tailWord_454421).sum := by decide
  have hdescent : baseEnd_454421 < baseStart_454421 := by decide
  rcases family_descends (prefixWord ++ tailWord_454421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454663 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 5]
def baseStart_454663 : Nat := 118140960795 + 454663 * 2 ^ 59
def prefixEnd_454663 : Nat := 4983230072969 + 3 ^ 40 * 454663 * 2
def baseEnd_454663 : Nat := 103760291029004383387355

theorem tailTrace_454663 : CollatzResearch.WordTrace tailWord_454663 prefixEnd_454663 103760291029004383387355 := by
  unfold tailWord_454663
  simp only [CollatzResearch.WordTrace]
  refine ⟨16582921951841076103456643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11055281301227384068971095 16582921951841076103456643)
  ·
    refine ⟨24874382927761614155184965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16582921951841076103456643 24874382927761614155184965)
    ·
      refine ⟨4663946798955302654097181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24874382927761614155184965 4663946798955302654097181)
      ·
        refine ⟨1748980049608238495286443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4663946798955302654097181 1748980049608238495286443)
        ·
          refine ⟨2623470074412357742929665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748980049608238495286443 2623470074412357742929665)
          ·
            refine ⟨1967602555809268307197249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2623470074412357742929665 1967602555809268307197249)
            ·
              refine ⟨1475701916856951230397937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967602555809268307197249 1475701916856951230397937)
              ·
                refine ⟨1106776437642713422798453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475701916856951230397937 1106776437642713422798453)
                ·
                  refine ⟨103760291029004383387355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1106776437642713422798453 103760291029004383387355)
                  ·
                    rfl

theorem cell21_454663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_454663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454663 prefixEnd_454663 := by exact prefixLift 454663
  have htrace : WordTrace (prefixWord ++ tailWord_454663) baseStart_454663 baseEnd_454663 := by
    simpa [prefixWord, tailWord_454663, baseEnd_454663] using wordTrace_append hprefix tailTrace_454663
  have hstable : (prefixWord ++ tailWord_454663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454663).length < 2 ^ (prefixWord ++ tailWord_454663).sum := by decide
  have hdescent : baseEnd_454663 < baseStart_454663 := by decide
  rcases family_descends (prefixWord ++ tailWord_454663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454666 : List Nat := [3, 1, 2, 2, 4, 2, 2, 5]
def baseStart_454666 : Nat := 118140960795 + 454666 * 2 ^ 59
def prefixEnd_454666 : Nat := 4983230072969 + 3 ^ 40 * 454666 * 2
def baseEnd_454666 : Nat := 34586991889959014945783

theorem tailTrace_454666 : CollatzResearch.WordTrace tailWord_454666 prefixEnd_454666 34586991889959014945783 := by
  unfold tailWord_454666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4145757842707551903953963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11055354247220138410543901 4145757842707551903953963)
  ·
    refine ⟨6218636764061327855930945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4145757842707551903953963 6218636764061327855930945)
    ·
      refine ⟨4663977573045995891948209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6218636764061327855930945 4663977573045995891948209)
      ·
        refine ⟨3497983179784496918961157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4663977573045995891948209 3497983179784496918961157)
        ·
          refine ⟨655871846209593172305217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3497983179784496918961157 655871846209593172305217)
          ·
            refine ⟨491903884657194879228913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655871846209593172305217 491903884657194879228913)
            ·
              refine ⟨368927913492896159421685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491903884657194879228913 368927913492896159421685)
              ·
                refine ⟨34586991889959014945783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368927913492896159421685 34586991889959014945783)
                ·
                  rfl

theorem cell21_454666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_454666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454666 prefixEnd_454666 := by exact prefixLift 454666
  have htrace : WordTrace (prefixWord ++ tailWord_454666) baseStart_454666 baseEnd_454666 := by
    simpa [prefixWord, tailWord_454666, baseEnd_454666] using wordTrace_append hprefix tailTrace_454666
  have hstable : (prefixWord ++ tailWord_454666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454666).length < 2 ^ (prefixWord ++ tailWord_454666).sum := by decide
  have hdescent : baseEnd_454666 < baseStart_454666 := by decide
  rcases family_descends (prefixWord ++ tailWord_454666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454770 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_454770 : Nat := 118140960795 + 454770 * 2 ^ 59
def prefixEnd_454770 : Nat := 4983230072969 + 3 ^ 40 * 454770 * 2
def baseEnd_454770 : Nat := 103784709886795975103803

theorem tailTrace_454770 : CollatzResearch.WordTrace tailWord_454770 prefixEnd_454770 103784709886795975103803 := by
  unfold tailWord_454770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4146706140613358344400441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11057883041635622251734509 4146706140613358344400441)
  ·
    refine ⟨3110029605460018758300331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4146706140613358344400441 3110029605460018758300331)
    ·
      refine ⟨4665044408190028137450497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3110029605460018758300331 4665044408190028137450497)
      ·
        refine ⟨3498783306142521103087873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4665044408190028137450497 3498783306142521103087873)
        ·
          refine ⟨2624087479606890827315905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3498783306142521103087873 2624087479606890827315905)
          ·
            refine ⟨1968065609705168120486929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2624087479606890827315905 1968065609705168120486929)
            ·
              refine ⟨1476049207278876090365197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968065609705168120486929 1476049207278876090365197)
              ·
                refine ⟨553518452729578533886949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1476049207278876090365197 553518452729578533886949)
                ·
                  refine ⟨103784709886795975103803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 553518452729578533886949 103784709886795975103803)
                  ·
                    rfl

theorem cell21_454770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_454770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454770 prefixEnd_454770 := by exact prefixLift 454770
  have htrace : WordTrace (prefixWord ++ tailWord_454770) baseStart_454770 baseEnd_454770 := by
    simpa [prefixWord, tailWord_454770, baseEnd_454770] using wordTrace_append hprefix tailTrace_454770
  have hstable : (prefixWord ++ tailWord_454770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454770).length < 2 ^ (prefixWord ++ tailWord_454770).sum := by decide
  have hdescent : baseEnd_454770 < baseStart_454770 := by decide
  rcases family_descends (prefixWord ++ tailWord_454770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454815 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 5]
def baseStart_454815 : Nat := 118140960795 + 454815 * 2 ^ 59
def prefixEnd_454815 : Nat := 4983230072969 + 3 ^ 40 * 454815 * 2
def baseEnd_454815 : Nat := 103794979499885896853711

theorem tailTrace_454815 : CollatzResearch.WordTrace tailWord_454815 prefixEnd_454815 103794979499885896853711 := by
  unfold tailWord_454815
  simp only [CollatzResearch.WordTrace]
  refine ⟨16588465847290406062989899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11058977231526937375326599 16588465847290406062989899)
  ·
    refine ⟨24882698770935609094484849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16588465847290406062989899 24882698770935609094484849)
    ·
      refine ⟨18662024078201706820863637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24882698770935609094484849 18662024078201706820863637)
      ·
        refine ⟨874782378665705007227983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18662024078201706820863637 874782378665705007227983)
        ·
          refine ⟨1312173567998557510841975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874782378665705007227983 1312173567998557510841975)
          ·
            refine ⟨1968260351997836266262963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312173567998557510841975 1968260351997836266262963)
            ·
              refine ⟨2952390527996754399394445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968260351997836266262963 2952390527996754399394445)
              ·
                refine ⟨1107146447998782899772917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2952390527996754399394445 1107146447998782899772917)
                ·
                  refine ⟨103794979499885896853711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1107146447998782899772917 103794979499885896853711)
                  ·
                    rfl

theorem cell21_454815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_454815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454815 prefixEnd_454815 := by exact prefixLift 454815
  have htrace : WordTrace (prefixWord ++ tailWord_454815) baseStart_454815 baseEnd_454815 := by
    simpa [prefixWord, tailWord_454815, baseEnd_454815] using wordTrace_append hprefix tailTrace_454815
  have hstable : (prefixWord ++ tailWord_454815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454815).length < 2 ^ (prefixWord ++ tailWord_454815).sum := by decide
  have hdescent : baseEnd_454815 < baseStart_454815 := by decide
  rcases family_descends (prefixWord ++ tailWord_454815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454843 : List Nat := [1, 1, 1, 1, 1, 2, 7, 7]
def baseStart_454843 : Nat := 118140960795 + 454843 * 2 ^ 59
def prefixEnd_454843 : Nat := 4983230072969 + 3 ^ 40 * 454843 * 2
def baseEnd_454843 : Nat := 34600456493788023462329

theorem tailTrace_454843 : CollatzResearch.WordTrace tailWord_454843 prefixEnd_454843 34600456493788023462329 := by
  unfold tailWord_454843
  simp only [CollatzResearch.WordTrace]
  refine ⟨16589487091188966845009183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11059658060792644563339455 16589487091188966845009183)
  ·
    refine ⟨24884230636783450267513775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16589487091188966845009183 24884230636783450267513775)
    ·
      refine ⟨37326345955175175401270663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24884230636783450267513775 37326345955175175401270663)
      ·
        refine ⟨55989518932762763101905995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37326345955175175401270663 55989518932762763101905995)
        ·
          refine ⟨83984278399144144652858993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55989518932762763101905995 83984278399144144652858993)
          ·
            refine ⟨62988208799358108489644245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83984278399144144652858993 62988208799358108489644245)
            ·
              refine ⟨1476286143734955667726037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62988208799358108489644245 1476286143734955667726037)
              ·
                refine ⟨34600456493788023462329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1476286143734955667726037 34600456493788023462329)
                ·
                  rfl

theorem cell21_454843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 7].length) (baseStart_454843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454843 prefixEnd_454843 := by exact prefixLift 454843
  have htrace : WordTrace (prefixWord ++ tailWord_454843) baseStart_454843 baseEnd_454843 := by
    simpa [prefixWord, tailWord_454843, baseEnd_454843] using wordTrace_append hprefix tailTrace_454843
  have hstable : (prefixWord ++ tailWord_454843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454843).length < 2 ^ (prefixWord ++ tailWord_454843).sum := by decide
  have hdescent : baseEnd_454843 < baseStart_454843 := by decide
  rcases family_descends (prefixWord ++ tailWord_454843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454877 : List Nat := [1, 4, 3, 2, 1, 2, 2, 6]
def baseStart_454877 : Nat := 118140960795 + 454877 * 2 ^ 59
def prefixEnd_454877 : Nat := 4983230072969 + 3 ^ 40 * 454877 * 2
def baseEnd_454877 : Nat := 34603042914862522273417

theorem tailTrace_454877 : CollatzResearch.WordTrace tailWord_454877 prefixEnd_454877 34603042914862522273417 := by
  unfold tailWord_454877
  simp only [CollatzResearch.WordTrace]
  refine ⟨16590727173065790651746885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11060484782043860434497923 16590727173065790651746885)
  ·
    refine ⟨3110761344949835747202541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16590727173065790651746885 3110761344949835747202541)
    ·
      refine ⟨1166535504356188405200953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3110761344949835747202541 1166535504356188405200953)
      ·
        refine ⟨874901628267141303900715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1166535504356188405200953 874901628267141303900715)
        ·
          refine ⟨1312352442400711955851073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874901628267141303900715 1312352442400711955851073)
          ·
            refine ⟨984264331800533966888305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1312352442400711955851073 984264331800533966888305)
            ·
              refine ⟨738198248850400475166229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984264331800533966888305 738198248850400475166229)
              ·
                refine ⟨34603042914862522273417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 738198248850400475166229 34603042914862522273417)
                ·
                  rfl

theorem cell21_454877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 6].length) (baseStart_454877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_454877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_454877 prefixEnd_454877 := by exact prefixLift 454877
  have htrace : WordTrace (prefixWord ++ tailWord_454877) baseStart_454877 baseEnd_454877 := by
    simpa [prefixWord, tailWord_454877, baseEnd_454877] using wordTrace_append hprefix tailTrace_454877
  have hstable : (prefixWord ++ tailWord_454877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454877).length < 2 ^ (prefixWord ++ tailWord_454877).sum := by decide
  have hdescent : baseEnd_454877 < baseStart_454877 := by decide
  rcases family_descends (prefixWord ++ tailWord_454877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455071 : List Nat := [1, 1, 2, 5, 1, 1, 1, 9]
def baseStart_455071 : Nat := 118140960795 + 455071 * 2 ^ 59
def prefixEnd_455071 : Nat := 4983230072969 + 3 ^ 40 * 455071 * 2
def baseEnd_455071 : Nat := 34617800729228780195507

theorem tailTrace_455071 : CollatzResearch.WordTrace tailWord_455071 prefixEnd_455071 34617800729228780195507 := by
  unfold tailWord_455071
  simp only [CollatzResearch.WordTrace]
  refine ⟨16597802934362961784309067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11065201956241974522872711 16597802934362961784309067)
  ·
    refine ⟨24896704401544442676463601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16597802934362961784309067 24896704401544442676463601)
    ·
      refine ⟨18672528301158332007347701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24896704401544442676463601 18672528301158332007347701)
      ·
        refine ⟨1750549528233593625688847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18672528301158332007347701 1750549528233593625688847)
        ·
          refine ⟨2625824292350390438533271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750549528233593625688847 2625824292350390438533271)
          ·
            refine ⟨3938736438525585657799907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625824292350390438533271 3938736438525585657799907)
            ·
              refine ⟨5908104657788378486699861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938736438525585657799907 5908104657788378486699861)
              ·
                refine ⟨34617800729228780195507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5908104657788378486699861 34617800729228780195507)
                ·
                  rfl

theorem cell21_455071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 9].length) (baseStart_455071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455071 prefixEnd_455071 := by exact prefixLift 455071
  have htrace : WordTrace (prefixWord ++ tailWord_455071) baseStart_455071 baseEnd_455071 := by
    simpa [prefixWord, tailWord_455071, baseEnd_455071] using wordTrace_append hprefix tailTrace_455071
  have hstable : (prefixWord ++ tailWord_455071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455071).length < 2 ^ (prefixWord ++ tailWord_455071).sum := by decide
  have hdescent : baseEnd_455071 < baseStart_455071 := by decide
  rcases family_descends (prefixWord ++ tailWord_455071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455122 : List Nat := [3, 2, 2, 4, 1, 1, 3, 5]
def baseStart_455122 : Nat := 118140960795 + 455122 * 2 ^ 59
def prefixEnd_455122 : Nat := 4983230072969 + 3 ^ 40 * 455122 * 2
def baseEnd_455122 : Nat := 34621680360840528412139

theorem tailTrace_455122 : CollatzResearch.WordTrace tailWord_455122 prefixEnd_455122 34621680360840528412139 := by
  unfold tailWord_455122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149915764294549373603905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11066442038118798329610413 4149915764294549373603905)
  ·
    refine ⟨3112436823220912030202929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4149915764294549373603905 3112436823220912030202929)
    ·
      refine ⟨2334327617415684022652197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3112436823220912030202929 2334327617415684022652197)
      ·
        refine ⟨437686428265440754247287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2334327617415684022652197 437686428265440754247287)
        ·
          refine ⟨656529642398161131370931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437686428265440754247287 656529642398161131370931)
          ·
            refine ⟨984794463597241697056397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656529642398161131370931 984794463597241697056397)
            ·
              refine ⟨369297923848965636396149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 984794463597241697056397 369297923848965636396149)
              ·
                refine ⟨34621680360840528412139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 369297923848965636396149 34621680360840528412139)
                ·
                  rfl

theorem cell21_455122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_455122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455122 prefixEnd_455122 := by exact prefixLift 455122
  have htrace : WordTrace (prefixWord ++ tailWord_455122) baseStart_455122 baseEnd_455122 := by
    simpa [prefixWord, tailWord_455122, baseEnd_455122] using wordTrace_append hprefix tailTrace_455122
  have hstable : (prefixWord ++ tailWord_455122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455122).length < 2 ^ (prefixWord ++ tailWord_455122).sum := by decide
  have hdescent : baseEnd_455122 < baseStart_455122 := by decide
  rcases family_descends (prefixWord ++ tailWord_455122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455133 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 6]
def baseStart_455133 : Nat := 118140960795 + 455133 * 2 ^ 59
def prefixEnd_455133 : Nat := 4983230072969 + 3 ^ 40 * 455133 * 2
def baseEnd_455133 : Nat := 103867551432388010553061

theorem tailTrace_455133 : CollatzResearch.WordTrace tailWord_455133 prefixEnd_455133 103867551432388010553061 := by
  unfold tailWord_455133
  simp only [CollatzResearch.WordTrace]
  refine ⟨16600064260138346373066053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11066709506758897582044035 16600064260138346373066053)
  ·
    refine ⟨3112512048775939944949885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16600064260138346373066053 3112512048775939944949885)
    ·
      refine ⟨1167192018290977479356207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3112512048775939944949885 1167192018290977479356207)
      ·
        refine ⟨1750788027436466219034311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167192018290977479356207 1750788027436466219034311)
        ·
          refine ⟨2626182041154699328551467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750788027436466219034311 2626182041154699328551467)
          ·
            refine ⟨3939273061732048992827201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626182041154699328551467 3939273061732048992827201)
            ·
              refine ⟨2954454796299036744620401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3939273061732048992827201 2954454796299036744620401)
              ·
                refine ⟨2215841097224277558465301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954454796299036744620401 2215841097224277558465301)
                ·
                  refine ⟨103867551432388010553061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2215841097224277558465301 103867551432388010553061)
                  ·
                    rfl

theorem cell21_455133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_455133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455133 prefixEnd_455133 := by exact prefixLift 455133
  have htrace : WordTrace (prefixWord ++ tailWord_455133) baseStart_455133 baseEnd_455133 := by
    simpa [prefixWord, tailWord_455133, baseEnd_455133] using wordTrace_append hprefix tailTrace_455133
  have hstable : (prefixWord ++ tailWord_455133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455133).length < 2 ^ (prefixWord ++ tailWord_455133).sum := by decide
  have hdescent : baseEnd_455133 < baseStart_455133 := by decide
  rcases family_descends (prefixWord ++ tailWord_455133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455150 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_455150 : Nat := 118140960795 + 455150 * 2 ^ 59
def prefixEnd_455150 : Nat := 4983230072969 + 3 ^ 40 * 455150 * 2
def baseEnd_455150 : Nat := 103871431063999758769693

theorem tailTrace_455150 : CollatzResearch.WordTrace tailWord_455150 prefixEnd_455150 103871431063999758769693 := by
  unfold tailWord_455150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075085537634594784554363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11067122867384505517623269 2075085537634594784554363)
  ·
    refine ⟨3112628306451892176831545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2075085537634594784554363 3112628306451892176831545)
    ·
      refine ⟨2334471229838919132623659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3112628306451892176831545 2334471229838919132623659)
      ·
        refine ⟨3501706844758378698935489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2334471229838919132623659 3501706844758378698935489)
        ·
          refine ⟨2626280133568784024201617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3501706844758378698935489 2626280133568784024201617)
          ·
            refine ⟨1969710100176588018151213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2626280133568784024201617 1969710100176588018151213)
            ·
              refine ⟨738641287566220506806705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1969710100176588018151213 738641287566220506806705)
              ·
                refine ⟨553980965674665380105029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738641287566220506806705 553980965674665380105029)
                ·
                  refine ⟨103871431063999758769693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 553980965674665380105029 103871431063999758769693)
                  ·
                    rfl

theorem cell21_455150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_455150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455150 prefixEnd_455150 := by exact prefixLift 455150
  have htrace : WordTrace (prefixWord ++ tailWord_455150) baseStart_455150 baseEnd_455150 := by
    simpa [prefixWord, tailWord_455150, baseEnd_455150] using wordTrace_append hprefix tailTrace_455150
  have hstable : (prefixWord ++ tailWord_455150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455150).length < 2 ^ (prefixWord ++ tailWord_455150).sum := by decide
  have hdescent : baseEnd_455150 < baseStart_455150 := by decide
  rcases family_descends (prefixWord ++ tailWord_455150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455178 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_455178 : Nat := 118140960795 + 455178 * 2 ^ 59
def prefixEnd_455178 : Nat := 4983230072969 + 3 ^ 40 * 455178 * 2
def baseEnd_455178 : Nat := 103877821045477932302969

theorem tailTrace_455178 : CollatzResearch.WordTrace tailWord_455178 prefixEnd_455178 103877821045477932302969 := by
  unfold tailWord_455178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4150426386243829764613547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11067803696650212705636125 4150426386243829764613547)
  ·
    refine ⟨6225639579365744646920321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4150426386243829764613547 6225639579365744646920321)
    ·
      refine ⟨4669229684524308485190241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6225639579365744646920321 4669229684524308485190241)
      ·
        refine ⟨3501922263393231363892681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4669229684524308485190241 3501922263393231363892681)
        ·
          refine ⟨2626441697544923522919511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3501922263393231363892681 2626441697544923522919511)
          ·
            refine ⟨3939662546317385284379267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626441697544923522919511 3939662546317385284379267)
            ·
              refine ⟨5909493819476077926568901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939662546317385284379267 5909493819476077926568901)
              ·
                refine ⟨1108030091151764611231669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5909493819476077926568901 1108030091151764611231669)
                ·
                  refine ⟨103877821045477932302969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1108030091151764611231669 103877821045477932302969)
                  ·
                    rfl

theorem cell21_455178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_455178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455178 prefixEnd_455178 := by exact prefixLift 455178
  have htrace : WordTrace (prefixWord ++ tailWord_455178) baseStart_455178 baseEnd_455178 := by
    simpa [prefixWord, tailWord_455178, baseEnd_455178] using wordTrace_append hprefix tailTrace_455178
  have hstable : (prefixWord ++ tailWord_455178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455178).length < 2 ^ (prefixWord ++ tailWord_455178).sum := by decide
  have hdescent : baseEnd_455178 < baseStart_455178 := by decide
  rcases family_descends (prefixWord ++ tailWord_455178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455223 : List Nat := [1, 1, 3, 1, 2, 3, 4, 6]
def baseStart_455223 : Nat := 118140960795 + 455223 * 2 ^ 59
def prefixEnd_455223 : Nat := 4983230072969 + 3 ^ 40 * 455223 * 2
def baseEnd_455223 : Nat := 34629363552855951350959

theorem tailTrace_455223 : CollatzResearch.WordTrace tailWord_455223 prefixEnd_455223 34629363552855951350959 := by
  unfold tailWord_455223
  simp only [CollatzResearch.WordTrace]
  refine ⟨16603346829812291743842323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11068897886541527829228215 16603346829812291743842323)
  ·
    refine ⟨24905020244718437615763485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16603346829812291743842323 24905020244718437615763485)
    ·
      refine ⟨9339382591769414105911307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24905020244718437615763485 9339382591769414105911307)
      ·
        refine ⟨14009073887654121158866961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9339382591769414105911307 14009073887654121158866961)
        ·
          refine ⟨10506805415740590869150221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14009073887654121158866961 10506805415740590869150221)
          ·
            refine ⟨3940052030902721575931333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10506805415740590869150221 3940052030902721575931333)
            ·
              refine ⟨738759755794260295487125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3940052030902721575931333 738759755794260295487125)
              ·
                refine ⟨34629363552855951350959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 738759755794260295487125 34629363552855951350959)
                ·
                  rfl

theorem cell21_455223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 6].length) (baseStart_455223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455223 prefixEnd_455223 := by exact prefixLift 455223
  have htrace : WordTrace (prefixWord ++ tailWord_455223) baseStart_455223 baseEnd_455223 := by
    simpa [prefixWord, tailWord_455223, baseEnd_455223] using wordTrace_append hprefix tailTrace_455223
  have hstable : (prefixWord ++ tailWord_455223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455223).length < 2 ^ (prefixWord ++ tailWord_455223).sum := by decide
  have hdescent : baseEnd_455223 < baseStart_455223 := by decide
  rcases family_descends (prefixWord ++ tailWord_455223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455226 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_455226 : Nat := 118140960795 + 455226 * 2 ^ 59
def prefixEnd_455226 : Nat := 4983230072969 + 3 ^ 40 * 455226 * 2
def baseEnd_455226 : Nat := 103888775299440515502871

theorem tailTrace_455226 : CollatzResearch.WordTrace tailWord_455226 prefixEnd_455226 103888775299440515502871 := by
  unfold tailWord_455226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4150864062200355814050383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11068970832534282170801021 4150864062200355814050383)
  ·
    refine ⟨6226296093300533721075575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4150864062200355814050383 6226296093300533721075575)
    ·
      refine ⟨9339444139950800581613363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6226296093300533721075575 9339444139950800581613363)
      ·
        refine ⟨14009166209926200872420045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9339444139950800581613363 14009166209926200872420045)
        ·
          refine ⟨5253437328722325327157517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14009166209926200872420045 5253437328722325327157517)
          ·
            refine ⟨1970038998270871997684069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5253437328722325327157517 1970038998270871997684069)
            ·
              refine ⟨369382312175788499565763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1970038998270871997684069 369382312175788499565763)
              ·
                refine ⟨554073468263682749348645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369382312175788499565763 554073468263682749348645)
                ·
                  refine ⟨103888775299440515502871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554073468263682749348645 103888775299440515502871)
                  ·
                    rfl

theorem cell21_455226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_455226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455226 prefixEnd_455226 := by exact prefixLift 455226
  have htrace : WordTrace (prefixWord ++ tailWord_455226) baseStart_455226 baseEnd_455226 := by
    simpa [prefixWord, tailWord_455226, baseEnd_455226] using wordTrace_append hprefix tailTrace_455226
  have hstable : (prefixWord ++ tailWord_455226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455226).length < 2 ^ (prefixWord ++ tailWord_455226).sum := by decide
  have hdescent : baseEnd_455226 < baseStart_455226 := by decide
  rcases family_descends (prefixWord ++ tailWord_455226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455316 : List Nat := [2, 4, 2, 2, 1, 2, 8]
def baseStart_455316 : Nat := 118140960795 + 455316 * 2 ^ 59
def prefixEnd_455316 : Nat := 4983230072969 + 3 ^ 40 * 455316 * 2
def baseEnd_455316 : Nat := 11545479391735595444743

theorem tailTrace_455316 : CollatzResearch.WordTrace tailWord_455316 prefixEnd_455316 11545479391735595444743 := by
  unfold tailWord_455316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8303369409237684313488901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11071159212316912417985201 8303369409237684313488901)
  ·
    refine ⟨1556881764232065808779169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8303369409237684313488901 1556881764232065808779169)
    ·
      refine ⟨1167661323174049356584377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1556881764232065808779169 1167661323174049356584377)
      ·
        refine ⟨875745992380537017438283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1167661323174049356584377 875745992380537017438283)
        ·
          refine ⟨1313618988570805526157425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875745992380537017438283 1313618988570805526157425)
          ·
            refine ⟨985214241428104144618069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1313618988570805526157425 985214241428104144618069)
            ·
              refine ⟨11545479391735595444743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 985214241428104144618069 11545479391735595444743)
              ·
                rfl

theorem cell21_455316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 8].length) (baseStart_455316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455316 prefixEnd_455316 := by exact prefixLift 455316
  have htrace : WordTrace (prefixWord ++ tailWord_455316) baseStart_455316 baseEnd_455316 := by
    simpa [prefixWord, tailWord_455316, baseEnd_455316] using wordTrace_append hprefix tailTrace_455316
  have hstable : (prefixWord ++ tailWord_455316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455316).length < 2 ^ (prefixWord ++ tailWord_455316).sum := by decide
  have hdescent : baseEnd_455316 < baseStart_455316 := by decide
  rcases family_descends (prefixWord ++ tailWord_455316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455364 : List Nat := [2, 3, 3, 1, 1, 2, 3, 3, 3]
def baseStart_455364 : Nat := 118140960795 + 455364 * 2 ^ 59
def prefixEnd_455364 : Nat := 4983230072969 + 3 ^ 40 * 455364 * 2
def baseEnd_455364 : Nat := 103920268779582942202589

theorem tailTrace_455364 : CollatzResearch.WordTrace tailWord_455364 prefixEnd_455364 103920268779582942202589 := by
  unfold tailWord_455364
  simp only [CollatzResearch.WordTrace]
  refine ⟨8304244761150736412362573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11072326348200981883150097 8304244761150736412362573)
  ·
    refine ⟨3114091785431526154635965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8304244761150736412362573 3114091785431526154635965)
    ·
      refine ⟨1167784419536822307988487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3114091785431526154635965 1167784419536822307988487)
      ·
        refine ⟨1751676629305233461982731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167784419536822307988487 1751676629305233461982731)
        ·
          refine ⟨2627514943957850192974097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751676629305233461982731 2627514943957850192974097)
          ·
            refine ⟨1970636207968387644730573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2627514943957850192974097 1970636207968387644730573)
            ·
              refine ⟨738988577988145366773965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1970636207968387644730573 738988577988145366773965)
              ·
                refine ⟨277120716745554512540237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 738988577988145366773965 277120716745554512540237)
                ·
                  refine ⟨103920268779582942202589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277120716745554512540237 103920268779582942202589)
                  ·
                    rfl

theorem cell21_455364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_455364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455364 prefixEnd_455364 := by exact prefixLift 455364
  have htrace : WordTrace (prefixWord ++ tailWord_455364) baseStart_455364 baseEnd_455364 := by
    simpa [prefixWord, tailWord_455364, baseEnd_455364] using wordTrace_append hprefix tailTrace_455364
  have hstable : (prefixWord ++ tailWord_455364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455364).length < 2 ^ (prefixWord ++ tailWord_455364).sum := by decide
  have hdescent : baseEnd_455364 < baseStart_455364 := by decide
  rcases family_descends (prefixWord ++ tailWord_455364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455381 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 5]
def baseStart_455381 : Nat := 118140960795 + 455381 * 2 ^ 59
def prefixEnd_455381 : Nat := 4983230072969 + 3 ^ 40 * 455381 * 2
def baseEnd_455381 : Nat := 103924148411194690419221

theorem tailTrace_455381 : CollatzResearch.WordTrace tailWord_455381 prefixEnd_455381 103924148411194690419221 := by
  unfold tailWord_455381
  simp only [CollatzResearch.WordTrace]
  refine ⟨16609109563239884728093997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11072739708826589818729331 16609109563239884728093997)
  ·
    refine ⟨6228416086214956773035249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16609109563239884728093997 6228416086214956773035249)
    ·
      refine ⟨4671312064661217579776437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6228416086214956773035249 4671312064661217579776437)
      ·
        refine ⟨437935506061989148104041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4671312064661217579776437 437935506061989148104041)
        ·
          refine ⟨328451629546491861078031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437935506061989148104041 328451629546491861078031)
          ·
            refine ⟨492677444319737791617047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328451629546491861078031 492677444319737791617047)
            ·
              refine ⟨739016166479606687425571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492677444319737791617047 739016166479606687425571)
              ·
                refine ⟨1108524249719410031138357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739016166479606687425571 1108524249719410031138357)
                ·
                  refine ⟨103924148411194690419221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1108524249719410031138357 103924148411194690419221)
                  ·
                    rfl

theorem cell21_455381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_455381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455381 prefixEnd_455381 := by exact prefixLift 455381
  have htrace : WordTrace (prefixWord ++ tailWord_455381) baseStart_455381 baseEnd_455381 := by
    simpa [prefixWord, tailWord_455381, baseEnd_455381] using wordTrace_append hprefix tailTrace_455381
  have hstable : (prefixWord ++ tailWord_455381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455381).length < 2 ^ (prefixWord ++ tailWord_455381).sum := by decide
  have hdescent : baseEnd_455381 < baseStart_455381 := by decide
  rcases family_descends (prefixWord ++ tailWord_455381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455395 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 4]
def baseStart_455395 : Nat := 118140960795 + 455395 * 2 ^ 59
def prefixEnd_455395 : Nat := 4983230072969 + 3 ^ 40 * 455395 * 2
def baseEnd_455395 : Nat := 103927343401933777185859

theorem tailTrace_455395 : CollatzResearch.WordTrace tailWord_455395 prefixEnd_455395 103927343401933777185859 := by
  unfold tailWord_455395
  simp only [CollatzResearch.WordTrace]
  refine ⟨16609620185189165119103639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11073080123459443412735759 16609620185189165119103639)
  ·
    refine ⟨24914430277783747678655459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16609620185189165119103639 24914430277783747678655459)
    ·
      refine ⟨37371645416675621517983189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24914430277783747678655459 37371645416675621517983189)
      ·
        refine ⟨875897939453334879327731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37371645416675621517983189 875897939453334879327731)
        ·
          refine ⟨1313846909180002318991597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875897939453334879327731 1313846909180002318991597)
          ·
            refine ⟨492692590942500869621849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1313846909180002318991597 492692590942500869621849)
            ·
              refine ⟨369519443206875652216387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492692590942500869621849 369519443206875652216387)
              ·
                refine ⟨554279164810313478324581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369519443206875652216387 554279164810313478324581)
                ·
                  refine ⟨103927343401933777185859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554279164810313478324581 103927343401933777185859)
                  ·
                    rfl

theorem cell21_455395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 4].length) (baseStart_455395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455395 prefixEnd_455395 := by exact prefixLift 455395
  have htrace : WordTrace (prefixWord ++ tailWord_455395) baseStart_455395 baseEnd_455395 := by
    simpa [prefixWord, tailWord_455395, baseEnd_455395] using wordTrace_append hprefix tailTrace_455395
  have hstable : (prefixWord ++ tailWord_455395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455395).length < 2 ^ (prefixWord ++ tailWord_455395).sum := by decide
  have hdescent : baseEnd_455395 < baseStart_455395 := by decide
  rcases family_descends (prefixWord ++ tailWord_455395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455465 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 5]
def baseStart_455465 : Nat := 118140960795 + 455465 * 2 ^ 59
def prefixEnd_455465 : Nat := 4983230072969 + 3 ^ 40 * 455465 * 2
def baseEnd_455465 : Nat := 103943318355629211019049

theorem tailTrace_455465 : CollatzResearch.WordTrace tailWord_455465 prefixEnd_455465 103943318355629211019049 := by
  unfold tailWord_455465
  simp only [CollatzResearch.WordTrace]
  refine ⟨16612173294935567074151849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11074782196623711382767899 16612173294935567074151849)
  ·
    refine ⟨12459129971201675305613887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16612173294935567074151849 12459129971201675305613887)
    ·
      refine ⟨18688694956802512958420831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12459129971201675305613887 18688694956802512958420831)
      ·
        refine ⟨28033042435203769437631247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18688694956802512958420831 28033042435203769437631247)
        ·
          refine ⟨42049563652805654156446871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28033042435203769437631247 42049563652805654156446871)
          ·
            refine ⟨63074345479208481234670307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42049563652805654156446871 63074345479208481234670307)
            ·
              refine ⟨94611518218812721852005461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63074345479208481234670307 94611518218812721852005461)
              ·
                refine ⟨1108728729126711584203189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 94611518218812721852005461 1108728729126711584203189)
                ·
                  refine ⟨103943318355629211019049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1108728729126711584203189 103943318355629211019049)
                  ·
                    rfl

theorem cell21_455465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_455465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455465 prefixEnd_455465 := by exact prefixLift 455465
  have htrace : WordTrace (prefixWord ++ tailWord_455465) baseStart_455465 baseEnd_455465 := by
    simpa [prefixWord, tailWord_455465, baseEnd_455465] using wordTrace_append hprefix tailTrace_455465
  have hstable : (prefixWord ++ tailWord_455465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455465).length < 2 ^ (prefixWord ++ tailWord_455465).sum := by decide
  have hdescent : baseEnd_455465 < baseStart_455465 := by decide
  rcases family_descends (prefixWord ++ tailWord_455465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455496 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_455496 : Nat := 118140960795 + 455496 * 2 ^ 59
def prefixEnd_455496 : Nat := 4983230072969 + 3 ^ 40 * 455496 * 2
def baseEnd_455496 : Nat := 103950392977980046002319

theorem tailTrace_455496 : CollatzResearch.WordTrace tailWord_455496 prefixEnd_455496 103950392977980046002319 := by
  unfold tailWord_455496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306651978911629684265171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11075535971882172912353561 8306651978911629684265171)
  ·
    refine ⟨12459977968367444526397757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8306651978911629684265171 12459977968367444526397757)
    ·
      refine ⟨4672491738137791697399159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12459977968367444526397757 4672491738137791697399159)
      ·
        refine ⟨7008737607206687546098739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672491738137791697399159 7008737607206687546098739)
        ·
          refine ⟨10513106410810031319148109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008737607206687546098739 10513106410810031319148109)
          ·
            refine ⟨3942414904053761744680541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10513106410810031319148109 3942414904053761744680541)
            ·
              refine ⟨1478405589020160654255203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3942414904053761744680541 1478405589020160654255203)
              ·
                refine ⟨2217608383530240981382805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478405589020160654255203 2217608383530240981382805)
                ·
                  refine ⟨103950392977980046002319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2217608383530240981382805 103950392977980046002319)
                  ·
                    rfl

theorem cell21_455496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_455496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455496 prefixEnd_455496 := by exact prefixLift 455496
  have htrace : WordTrace (prefixWord ++ tailWord_455496) baseStart_455496 baseEnd_455496 := by
    simpa [prefixWord, tailWord_455496, baseEnd_455496] using wordTrace_append hprefix tailTrace_455496
  have hstable : (prefixWord ++ tailWord_455496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455496).length < 2 ^ (prefixWord ++ tailWord_455496).sum := by decide
  have hdescent : baseEnd_455496 < baseStart_455496 := by decide
  rcases family_descends (prefixWord ++ tailWord_455496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455527 : List Nat := [1, 1, 5, 1, 2, 3, 1, 7]
def baseStart_455527 : Nat := 118140960795 + 455527 * 2 ^ 59
def prefixEnd_455527 : Nat := 4983230072969 + 3 ^ 40 * 455527 * 2
def baseEnd_455527 : Nat := 34652489200110293661863

theorem tailTrace_455527 : CollatzResearch.WordTrace tailWord_455527 prefixEnd_455527 34652489200110293661863 := by
  unfold tailWord_455527
  simp only [CollatzResearch.WordTrace]
  refine ⟨16614434620710951662908835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11076289747140634441939223 16614434620710951662908835)
  ·
    refine ⟨24921651931066427494363253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16614434620710951662908835 24921651931066427494363253)
    ·
      refine ⟨2336404868537477577596555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24921651931066427494363253 2336404868537477577596555)
      ·
        refine ⟨3504607302806216366394833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336404868537477577596555 3504607302806216366394833)
        ·
          refine ⟨2628455477104662274796125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3504607302806216366394833 2628455477104662274796125)
          ·
            refine ⟨985670803914248353048547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2628455477104662274796125 985670803914248353048547)
            ·
              refine ⟨1478506205871372529572821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985670803914248353048547 1478506205871372529572821)
              ·
                refine ⟨34652489200110293661863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1478506205871372529572821 34652489200110293661863)
                ·
                  rfl

theorem cell21_455527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 7].length) (baseStart_455527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455527 prefixEnd_455527 := by exact prefixLift 455527
  have htrace : WordTrace (prefixWord ++ tailWord_455527) baseStart_455527 baseEnd_455527 := by
    simpa [prefixWord, tailWord_455527, baseEnd_455527] using wordTrace_append hprefix tailTrace_455527
  have hstable : (prefixWord ++ tailWord_455527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455527).length < 2 ^ (prefixWord ++ tailWord_455527).sum := by decide
  have hdescent : baseEnd_455527 < baseStart_455527 := by decide
  rcases family_descends (prefixWord ++ tailWord_455527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455550 : List Nat := [4, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_455550 : Nat := 118140960795 + 455550 * 2 ^ 59
def prefixEnd_455550 : Nat := 4983230072969 + 3 ^ 40 * 455550 * 2
def baseEnd_455550 : Nat := 103962716513687952102209

theorem tailTrace_455550 : CollatzResearch.WordTrace tailWord_455550 prefixEnd_455550 103962716513687952102209 := by
  unfold tailWord_455550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2076909187453453323874513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11076848999751751060664069 2076909187453453323874513)
  ·
    refine ⟨1557681890590089992905885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2076909187453453323874513 1557681890590089992905885)
    ·
      refine ⟨584130708971283747339707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1557681890590089992905885 584130708971283747339707)
      ·
        refine ⟨876196063456925621009561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584130708971283747339707 876196063456925621009561)
        ·
          refine ⟨657147047592694215757171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876196063456925621009561 657147047592694215757171)
          ·
            refine ⟨985720571389041323635757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657147047592694215757171 985720571389041323635757)
            ·
              refine ⟨369645214270890496363409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 985720571389041323635757 369645214270890496363409)
              ·
                refine ⟨277233910703167872272557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369645214270890496363409 277233910703167872272557)
                ·
                  refine ⟨103962716513687952102209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277233910703167872272557 103962716513687952102209)
                  ·
                    rfl

theorem cell21_455550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_455550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455550 prefixEnd_455550 := by exact prefixLift 455550
  have htrace : WordTrace (prefixWord ++ tailWord_455550) baseStart_455550 baseEnd_455550 := by
    simpa [prefixWord, tailWord_455550, baseEnd_455550] using wordTrace_append hprefix tailTrace_455550
  have hstable : (prefixWord ++ tailWord_455550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455550).length < 2 ^ (prefixWord ++ tailWord_455550).sum := by decide
  have hdescent : baseEnd_455550 < baseStart_455550 := by decide
  rcases family_descends (prefixWord ++ tailWord_455550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455634 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_455634 : Nat := 118140960795 + 455634 * 2 ^ 59
def prefixEnd_455634 : Nat := 4983230072969 + 3 ^ 40 * 455634 * 2
def baseEnd_455634 : Nat := 103981886458122472702037

theorem tailTrace_455634 : CollatzResearch.WordTrace tailWord_455634 prefixEnd_455634 103981886458122472702037 := by
  unfold tailWord_455634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4154584307830827234263489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11078891487548872624702637 4154584307830827234263489)
  ·
    refine ⟨3115938230873120425697617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4154584307830827234263489 3115938230873120425697617)
    ·
      refine ⟨2336953673154840319273213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3115938230873120425697617 2336953673154840319273213)
      ·
        refine ⟨876357627433065119727455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2336953673154840319273213 876357627433065119727455)
        ·
          refine ⟨1314536441149597679591183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876357627433065119727455 1314536441149597679591183)
          ·
            refine ⟨1971804661724396519386775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314536441149597679591183 1971804661724396519386775)
            ·
              refine ⟨2957706992586594779080163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971804661724396519386775 2957706992586594779080163)
              ·
                refine ⟨4436560488879892168620245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957706992586594779080163 4436560488879892168620245)
                ·
                  refine ⟨103981886458122472702037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4436560488879892168620245 103981886458122472702037)
                  ·
                    rfl

theorem cell21_455634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_455634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455634 prefixEnd_455634 := by exact prefixLift 455634
  have htrace : WordTrace (prefixWord ++ tailWord_455634) baseStart_455634 baseEnd_455634 := by
    simpa [prefixWord, tailWord_455634, baseEnd_455634] using wordTrace_append hprefix tailTrace_455634
  have hstable : (prefixWord ++ tailWord_455634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455634).length < 2 ^ (prefixWord ++ tailWord_455634).sum := by decide
  have hdescent : baseEnd_455634 < baseStart_455634 := by decide
  rcases family_descends (prefixWord ++ tailWord_455634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455651 : List Nat := [1, 1, 1, 6, 1, 1, 4, 3, 3]
def baseStart_455651 : Nat := 118140960795 + 455651 * 2 ^ 59
def prefixEnd_455651 : Nat := 4983230072969 + 3 ^ 40 * 455651 * 2
def baseEnd_455651 : Nat := 103985766089734220918669

theorem tailTrace_455651 : CollatzResearch.WordTrace tailWord_455651 prefixEnd_455651 103985766089734220918669 := by
  unfold tailWord_455651
  simp only [CollatzResearch.WordTrace]
  refine ⟨16618957272261720840422807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11079304848174480560281871 16618957272261720840422807)
  ·
    refine ⟨24928435908392581260634211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16618957272261720840422807 24928435908392581260634211)
    ·
      refine ⟨37392653862588871890951317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24928435908392581260634211 37392653862588871890951317)
      ·
        refine ⟨1752780649808853369888343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37392653862588871890951317 1752780649808853369888343)
        ·
          refine ⟨2629170974713280054832515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752780649808853369888343 2629170974713280054832515)
          ·
            refine ⟨3943756462069920082248773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629170974713280054832515 3943756462069920082248773)
            ·
              refine ⟨739454336638110015421645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3943756462069920082248773 739454336638110015421645)
              ·
                refine ⟨277295376239291255783117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739454336638110015421645 277295376239291255783117)
                ·
                  refine ⟨103985766089734220918669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277295376239291255783117 103985766089734220918669)
                  ·
                    rfl

theorem cell21_455651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 3].length) (baseStart_455651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455651 prefixEnd_455651 := by exact prefixLift 455651
  have htrace : WordTrace (prefixWord ++ tailWord_455651) baseStart_455651 baseEnd_455651 := by
    simpa [prefixWord, tailWord_455651, baseEnd_455651] using wordTrace_append hprefix tailTrace_455651
  have hstable : (prefixWord ++ tailWord_455651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455651).length < 2 ^ (prefixWord ++ tailWord_455651).sum := by decide
  have hdescent : baseEnd_455651 < baseStart_455651 := by decide
  rcases family_descends (prefixWord ++ tailWord_455651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455665 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 4]
def baseStart_455665 : Nat := 118140960795 + 455665 * 2 ^ 59
def prefixEnd_455665 : Nat := 4983230072969 + 3 ^ 40 * 455665 * 2
def baseEnd_455665 : Nat := 103988961080473307685307

theorem tailTrace_455665 : CollatzResearch.WordTrace tailWord_455665 prefixEnd_455665 103988961080473307685307 := by
  unfold tailWord_455665
  simp only [CollatzResearch.WordTrace]
  refine ⟨16619467894211001231432449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11079645262807334154288299 16619467894211001231432449)
  ·
    refine ⟨12464600920658250923574337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16619467894211001231432449 12464600920658250923574337)
    ·
      refine ⟨9348450690493688192680753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12464600920658250923574337 9348450690493688192680753)
      ·
        refine ⟨7011338017870266144510565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9348450690493688192680753 7011338017870266144510565)
        ·
          refine ⟨1314625878350674902095731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7011338017870266144510565 1314625878350674902095731)
          ·
            refine ⟨1971938817526012353143597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314625878350674902095731 1971938817526012353143597)
            ·
              refine ⟨739477056572254632428849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1971938817526012353143597 739477056572254632428849)
              ·
                refine ⟨554607792429190974321637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739477056572254632428849 554607792429190974321637)
                ·
                  refine ⟨103988961080473307685307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554607792429190974321637 103988961080473307685307)
                  ·
                    rfl

theorem cell21_455665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_455665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455665 prefixEnd_455665 := by exact prefixLift 455665
  have htrace : WordTrace (prefixWord ++ tailWord_455665) baseStart_455665 baseEnd_455665 := by
    simpa [prefixWord, tailWord_455665, baseEnd_455665] using wordTrace_append hprefix tailTrace_455665
  have hstable : (prefixWord ++ tailWord_455665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455665).length < 2 ^ (prefixWord ++ tailWord_455665).sum := by decide
  have hdescent : baseEnd_455665 < baseStart_455665 := by decide
  rcases family_descends (prefixWord ++ tailWord_455665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455724 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_455724 : Nat := 118140960795 + 455724 * 2 ^ 59
def prefixEnd_455724 : Nat := 4983230072969 + 3 ^ 40 * 455724 * 2
def baseEnd_455724 : Nat := 104002425684302316201853

theorem tailTrace_455724 : CollatzResearch.WordTrace tailWord_455724 prefixEnd_455724 104002425684302316201853 := by
  unfold tailWord_455724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8310809900498627153915113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11081079867331502871886817 8310809900498627153915113)
  ·
    refine ⟨6233107425373970365436335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8310809900498627153915113 6233107425373970365436335)
    ·
      refine ⟨9349661138060955548154503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6233107425373970365436335 9349661138060955548154503)
      ·
        refine ⟨14024491707091433322231755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9349661138060955548154503 14024491707091433322231755)
        ·
          refine ⟨21036737560637149983347633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14024491707091433322231755 21036737560637149983347633)
          ·
            refine ⟨15777553170477862487510725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21036737560637149983347633 15777553170477862487510725)
            ·
              refine ⟨2958291219464599216408261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15777553170477862487510725 2958291219464599216408261)
              ·
                refine ⟨554679603649612353076549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2958291219464599216408261 554679603649612353076549)
                ·
                  refine ⟨104002425684302316201853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554679603649612353076549 104002425684302316201853)
                  ·
                    rfl

theorem cell21_455724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_455724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455724 prefixEnd_455724 := by exact prefixLift 455724
  have htrace : WordTrace (prefixWord ++ tailWord_455724) baseStart_455724 baseEnd_455724 := by
    simpa [prefixWord, tailWord_455724, baseEnd_455724] using wordTrace_append hprefix tailTrace_455724
  have hstable : (prefixWord ++ tailWord_455724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455724).length < 2 ^ (prefixWord ++ tailWord_455724).sum := by decide
  have hdescent : baseEnd_455724 < baseStart_455724 := by decide
  rcases family_descends (prefixWord ++ tailWord_455724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455738 : List Nat := [3, 1, 1, 1, 3, 1, 3, 8]
def baseStart_455738 : Nat := 118140960795 + 455738 * 2 ^ 59
def prefixEnd_455738 : Nat := 4983230072969 + 3 ^ 40 * 455738 * 2
def baseEnd_455738 : Nat := 34668540225013800989497

theorem tailTrace_455738 : CollatzResearch.WordTrace tailWord_455738 prefixEnd_455738 34668540225013800989497 := by
  unfold tailWord_455738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155532605736633674709967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11081420281964356465893245 4155532605736633674709967)
  ·
    refine ⟨6233298908604950512064951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4155532605736633674709967 6233298908604950512064951)
    ·
      refine ⟨9349948362907425768097427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6233298908604950512064951 9349948362907425768097427)
      ·
        refine ⟨14024922544361138652146141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9349948362907425768097427 14024922544361138652146141)
        ·
          refine ⟨5259345954135426994554803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14024922544361138652146141 5259345954135426994554803)
          ·
            refine ⟨7889018931203140491832205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259345954135426994554803 7889018931203140491832205)
            ·
              refine ⟨2958382099201177684437077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7889018931203140491832205 2958382099201177684437077)
              ·
                refine ⟨34668540225013800989497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2958382099201177684437077 34668540225013800989497)
                ·
                  rfl

theorem cell21_455738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_455738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455738 prefixEnd_455738 := by exact prefixLift 455738
  have htrace : WordTrace (prefixWord ++ tailWord_455738) baseStart_455738 baseEnd_455738 := by
    simpa [prefixWord, tailWord_455738, baseEnd_455738] using wordTrace_append hprefix tailTrace_455738
  have hstable : (prefixWord ++ tailWord_455738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455738).length < 2 ^ (prefixWord ++ tailWord_455738).sum := by decide
  have hdescent : baseEnd_455738 < baseStart_455738 := by decide
  rcases family_descends (prefixWord ++ tailWord_455738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455741 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 4]
def baseStart_455741 : Nat := 118140960795 + 455741 * 2 ^ 59
def prefixEnd_455741 : Nat := 4983230072969 + 3 ^ 40 * 455741 * 2
def baseEnd_455741 : Nat := 104006305315914064418485

theorem tailTrace_455741 : CollatzResearch.WordTrace tailWord_455741 prefixEnd_455741 104006305315914064418485 := by
  unfold tailWord_455741
  simp only [CollatzResearch.WordTrace]
  refine ⟨16622239841935666211199077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11081493227957110807466051 16622239841935666211199077)
  ·
    refine ⟨3116669970362937414599827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16622239841935666211199077 3116669970362937414599827)
    ·
      refine ⟨4675004955544406121899741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3116669970362937414599827 4675004955544406121899741)
      ·
        refine ⟨1753126858329152295712403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4675004955544406121899741 1753126858329152295712403)
        ·
          refine ⟨2629690287493728443568605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753126858329152295712403 2629690287493728443568605)
          ·
            refine ⟨986133857810148166338227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2629690287493728443568605 986133857810148166338227)
            ·
              refine ⟨1479200786715222249507341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986133857810148166338227 1479200786715222249507341)
              ·
                refine ⟨554700295018208343565253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479200786715222249507341 554700295018208343565253)
                ·
                  refine ⟨104006305315914064418485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554700295018208343565253 104006305315914064418485)
                  ·
                    rfl

theorem cell21_455741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_455741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455741 prefixEnd_455741 := by exact prefixLift 455741
  have htrace : WordTrace (prefixWord ++ tailWord_455741) baseStart_455741 baseEnd_455741 := by
    simpa [prefixWord, tailWord_455741, baseEnd_455741] using wordTrace_append hprefix tailTrace_455741
  have hstable : (prefixWord ++ tailWord_455741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455741).length < 2 ^ (prefixWord ++ tailWord_455741).sum := by decide
  have hdescent : baseEnd_455741 < baseStart_455741 := by decide
  rcases family_descends (prefixWord ++ tailWord_455741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455800 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_455800 : Nat := 118140960795 + 455800 * 2 ^ 59
def prefixEnd_455800 : Nat := 4983230072969 + 3 ^ 40 * 455800 * 2
def baseEnd_455800 : Nat := 104019769919743072935031

theorem tailTrace_455800 : CollatzResearch.WordTrace tailWord_455800 prefixEnd_455800 104019769919743072935031 := by
  unfold tailWord_455800
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312195874360959643798427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11082927832481279525064569 8312195874360959643798427)
  ·
    refine ⟨12468293811541439465697641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312195874360959643798427 12468293811541439465697641)
    ·
      refine ⟨9351220358656079599273231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12468293811541439465697641 9351220358656079599273231)
      ·
        refine ⟨14026830537984119398909847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9351220358656079599273231 14026830537984119398909847)
        ·
          refine ⟨21040245806976179098364771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14026830537984119398909847 21040245806976179098364771)
          ·
            refine ⟨31560368710464268647547157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21040245806976179098364771 31560368710464268647547157)
            ·
              refine ⟨1479392283303012592853773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31560368710464268647547157 1479392283303012592853773)
              ·
                refine ⟨554772106238629722320165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479392283303012592853773 554772106238629722320165)
                ·
                  refine ⟨104019769919743072935031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554772106238629722320165 104019769919743072935031)
                  ·
                    rfl

theorem cell21_455800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_455800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455800 prefixEnd_455800 := by exact prefixLift 455800
  have htrace : WordTrace (prefixWord ++ tailWord_455800) baseStart_455800 baseEnd_455800 := by
    simpa [prefixWord, tailWord_455800, baseEnd_455800] using wordTrace_append hprefix tailTrace_455800
  have hstable : (prefixWord ++ tailWord_455800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455800).length < 2 ^ (prefixWord ++ tailWord_455800).sum := by decide
  have hdescent : baseEnd_455800 < baseStart_455800 := by decide
  rcases family_descends (prefixWord ++ tailWord_455800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455834 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_455834 : Nat := 118140960795 + 455834 * 2 ^ 59
def prefixEnd_455834 : Nat := 4983230072969 + 3 ^ 40 * 455834 * 2
def baseEnd_455834 : Nat := 104027529182966569368295

theorem tailTrace_455834 : CollatzResearch.WordTrace tailWord_455834 prefixEnd_455834 104027529182966569368295 := by
  unfold tailWord_455834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156407957649685773583639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11083754553732495396223037 4156407957649685773583639)
  ·
    refine ⟨6234611936474528660375459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4156407957649685773583639 6234611936474528660375459)
    ·
      refine ⟨9351917904711792990563189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6234611936474528660375459 9351917904711792990563189)
      ·
        refine ⟨876742303566730592865299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9351917904711792990563189 876742303566730592865299)
        ·
          refine ⟨1315113455350095889297949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876742303566730592865299 1315113455350095889297949)
          ·
            refine ⟨493167545756285958486731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1315113455350095889297949 493167545756285958486731)
            ·
              refine ⟨739751318634428937730097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493167545756285958486731 739751318634428937730097)
              ·
                refine ⟨554813488975821703297573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739751318634428937730097 554813488975821703297573)
                ·
                  refine ⟨104027529182966569368295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554813488975821703297573 104027529182966569368295)
                  ·
                    rfl

theorem cell21_455834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_455834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455834 prefixEnd_455834 := by exact prefixLift 455834
  have htrace : WordTrace (prefixWord ++ tailWord_455834) baseStart_455834 baseEnd_455834 := by
    simpa [prefixWord, tailWord_455834, baseEnd_455834] using wordTrace_append hprefix tailTrace_455834
  have hstable : (prefixWord ++ tailWord_455834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455834).length < 2 ^ (prefixWord ++ tailWord_455834).sum := by decide
  have hdescent : baseEnd_455834 < baseStart_455834 := by decide
  rcases family_descends (prefixWord ++ tailWord_455834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455845 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 5]
def baseStart_455845 : Nat := 118140960795 + 455845 * 2 ^ 59
def prefixEnd_455845 : Nat := 4983230072969 + 3 ^ 40 * 455845 * 2
def baseEnd_455845 : Nat := 104030039532832994684939

theorem tailTrace_455845 : CollatzResearch.WordTrace tailWord_455845 prefixEnd_455845 104030039532832994684939 := by
  unfold tailWord_455845
  simp only [CollatzResearch.WordTrace]
  refine ⟨16626033033558891972984989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11084022022372594648656659 16626033033558891972984989)
  ·
    refine ⟨6234762387584584489869371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16626033033558891972984989 6234762387584584489869371)
    ·
      refine ⟨9352143581376876734804057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6234762387584584489869371 9352143581376876734804057)
      ·
        refine ⟨7014107686032657551103043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9352143581376876734804057 7014107686032657551103043)
        ·
          refine ⟨10521161529048986326654565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014107686032657551103043 10521161529048986326654565)
          ·
            refine ⟨1972717786696684936247731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10521161529048986326654565 1972717786696684936247731)
            ·
              refine ⟨2959076680045027404371597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972717786696684936247731 2959076680045027404371597)
              ·
                refine ⟨1109653755016885276639349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2959076680045027404371597 1109653755016885276639349)
                ·
                  refine ⟨104030039532832994684939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1109653755016885276639349 104030039532832994684939)
                  ·
                    rfl

theorem cell21_455845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_455845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455845 prefixEnd_455845 := by exact prefixLift 455845
  have htrace : WordTrace (prefixWord ++ tailWord_455845) baseStart_455845 baseEnd_455845 := by
    simpa [prefixWord, tailWord_455845, baseEnd_455845] using wordTrace_append hprefix tailTrace_455845
  have hstable : (prefixWord ++ tailWord_455845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455845).length < 2 ^ (prefixWord ++ tailWord_455845).sum := by decide
  have hdescent : baseEnd_455845 < baseStart_455845 := by decide
  rcases family_descends (prefixWord ++ tailWord_455845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455896 : List Nat := [2, 1, 2, 2, 5, 1, 3, 2, 3]
def baseStart_455896 : Nat := 118140960795 + 455896 * 2 ^ 59
def prefixEnd_455896 : Nat := 4983230072969 + 3 ^ 40 * 455896 * 2
def baseEnd_455896 : Nat := 104041678427668239334835

theorem tailTrace_455896 : CollatzResearch.WordTrace tailWord_455896 prefixEnd_455896 104041678427668239334835 := by
  unfold tailWord_455896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8313946578187063841545771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11085262104249418455394361 8313946578187063841545771)
  ·
    refine ⟨12470919867280595762318657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8313946578187063841545771 12470919867280595762318657)
    ·
      refine ⟨9353189900460446821738993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12470919867280595762318657 9353189900460446821738993)
      ·
        refine ⟨7014892425345335116304245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9353189900460446821738993 7014892425345335116304245)
        ·
          refine ⟨657646164876125167153523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7014892425345335116304245 657646164876125167153523)
          ·
            refine ⟨986469247314187750730285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657646164876125167153523 986469247314187750730285)
            ·
              refine ⟨369925967742820406523857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 986469247314187750730285 369925967742820406523857)
              ·
                refine ⟨277444475807115304892893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369925967742820406523857 277444475807115304892893)
                ·
                  refine ⟨104041678427668239334835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277444475807115304892893 104041678427668239334835)
                  ·
                    rfl

theorem cell21_455896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_455896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_455896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_455896 prefixEnd_455896 := by exact prefixLift 455896
  have htrace : WordTrace (prefixWord ++ tailWord_455896) baseStart_455896 baseEnd_455896 := by
    simpa [prefixWord, tailWord_455896, baseEnd_455896] using wordTrace_append hprefix tailTrace_455896
  have hstable : (prefixWord ++ tailWord_455896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455896).length < 2 ^ (prefixWord ++ tailWord_455896).sum := by decide
  have hdescent : baseEnd_455896 < baseStart_455896 := by decide
  rcases family_descends (prefixWord ++ tailWord_455896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456014 : List Nat := [4, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_456014 : Nat := 118140960795 + 456014 * 2 ^ 59
def prefixEnd_456014 : Nat := 4983230072969 + 3 ^ 40 * 456014 * 2
def baseEnd_456014 : Nat := 104068607635326256367927

theorem tailTrace_456014 : CollatzResearch.WordTrace tailWord_456014 prefixEnd_456014 104068607635326256367927 := by
  unfold tailWord_456014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079024621243329229485887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11088131313297755890591397 2079024621243329229485887)
  ·
    refine ⟨3118536931864993844228831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2079024621243329229485887 3118536931864993844228831)
    ·
      refine ⟨4677805397797490766343247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3118536931864993844228831 4677805397797490766343247)
      ·
        refine ⟨7016708096696236149514871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677805397797490766343247 7016708096696236149514871)
        ·
          refine ⟨10525062145044354224272307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7016708096696236149514871 10525062145044354224272307)
          ·
            refine ⟨15787593217566531336408461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10525062145044354224272307 15787593217566531336408461)
            ·
              refine ⟨5920347456587449251153173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15787593217566531336408461 5920347456587449251153173)
              ·
                refine ⟨277516287027536683647805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5920347456587449251153173 277516287027536683647805)
                ·
                  refine ⟨104068607635326256367927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277516287027536683647805 104068607635326256367927)
                  ·
                    rfl

theorem cell21_456014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_456014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456014 prefixEnd_456014 := by exact prefixLift 456014
  have htrace : WordTrace (prefixWord ++ tailWord_456014) baseStart_456014 baseEnd_456014 := by
    simpa [prefixWord, tailWord_456014, baseEnd_456014] using wordTrace_append hprefix tailTrace_456014
  have hstable : (prefixWord ++ tailWord_456014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456014).length < 2 ^ (prefixWord ++ tailWord_456014).sum := by decide
  have hdescent : baseEnd_456014 < baseStart_456014 := by decide
  rcases family_descends (prefixWord ++ tailWord_456014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456121 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 4]
def baseStart_456121 : Nat := 118140960795 + 456121 * 2 ^ 59
def prefixEnd_456121 : Nat := 4983230072969 + 3 ^ 40 * 456121 * 2
def baseEnd_456121 : Nat := 104093026493117848084375

theorem tailTrace_456121 : CollatzResearch.WordTrace tailWord_456121 prefixEnd_456121 104093026493117848084375 := by
  unfold tailWord_456121
  simp only [CollatzResearch.WordTrace]
  refine ⟨16636099580558991110032217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11090733053705994073354811 16636099580558991110032217)
  ·
    refine ⟨12477074685419243332524163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16636099580558991110032217 12477074685419243332524163)
    ·
      refine ⟨18715612028128864998786245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12477074685419243332524163 18715612028128864998786245)
      ·
        refine ⟨3509177255274162187272421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18715612028128864998786245 3509177255274162187272421)
        ·
          refine ⟨657970735363905410113579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3509177255274162187272421 657970735363905410113579)
          ·
            refine ⟨986956103045858115170369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657970735363905410113579 986956103045858115170369)
            ·
              refine ⟨740217077284393586377777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986956103045858115170369 740217077284393586377777)
              ·
                refine ⟨555162807963295189783333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740217077284393586377777 555162807963295189783333)
                ·
                  refine ⟨104093026493117848084375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555162807963295189783333 104093026493117848084375)
                  ·
                    rfl

theorem cell21_456121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_456121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456121 prefixEnd_456121 := by exact prefixLift 456121
  have htrace : WordTrace (prefixWord ++ tailWord_456121) baseStart_456121 baseEnd_456121 := by
    simpa [prefixWord, tailWord_456121, baseEnd_456121] using wordTrace_append hprefix tailTrace_456121
  have hstable : (prefixWord ++ tailWord_456121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456121).length < 2 ^ (prefixWord ++ tailWord_456121).sum := by decide
  have hdescent : baseEnd_456121 < baseStart_456121 := by decide
  rcases family_descends (prefixWord ++ tailWord_456121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456149 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 5]
def baseStart_456149 : Nat := 118140960795 + 456149 * 2 ^ 59
def prefixEnd_456149 : Nat := 4983230072969 + 3 ^ 40 * 456149 * 2
def baseEnd_456149 : Nat := 104099416474596021617651

theorem tailTrace_456149 : CollatzResearch.WordTrace tailWord_456149 prefixEnd_456149 104099416474596021617651 := by
  unfold tailWord_456149
  simp only [CollatzResearch.WordTrace]
  refine ⟨16637120824457551892051501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11091413882971701261367667 16637120824457551892051501)
  ·
    refine ⟨6238920309171581959519313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16637120824457551892051501 6238920309171581959519313)
    ·
      refine ⟨4679190231878686469639485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6238920309171581959519313 4679190231878686469639485)
      ·
        refine ⟨1754696336954507426114807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4679190231878686469639485 1754696336954507426114807)
        ·
          refine ⟨2632044505431761139172211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754696336954507426114807 2632044505431761139172211)
          ·
            refine ⟨3948066758147641708758317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632044505431761139172211 3948066758147641708758317)
            ·
              refine ⟨1480525034305365640784369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3948066758147641708758317 1480525034305365640784369)
              ·
                refine ⟨1110393775729024230588277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480525034305365640784369 1110393775729024230588277)
                ·
                  refine ⟨104099416474596021617651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1110393775729024230588277 104099416474596021617651)
                  ·
                    rfl

theorem cell21_456149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_456149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456149 prefixEnd_456149 := by exact prefixLift 456149
  have htrace : WordTrace (prefixWord ++ tailWord_456149) baseStart_456149 baseEnd_456149 := by
    simpa [prefixWord, tailWord_456149, baseEnd_456149] using wordTrace_append hprefix tailTrace_456149
  have hstable : (prefixWord ++ tailWord_456149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456149).length < 2 ^ (prefixWord ++ tailWord_456149).sum := by decide
  have hdescent : baseEnd_456149 < baseStart_456149 := by decide
  rcases family_descends (prefixWord ++ tailWord_456149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456211 : List Nat := [1, 1, 1, 2, 1, 8, 2, 5]
def baseStart_456211 : Nat := 118140960795 + 456211 * 2 ^ 59
def prefixEnd_456211 : Nat := 4983230072969 + 3 ^ 40 * 456211 * 2
def baseEnd_456211 : Nat := 34704521906432563861397

theorem tailTrace_456211 : CollatzResearch.WordTrace tailWord_456211 prefixEnd_456211 34704521906432563861397 := by
  unfold tailWord_456211
  simp only [CollatzResearch.WordTrace]
  refine ⟨16639382150232936480808487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11092921433488624320538991 16639382150232936480808487)
  ·
    refine ⟨24959073225349404721212731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16639382150232936480808487 24959073225349404721212731)
    ·
      refine ⟨37438609838024107081819097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24959073225349404721212731 37438609838024107081819097)
      ·
        refine ⟨28078957378518080311364323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37438609838024107081819097 28078957378518080311364323)
        ·
          refine ⟨42118436067777120467046485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28078957378518080311364323 42118436067777120467046485)
          ·
            refine ⟨493575422669263130473201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 42118436067777120467046485 493575422669263130473201)
            ·
              refine ⟨370181567001947347854901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493575422669263130473201 370181567001947347854901)
              ·
                refine ⟨34704521906432563861397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 370181567001947347854901 34704521906432563861397)
                ·
                  rfl

theorem cell21_456211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 5].length) (baseStart_456211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456211 prefixEnd_456211 := by exact prefixLift 456211
  have htrace : WordTrace (prefixWord ++ tailWord_456211) baseStart_456211 baseEnd_456211 := by
    simpa [prefixWord, tailWord_456211, baseEnd_456211] using wordTrace_append hprefix tailTrace_456211
  have hstable : (prefixWord ++ tailWord_456211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456211).length < 2 ^ (prefixWord ++ tailWord_456211).sum := by decide
  have hdescent : baseEnd_456211 < baseStart_456211 := by decide
  rcases family_descends (prefixWord ++ tailWord_456211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456315 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 4]
def baseStart_456315 : Nat := 118140960795 + 456315 * 2 ^ 59
def prefixEnd_456315 : Nat := 4983230072969 + 3 ^ 40 * 456315 * 2
def baseEnd_456315 : Nat := 104137299936216621850645

theorem tailTrace_456315 : CollatzResearch.WordTrace tailWord_456315 prefixEnd_456315 104137299936216621850645 := by
  unfold tailWord_456315
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643175341856162242594399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11095450227904108161729599 16643175341856162242594399)
  ·
    refine ⟨24964763012784243363891599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16643175341856162242594399 24964763012784243363891599)
    ·
      refine ⟨37447144519176365045837399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24964763012784243363891599 37447144519176365045837399)
      ·
        refine ⟨56170716778764547568756099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37447144519176365045837399 56170716778764547568756099)
        ·
          refine ⟨84256075168146821353134149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56170716778764547568756099 84256075168146821353134149)
          ·
            refine ⟨15798014094027529003712653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84256075168146821353134149 15798014094027529003712653)
            ·
              refine ⟨5924255285260323376392245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15798014094027529003712653 5924255285260323376392245)
              ·
                refine ⟨555398932993155316536773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5924255285260323376392245 555398932993155316536773)
                ·
                  refine ⟨104137299936216621850645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555398932993155316536773 104137299936216621850645)
                  ·
                    rfl

theorem cell21_456315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 4].length) (baseStart_456315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456315 prefixEnd_456315 := by exact prefixLift 456315
  have htrace : WordTrace (prefixWord ++ tailWord_456315) baseStart_456315 baseEnd_456315 := by
    simpa [prefixWord, tailWord_456315, baseEnd_456315] using wordTrace_append hprefix tailTrace_456315
  have hstable : (prefixWord ++ tailWord_456315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456315).length < 2 ^ (prefixWord ++ tailWord_456315).sum := by decide
  have hdescent : baseEnd_456315 < baseStart_456315 := by decide
  rcases family_descends (prefixWord ++ tailWord_456315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456329 : List Nat := [1, 2, 1, 1, 4, 1, 2, 9]
def baseStart_456329 : Nat := 118140960795 + 456329 * 2 ^ 59
def prefixEnd_456329 : Nat := 4983230072969 + 3 ^ 40 * 456329 * 2
def baseEnd_456329 : Nat := 34713498308985236205761

theorem tailTrace_456329 : CollatzResearch.WordTrace tailWord_456329 prefixEnd_456329 34713498308985236205761 := by
  unfold tailWord_456329
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643685963805442633604041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11095790642536961755736027 16643685963805442633604041)
  ·
    refine ⟨12482764472854081975203031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16643685963805442633604041 12482764472854081975203031)
    ·
      refine ⟨18724146709281122962804547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12482764472854081975203031 18724146709281122962804547)
      ·
        refine ⟨28086220063921684444206821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18724146709281122962804547 28086220063921684444206821)
        ·
          refine ⟨5266166261985315833288779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28086220063921684444206821 5266166261985315833288779)
          ·
            refine ⟨7899249392977973749933169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266166261985315833288779 7899249392977973749933169)
            ·
              refine ⟨5924437044733480312449877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7899249392977973749933169 5924437044733480312449877)
              ·
                refine ⟨34713498308985236205761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5924437044733480312449877 34713498308985236205761)
                ·
                  rfl

theorem cell21_456329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 9].length) (baseStart_456329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456329 prefixEnd_456329 := by exact prefixLift 456329
  have htrace : WordTrace (prefixWord ++ tailWord_456329) baseStart_456329 baseEnd_456329 := by
    simpa [prefixWord, tailWord_456329, baseEnd_456329] using wordTrace_append hprefix tailTrace_456329
  have hstable : (prefixWord ++ tailWord_456329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456329).length < 2 ^ (prefixWord ++ tailWord_456329).sum := by decide
  have hdescent : baseEnd_456329 < baseStart_456329 := by decide
  rcases family_descends (prefixWord ++ tailWord_456329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456386 : List Nat := [3, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_456386 : Nat := 118140960795 + 456386 * 2 ^ 59
def prefixEnd_456386 : Nat := 4983230072969 + 3 ^ 40 * 456386 * 2
def baseEnd_456386 : Nat := 104153503103536276167167

theorem tailTrace_456386 : CollatzResearch.WordTrace tailWord_456386 prefixEnd_456386 104153503103536276167167 := by
  unfold tailWord_456386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161441231149735342107253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11097176616399294245619341 4161441231149735342107253)
  ·
    refine ⟨390135115420287688322555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4161441231149735342107253 390135115420287688322555)
    ·
      refine ⟨585202673130431532483833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390135115420287688322555 585202673130431532483833)
      ·
        refine ⟨438902004847823649362875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585202673130431532483833 438902004847823649362875)
        ·
          refine ⟨658353007271735474044313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438902004847823649362875 658353007271735474044313)
          ·
            refine ⟨493764755453801605533235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658353007271735474044313 493764755453801605533235)
            ·
              refine ⟨740647133180702408299853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493764755453801605533235 740647133180702408299853)
              ·
                refine ⟨277742674942763403112445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 740647133180702408299853 277742674942763403112445)
                ·
                  refine ⟨104153503103536276167167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277742674942763403112445 104153503103536276167167)
                  ·
                    rfl

theorem cell21_456386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_456386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456386 prefixEnd_456386 := by exact prefixLift 456386
  have htrace : WordTrace (prefixWord ++ tailWord_456386) baseStart_456386 baseEnd_456386 := by
    simpa [prefixWord, tailWord_456386, baseEnd_456386] using wordTrace_append hprefix tailTrace_456386
  have hstable : (prefixWord ++ tailWord_456386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456386).length < 2 ^ (prefixWord ++ tailWord_456386).sum := by decide
  have hdescent : baseEnd_456386 < baseStart_456386 := by decide
  rcases family_descends (prefixWord ++ tailWord_456386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456484 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_456484 : Nat := 118140960795 + 456484 * 2 ^ 59
def prefixEnd_456484 : Nat := 4983230072969 + 3 ^ 40 * 456484 * 2
def baseEnd_456484 : Nat := 104175868038709883533633

theorem tailTrace_456484 : CollatzResearch.WordTrace tailWord_456484 prefixEnd_456484 104175868038709883533633 := by
  unfold tailWord_456484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8324669639121952052748253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11099559518829269403664337 8324669639121952052748253)
  ·
    refine ⟨3121751114670732019780595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8324669639121952052748253 3121751114670732019780595)
    ·
      refine ⟨4682626672006098029670893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3121751114670732019780595 4682626672006098029670893)
      ·
        refine ⟨1755985002002286761126585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4682626672006098029670893 1755985002002286761126585)
        ·
          refine ⟨1316988751501715070844939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1755985002002286761126585 1316988751501715070844939)
          ·
            refine ⟨1975483127252572606267409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316988751501715070844939 1975483127252572606267409)
            ·
              refine ⟨1481612345439429454700557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975483127252572606267409 1481612345439429454700557)
              ·
                refine ⟨555604629539786045512709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1481612345439429454700557 555604629539786045512709)
                ·
                  refine ⟨104175868038709883533633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555604629539786045512709 104175868038709883533633)
                  ·
                    rfl

theorem cell21_456484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_456484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456484 prefixEnd_456484 := by exact prefixLift 456484
  have htrace : WordTrace (prefixWord ++ tailWord_456484) baseStart_456484 baseEnd_456484 := by
    simpa [prefixWord, tailWord_456484, baseEnd_456484] using wordTrace_append hprefix tailTrace_456484
  have hstable : (prefixWord ++ tailWord_456484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456484).length < 2 ^ (prefixWord ++ tailWord_456484).sum := by decide
  have hdescent : baseEnd_456484 < baseStart_456484 := by decide
  rcases family_descends (prefixWord ++ tailWord_456484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456518 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_456518 : Nat := 118140960795 + 456518 * 2 ^ 59
def prefixEnd_456518 : Nat := 4983230072969 + 3 ^ 40 * 456518 * 2
def baseEnd_456518 : Nat := 104183627301933379966897

theorem tailTrace_456518 : CollatzResearch.WordTrace tailWord_456518 prefixEnd_456518 104183627301933379966897 := by
  unfold tailWord_456518
  simp only [CollatzResearch.WordTrace]
  refine ⟨520330605003772747257319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11100386240080485274822805 520330605003772747257319)
  ·
    refine ⟨780495907505659120885979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 520330605003772747257319 780495907505659120885979)
    ·
      refine ⟨1170743861258488681328969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780495907505659120885979 1170743861258488681328969)
      ·
        refine ⟨878057895943866510996727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170743861258488681328969 878057895943866510996727)
        ·
          refine ⟨1317086843915799766495091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878057895943866510996727 1317086843915799766495091)
          ·
            refine ⟨1975630265873699649742637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317086843915799766495091 1975630265873699649742637)
            ·
              refine ⟨740861349702637368653489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1975630265873699649742637 740861349702637368653489)
              ·
                refine ⟨555646012276978026490117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740861349702637368653489 555646012276978026490117)
                ·
                  refine ⟨104183627301933379966897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555646012276978026490117 104183627301933379966897)
                  ·
                    rfl

theorem cell21_456518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_456518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456518 prefixEnd_456518 := by exact prefixLift 456518
  have htrace : WordTrace (prefixWord ++ tailWord_456518) baseStart_456518 baseEnd_456518 := by
    simpa [prefixWord, tailWord_456518, baseEnd_456518] using wordTrace_append hprefix tailTrace_456518
  have hstable : (prefixWord ++ tailWord_456518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456518).length < 2 ^ (prefixWord ++ tailWord_456518).sum := by decide
  have hdescent : baseEnd_456518 < baseStart_456518 := by decide
  rcases family_descends (prefixWord ++ tailWord_456518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456529 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 5]
def baseStart_456529 : Nat := 118140960795 + 456529 * 2 ^ 59
def prefixEnd_456529 : Nat := 4983230072969 + 3 ^ 40 * 456529 * 2
def baseEnd_456529 : Nat := 104186137651799805283541

theorem tailTrace_456529 : CollatzResearch.WordTrace tailWord_456529 prefixEnd_456529 104186137651799805283541 := by
  unfold tailWord_456529
  simp only [CollatzResearch.WordTrace]
  refine ⟨16650980563080876790884641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11100653708720584527256427 16650980563080876790884641)
  ·
    refine ⟨12488235422310657593163481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16650980563080876790884641 12488235422310657593163481)
    ·
      refine ⟨9366176566732993194872611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12488235422310657593163481 9366176566732993194872611)
      ·
        refine ⟨14049264850099489792308917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9366176566732993194872611 14049264850099489792308917)
        ·
          refine ⟨1317118579696827168028961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14049264850099489792308917 1317118579696827168028961)
          ·
            refine ⟨987838934772620376021721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317118579696827168028961 987838934772620376021721)
            ·
              refine ⟨740879201079465282016291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987838934772620376021721 740879201079465282016291)
              ·
                refine ⟨1111318801619197923024437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740879201079465282016291 1111318801619197923024437)
                ·
                  refine ⟨104186137651799805283541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1111318801619197923024437 104186137651799805283541)
                  ·
                    rfl

theorem cell21_456529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_456529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456529 prefixEnd_456529 := by exact prefixLift 456529
  have htrace : WordTrace (prefixWord ++ tailWord_456529) baseStart_456529 baseEnd_456529 := by
    simpa [prefixWord, tailWord_456529, baseEnd_456529] using wordTrace_append hprefix tailTrace_456529
  have hstable : (prefixWord ++ tailWord_456529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456529).length < 2 ^ (prefixWord ++ tailWord_456529).sum := by decide
  have hdescent : baseEnd_456529 < baseStart_456529 := by decide
  rcases family_descends (prefixWord ++ tailWord_456529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456594 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_456594 : Nat := 118140960795 + 456594 * 2 ^ 59
def prefixEnd_456594 : Nat := 4983230072969 + 3 ^ 40 * 456594 * 2
def baseEnd_456594 : Nat := 104200971537374136700075

theorem tailTrace_456594 : CollatzResearch.WordTrace tailWord_456594 prefixEnd_456594 104200971537374136700075 := by
  unfold tailWord_456594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4163337826961348223000209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11102234205230261928000557 4163337826961348223000209)
  ·
    refine ⟨3122503370221011167250157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4163337826961348223000209 3122503370221011167250157)
    ·
      refine ⟨1170938763832879187718809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3122503370221011167250157 1170938763832879187718809)
      ·
        refine ⟨878204072874659390789107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170938763832879187718809 878204072874659390789107)
        ·
          refine ⟨1317306109311989086183661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878204072874659390789107 1317306109311989086183661)
          ·
            refine ⟨493989790991995907318873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1317306109311989086183661 493989790991995907318873)
            ·
              refine ⟨370492343243996930489155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493989790991995907318873 370492343243996930489155)
              ·
                refine ⟨555738514865995395733733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370492343243996930489155 555738514865995395733733)
                ·
                  refine ⟨104200971537374136700075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555738514865995395733733 104200971537374136700075)
                  ·
                    rfl

theorem cell21_456594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_456594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456594 prefixEnd_456594 := by exact prefixLift 456594
  have htrace : WordTrace (prefixWord ++ tailWord_456594) baseStart_456594 baseEnd_456594 := by
    simpa [prefixWord, tailWord_456594, baseEnd_456594] using wordTrace_append hprefix tailTrace_456594
  have hstable : (prefixWord ++ tailWord_456594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456594).length < 2 ^ (prefixWord ++ tailWord_456594).sum := by decide
  have hdescent : baseEnd_456594 < baseStart_456594 := by decide
  rcases family_descends (prefixWord ++ tailWord_456594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456664 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_456664 : Nat := 118140960795 + 456664 * 2 ^ 59
def prefixEnd_456664 : Nat := 4983230072969 + 3 ^ 40 * 456664 * 2
def baseEnd_456664 : Nat := 104216946491069570533265

theorem tailTrace_456664 : CollatzResearch.WordTrace tailWord_456664 prefixEnd_456664 104216946491069570533265 := by
  unfold tailWord_456664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327952208795897423524523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11103936278394529898032697 8327952208795897423524523)
  ·
    refine ⟨12491928313193846135286785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8327952208795897423524523 12491928313193846135286785)
    ·
      refine ⟨9368946234895384601465089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12491928313193846135286785 9368946234895384601465089)
      ·
        refine ⟨7026709676171538451098817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9368946234895384601465089 7026709676171538451098817)
        ·
          refine ⟨5270032257128653838324113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7026709676171538451098817 5270032257128653838324113)
          ·
            refine ⟨3952524192846490378743085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5270032257128653838324113 3952524192846490378743085)
            ·
              refine ⟨1482196572317433892028657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3952524192846490378743085 1482196572317433892028657)
              ·
                refine ⟨1111647429238075419021493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482196572317433892028657 1111647429238075419021493)
                ·
                  refine ⟨104216946491069570533265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1111647429238075419021493 104216946491069570533265)
                  ·
                    rfl

theorem cell21_456664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_456664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456664 prefixEnd_456664 := by exact prefixLift 456664
  have htrace : WordTrace (prefixWord ++ tailWord_456664) baseStart_456664 baseEnd_456664 := by
    simpa [prefixWord, tailWord_456664, baseEnd_456664] using wordTrace_append hprefix tailTrace_456664
  have hstable : (prefixWord ++ tailWord_456664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456664).length < 2 ^ (prefixWord ++ tailWord_456664).sum := by decide
  have hdescent : baseEnd_456664 < baseStart_456664 := by decide
  rcases family_descends (prefixWord ++ tailWord_456664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456712 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_456712 : Nat := 118140960795 + 456712 * 2 ^ 59
def prefixEnd_456712 : Nat := 4983230072969 + 3 ^ 40 * 456712 * 2
def baseEnd_456712 : Nat := 104227900745032153733167

theorem tailTrace_456712 : CollatzResearch.WordTrace tailWord_456712 prefixEnd_456712 104227900745032153733167 := by
  unfold tailWord_456712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328827560708949522398195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11105103414278599363197593 8328827560708949522398195)
  ·
    refine ⟨12493241341063424283597293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8328827560708949522398195 12493241341063424283597293)
    ·
      refine ⟨4684965502898784106348985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12493241341063424283597293 4684965502898784106348985)
      ·
        refine ⟨3513724127174088079761739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4684965502898784106348985 3513724127174088079761739)
        ·
          refine ⟨5270586190761132119642609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513724127174088079761739 5270586190761132119642609)
          ·
            refine ⟨3952939643070849089731957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5270586190761132119642609 3952939643070849089731957)
            ·
              refine ⟨370588091537892102162371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3952939643070849089731957 370588091537892102162371)
              ·
                refine ⟨555882137306838153243557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370588091537892102162371 555882137306838153243557)
                ·
                  refine ⟨104227900745032153733167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555882137306838153243557 104227900745032153733167)
                  ·
                    rfl

theorem cell21_456712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_456712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456712 prefixEnd_456712 := by exact prefixLift 456712
  have htrace : WordTrace (prefixWord ++ tailWord_456712) baseStart_456712 baseEnd_456712 := by
    simpa [prefixWord, tailWord_456712, baseEnd_456712] using wordTrace_append hprefix tailTrace_456712
  have hstable : (prefixWord ++ tailWord_456712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456712).length < 2 ^ (prefixWord ++ tailWord_456712).sum := by decide
  have hdescent : baseEnd_456712 < baseStart_456712 := by decide
  rcases family_descends (prefixWord ++ tailWord_456712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456743 : List Nat := [1, 1, 7, 1, 2, 2, 7]
def baseStart_456743 : Nat := 118140960795 + 456743 * 2 ^ 59
def prefixEnd_456743 : Nat := 4983230072969 + 3 ^ 40 * 456743 * 2
def baseEnd_456743 : Nat := 11581663929709220968493

theorem tailTrace_456743 : CollatzResearch.WordTrace tailWord_456743 prefixEnd_456743 11581663929709220968493 := by
  unfold tailWord_456743
  simp only [CollatzResearch.WordTrace]
  refine ⟨16658785784305591339174883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11105857189537060892783255 16658785784305591339174883)
  ·
    refine ⟨24988178676458387008762325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16658785784305591339174883 24988178676458387008762325)
    ·
      refine ⟨585660437729493445517867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24988178676458387008762325 585660437729493445517867)
      ·
        refine ⟨878490656594240168276801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585660437729493445517867 878490656594240168276801)
        ·
          refine ⟨658867992445680126207601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878490656594240168276801 658867992445680126207601)
          ·
            refine ⟨494150994334260094655701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658867992445680126207601 494150994334260094655701)
            ·
              refine ⟨11581663929709220968493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 494150994334260094655701 11581663929709220968493)
              ·
                rfl

theorem cell21_456743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 7].length) (baseStart_456743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456743 prefixEnd_456743 := by exact prefixLift 456743
  have htrace : WordTrace (prefixWord ++ tailWord_456743) baseStart_456743 baseEnd_456743 := by
    simpa [prefixWord, tailWord_456743, baseEnd_456743] using wordTrace_append hprefix tailTrace_456743
  have hstable : (prefixWord ++ tailWord_456743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456743).length < 2 ^ (prefixWord ++ tailWord_456743).sum := by decide
  have hdescent : baseEnd_456743 < baseStart_456743 := by decide
  rcases family_descends (prefixWord ++ tailWord_456743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456757 : List Nat := [1, 3, 3, 1, 1, 1, 2, 6, 3]
def baseStart_456757 : Nat := 118140960795 + 456757 * 2 ^ 59
def prefixEnd_456757 : Nat := 4983230072969 + 3 ^ 40 * 456757 * 2
def baseEnd_456757 : Nat := 104238170358122075483075

theorem tailTrace_456757 : CollatzResearch.WordTrace tailWord_456757 prefixEnd_456757 104238170358122075483075 := by
  unfold tailWord_456757
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659296406254871730184525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11106197604169914486789683 16659296406254871730184525)
  ·
    refine ⟨6247236152345576898819197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16659296406254871730184525 6247236152345576898819197)
    ·
      refine ⟨2342713557129591337057199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6247236152345576898819197 2342713557129591337057199)
      ·
        refine ⟨3514070335694387005585799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342713557129591337057199 3514070335694387005585799)
        ·
          refine ⟨5271105503541580508378699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3514070335694387005585799 5271105503541580508378699)
          ·
            refine ⟨7906658255312370762568049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271105503541580508378699 7906658255312370762568049)
            ·
              refine ⟨5929993691484278071926037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7906658255312370762568049 5929993691484278071926037)
              ·
                refine ⟨277968454288325534621533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5929993691484278071926037 277968454288325534621533)
                ·
                  refine ⟨104238170358122075483075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277968454288325534621533 104238170358122075483075)
                  ·
                    rfl

theorem cell21_456757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_456757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456757 prefixEnd_456757 := by exact prefixLift 456757
  have htrace : WordTrace (prefixWord ++ tailWord_456757) baseStart_456757 baseEnd_456757 := by
    simpa [prefixWord, tailWord_456757, baseEnd_456757] using wordTrace_append hprefix tailTrace_456757
  have hstable : (prefixWord ++ tailWord_456757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456757).length < 2 ^ (prefixWord ++ tailWord_456757).sum := by decide
  have hdescent : baseEnd_456757 < baseStart_456757 := by decide
  rcases family_descends (prefixWord ++ tailWord_456757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456799 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 9]
def baseStart_456799 : Nat := 118140960795 + 456799 * 2 ^ 59
def prefixEnd_456799 : Nat := 4983230072969 + 3 ^ 40 * 456799 * 2
def baseEnd_456799 : Nat := 104247755330339335782989

theorem tailTrace_456799 : CollatzResearch.WordTrace tailWord_456799 prefixEnd_456799 104247755330339335782989 := by
  unfold tailWord_456799
  simp only [CollatzResearch.WordTrace]
  refine ⟨16660828272102712903213451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11107218848068475268808967 16660828272102712903213451)
  ·
    refine ⟨24991242408154069354820177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16660828272102712903213451 24991242408154069354820177)
    ·
      refine ⟨18743431806115552016115133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24991242408154069354820177 18743431806115552016115133)
      ·
        refine ⟨7028786927293332006043175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18743431806115552016115133 7028786927293332006043175)
        ·
          refine ⟨10543180390939998009064763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7028786927293332006043175 10543180390939998009064763)
          ·
            refine ⟨15814770586409997013597145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10543180390939998009064763 15814770586409997013597145)
            ·
              refine ⟨11861077939807497760197859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15814770586409997013597145 11861077939807497760197859)
              ·
                refine ⟨17791616909711246640296789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11861077939807497760197859 17791616909711246640296789)
                ·
                  refine ⟨104247755330339335782989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17791616909711246640296789 104247755330339335782989)
                  ·
                    rfl

theorem cell21_456799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_456799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456799 prefixEnd_456799 := by exact prefixLift 456799
  have htrace : WordTrace (prefixWord ++ tailWord_456799) baseStart_456799 baseEnd_456799 := by
    simpa [prefixWord, tailWord_456799, baseEnd_456799] using wordTrace_append hprefix tailTrace_456799
  have hstable : (prefixWord ++ tailWord_456799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456799).length < 2 ^ (prefixWord ++ tailWord_456799).sum := by decide
  have hdescent : baseEnd_456799 < baseStart_456799 := by decide
  rcases family_descends (prefixWord ++ tailWord_456799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456802 : List Nat := [3, 3, 2, 2, 2, 9]
def baseStart_456802 : Nat := 118140960795 + 456802 * 2 ^ 59
def prefixEnd_456802 : Nat := 4983230072969 + 3 ^ 40 * 456802 * 2
def baseEnd_456802 : Nat := 3861053332267111008629

theorem tailTrace_456802 : CollatzResearch.WordTrace tailWord_456802 prefixEnd_456802 3861053332267111008629 := by
  unfold tailWord_456802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4165234422772961103893165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11107291794061229610381773 4165234422772961103893165)
  ·
    refine ⟨1561962908539860413959937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4165234422772961103893165 1561962908539860413959937)
    ·
      refine ⟨1171472181404895310469953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1561962908539860413959937 1171472181404895310469953)
      ·
        refine ⟨878604136053671482852465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1171472181404895310469953 878604136053671482852465)
        ·
          refine ⟨658953102040253612139349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878604136053671482852465 658953102040253612139349)
          ·
            refine ⟨3861053332267111008629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 658953102040253612139349 3861053332267111008629)
            ·
              rfl

theorem cell21_456802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 9].length) (baseStart_456802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456802 prefixEnd_456802 := by exact prefixLift 456802
  have htrace : WordTrace (prefixWord ++ tailWord_456802) baseStart_456802 baseEnd_456802 := by
    simpa [prefixWord, tailWord_456802, baseEnd_456802] using wordTrace_append hprefix tailTrace_456802
  have hstable : (prefixWord ++ tailWord_456802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456802).length < 2 ^ (prefixWord ++ tailWord_456802).sum := by decide
  have hdescent : baseEnd_456802 < baseStart_456802 := by decide
  rcases family_descends (prefixWord ++ tailWord_456802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456833 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 5]
def baseStart_456833 : Nat := 118140960795 + 456833 * 2 ^ 59
def prefixEnd_456833 : Nat := 4983230072969 + 3 ^ 40 * 456833 * 2
def baseEnd_456833 : Nat := 104255514593562832216253

theorem tailTrace_456833 : CollatzResearch.WordTrace tailWord_456833 prefixEnd_456833 104255514593562832216253 := by
  unfold tailWord_456833
  simp only [CollatzResearch.WordTrace]
  refine ⟨16662068353979536709951153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11108045569319691139967435 16662068353979536709951153)
  ·
    refine ⟨12496551265484652532463365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16662068353979536709951153 12496551265484652532463365)
    ·
      refine ⟨2343103362278372349836881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12496551265484652532463365 2343103362278372349836881)
      ·
        refine ⟨1757327521708779262377661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2343103362278372349836881 1757327521708779262377661)
        ·
          refine ⟨658997820640792223391623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1757327521708779262377661 658997820640792223391623)
          ·
            refine ⟨988496730961188335087435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658997820640792223391623 988496730961188335087435)
            ·
              refine ⟨1482745096441782502631153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988496730961188335087435 1482745096441782502631153)
              ·
                refine ⟨1112058822331336876973365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482745096441782502631153 1112058822331336876973365)
                ·
                  refine ⟨104255514593562832216253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1112058822331336876973365 104255514593562832216253)
                  ·
                    rfl

theorem cell21_456833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_456833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456833 prefixEnd_456833 := by exact prefixLift 456833
  have htrace : WordTrace (prefixWord ++ tailWord_456833) baseStart_456833 baseEnd_456833 := by
    simpa [prefixWord, tailWord_456833, baseEnd_456833] using wordTrace_append hprefix tailTrace_456833
  have hstable : (prefixWord ++ tailWord_456833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456833).length < 2 ^ (prefixWord ++ tailWord_456833).sum := by decide
  have hdescent : baseEnd_456833 < baseStart_456833 := by decide
  rcases family_descends (prefixWord ++ tailWord_456833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456850 : List Nat := [3, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_456850 : Nat := 118140960795 + 456850 * 2 ^ 59
def prefixEnd_456850 : Nat := 4983230072969 + 3 ^ 40 * 456850 * 2
def baseEnd_456850 : Nat := 104259394225174580432885

theorem tailTrace_456850 : CollatzResearch.WordTrace tailWord_456850 prefixEnd_456850 104259394225174580432885 := by
  unfold tailWord_456850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4165672098729487153330001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11108458929945299075546669 4165672098729487153330001)
  ·
    refine ⟨3124254074047115364997501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4165672098729487153330001 3124254074047115364997501)
    ·
      refine ⟨1171595277767668261874063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3124254074047115364997501 1171595277767668261874063)
      ·
        refine ⟨1757392916651502392811095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171595277767668261874063 1757392916651502392811095)
        ·
          refine ⟨2636089374977253589216643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757392916651502392811095 2636089374977253589216643)
          ·
            refine ⟨3954134062465880383824965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636089374977253589216643 3954134062465880383824965)
            ·
              refine ⟨741400136712352571967181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3954134062465880383824965 741400136712352571967181)
              ·
                refine ⟨278025051267132214487693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 741400136712352571967181 278025051267132214487693)
                ·
                  refine ⟨104259394225174580432885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278025051267132214487693 104259394225174580432885)
                  ·
                    rfl

theorem cell21_456850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_456850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456850 prefixEnd_456850 := by exact prefixLift 456850
  have htrace : WordTrace (prefixWord ++ tailWord_456850) baseStart_456850 baseEnd_456850 := by
    simpa [prefixWord, tailWord_456850, baseEnd_456850] using wordTrace_append hprefix tailTrace_456850
  have hstable : (prefixWord ++ tailWord_456850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456850).length < 2 ^ (prefixWord ++ tailWord_456850).sum := by decide
  have hdescent : baseEnd_456850 < baseStart_456850 := by decide
  rcases family_descends (prefixWord ++ tailWord_456850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456861 : List Nat := [1, 4, 2, 1, 1, 4, 8]
def baseStart_456861 : Nat := 118140960795 + 456861 * 2 ^ 59
def prefixEnd_456861 : Nat := 4983230072969 + 3 ^ 40 * 456861 * 2
def baseEnd_456861 : Nat := 11584656063893445083281

theorem tailTrace_456861 : CollatzResearch.WordTrace tailWord_456861 prefixEnd_456861 11584656063893445083281 := by
  unfold tailWord_456861
  simp only [CollatzResearch.WordTrace]
  refine ⟨16663089597878097491970437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11108726398585398327980291 16663089597878097491970437)
  ·
    refine ⟨3124329299602143279744457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16663089597878097491970437 3124329299602143279744457)
    ·
      refine ⟨2343246974701607459808343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3124329299602143279744457 2343246974701607459808343)
      ·
        refine ⟨3514870462052411189712515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343246974701607459808343 3514870462052411189712515)
        ·
          refine ⟨5272305693078616784568773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3514870462052411189712515 5272305693078616784568773)
          ·
            refine ⟨988557317452240647106645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5272305693078616784568773 988557317452240647106645)
            ·
              refine ⟨11584656063893445083281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 988557317452240647106645 11584656063893445083281)
              ·
                rfl

theorem cell21_456861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 8].length) (baseStart_456861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456861 prefixEnd_456861 := by exact prefixLift 456861
  have htrace : WordTrace (prefixWord ++ tailWord_456861) baseStart_456861 baseEnd_456861 := by
    simpa [prefixWord, tailWord_456861, baseEnd_456861] using wordTrace_append hprefix tailTrace_456861
  have hstable : (prefixWord ++ tailWord_456861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456861).length < 2 ^ (prefixWord ++ tailWord_456861).sum := by decide
  have hdescent : baseEnd_456861 < baseStart_456861 := by decide
  rcases family_descends (prefixWord ++ tailWord_456861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456864 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_456864 : Nat := 118140960795 + 456864 * 2 ^ 59
def prefixEnd_456864 : Nat := 4983230072969 + 3 ^ 40 * 456864 * 2
def baseEnd_456864 : Nat := 104262589215913667199523

theorem tailTrace_456864 : CollatzResearch.WordTrace tailWord_456864 prefixEnd_456864 104262589215913667199523 := by
  unfold tailWord_456864
  simp only [CollatzResearch.WordTrace]
  refine ⟨8331599508433614502164823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11108799344578152669553097 8331599508433614502164823)
  ·
    refine ⟨12497399262650421753247235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8331599508433614502164823 12497399262650421753247235)
    ·
      refine ⟨18746098893975632629870853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12497399262650421753247235 18746098893975632629870853)
      ·
        refine ⟨3514893542620431118100785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18746098893975632629870853 3514893542620431118100785)
        ·
          refine ⟨2636170156965323338575589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3514893542620431118100785 2636170156965323338575589)
          ·
            refine ⟨494281904430998125982923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2636170156965323338575589 494281904430998125982923)
            ·
              refine ⟨741422856646497188974385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494281904430998125982923 741422856646497188974385)
              ·
                refine ⟨556067142484872891730789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741422856646497188974385 556067142484872891730789)
                ·
                  refine ⟨104262589215913667199523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556067142484872891730789 104262589215913667199523)
                  ·
                    rfl

theorem cell21_456864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_456864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456864 prefixEnd_456864 := by exact prefixLift 456864
  have htrace : WordTrace (prefixWord ++ tailWord_456864) baseStart_456864 baseEnd_456864 := by
    simpa [prefixWord, tailWord_456864, baseEnd_456864] using wordTrace_append hprefix tailTrace_456864
  have hstable : (prefixWord ++ tailWord_456864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456864).length < 2 ^ (prefixWord ++ tailWord_456864).sum := by decide
  have hdescent : baseEnd_456864 < baseStart_456864 := by decide
  rcases family_descends (prefixWord ++ tailWord_456864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456881 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 4]
def baseStart_456881 : Nat := 118140960795 + 456881 * 2 ^ 59
def prefixEnd_456881 : Nat := 4983230072969 + 3 ^ 40 * 456881 * 2
def baseEnd_456881 : Nat := 104266468847525415416155

theorem tailTrace_456881 : CollatzResearch.WordTrace tailWord_456881 prefixEnd_456881 104266468847525415416155 := by
  unfold tailWord_456881
  simp only [CollatzResearch.WordTrace]
  refine ⟨16663819057805640907698497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11109212705203760605132331 16663819057805640907698497)
  ·
    refine ⟨12497864293354230680773873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16663819057805640907698497 12497864293354230680773873)
    ·
      refine ⟨9373398220015673010580405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12497864293354230680773873 9373398220015673010580405)
      ·
        refine ⟨878756083126469344741913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9373398220015673010580405 878756083126469344741913)
        ·
          refine ⟨659067062344852008556435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878756083126469344741913 659067062344852008556435)
          ·
            refine ⟨988600593517278012834653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659067062344852008556435 988600593517278012834653)
            ·
              refine ⟨370725222568979254812995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 988600593517278012834653 370725222568979254812995)
              ·
                refine ⟨556087833853468882219493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370725222568979254812995 556087833853468882219493)
                ·
                  refine ⟨104266468847525415416155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556087833853468882219493 104266468847525415416155)
                  ·
                    rfl

theorem cell21_456881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_456881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456881 prefixEnd_456881 := by exact prefixLift 456881
  have htrace : WordTrace (prefixWord ++ tailWord_456881) baseStart_456881 baseEnd_456881 := by
    simpa [prefixWord, tailWord_456881, baseEnd_456881] using wordTrace_append hprefix tailTrace_456881
  have hstable : (prefixWord ++ tailWord_456881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456881).length < 2 ^ (prefixWord ++ tailWord_456881).sum := by decide
  have hdescent : baseEnd_456881 < baseStart_456881 := by decide
  rcases family_descends (prefixWord ++ tailWord_456881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456906 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_456906 : Nat := 118140960795 + 456906 * 2 ^ 59
def prefixEnd_456906 : Nat := 4983230072969 + 3 ^ 40 * 456906 * 2
def baseEnd_456906 : Nat := 104272174188130927499437

theorem tailTrace_456906 : CollatzResearch.WordTrace tailWord_456906 prefixEnd_456906 104272174188130927499437 := by
  unfold tailWord_456906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166182720678767544339643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11109820588476713451572381 4166182720678767544339643)
  ·
    refine ⟨6249274081018151316509465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4166182720678767544339643 6249274081018151316509465)
    ·
      refine ⟨4686955560763613487382099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6249274081018151316509465 4686955560763613487382099)
      ·
        refine ⟨7030433341145420231073149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4686955560763613487382099 7030433341145420231073149)
        ·
          refine ⟨2636412502929532586652431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7030433341145420231073149 2636412502929532586652431)
          ·
            refine ⟨3954618754394298879978647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636412502929532586652431 3954618754394298879978647)
            ·
              refine ⟨5931928131591448319967971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954618754394298879978647 5931928131591448319967971)
              ·
                refine ⟨8897892197387172479951957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931928131591448319967971 8897892197387172479951957)
                ·
                  refine ⟨104272174188130927499437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8897892197387172479951957 104272174188130927499437)
                  ·
                    rfl

theorem cell21_456906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_456906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_456906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_456906 prefixEnd_456906 := by exact prefixLift 456906
  have htrace : WordTrace (prefixWord ++ tailWord_456906) baseStart_456906 baseEnd_456906 := by
    simpa [prefixWord, tailWord_456906, baseEnd_456906] using wordTrace_append hprefix tailTrace_456906
  have hstable : (prefixWord ++ tailWord_456906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456906).length < 2 ^ (prefixWord ++ tailWord_456906).sum := by decide
  have hdescent : baseEnd_456906 < baseStart_456906 := by decide
  rcases family_descends (prefixWord ++ tailWord_456906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457044 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_457044 : Nat := 118140960795 + 457044 * 2 ^ 59
def prefixEnd_457044 : Nat := 4983230072969 + 3 ^ 40 * 457044 * 2
def baseEnd_457044 : Nat := 104303667668273354199155

theorem tailTrace_457044 : CollatzResearch.WordTrace tailWord_457044 prefixEnd_457044 104303667668273354199155 := by
  unfold tailWord_457044
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334882078107559872941093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11113176104143413163921457 8334882078107559872941093)
  ·
    refine ⟨1562790389645167476176455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8334882078107559872941093 1562790389645167476176455)
    ·
      refine ⟨2344185584467751214264683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1562790389645167476176455 2344185584467751214264683)
      ·
        refine ⟨3516278376701626821397025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344185584467751214264683 3516278376701626821397025)
        ·
          refine ⟨2637208782526220116047769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3516278376701626821397025 2637208782526220116047769)
          ·
            refine ⟨1977906586894665087035827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2637208782526220116047769 1977906586894665087035827)
            ·
              refine ⟨2966859880341997630553741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977906586894665087035827 2966859880341997630553741)
              ·
                refine ⟨1112572455128249111457653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2966859880341997630553741 1112572455128249111457653)
                ·
                  refine ⟨104303667668273354199155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1112572455128249111457653 104303667668273354199155)
                  ·
                    rfl

theorem cell21_457044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_457044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457044 prefixEnd_457044 := by exact prefixLift 457044
  have htrace : WordTrace (prefixWord ++ tailWord_457044) baseStart_457044 baseEnd_457044 := by
    simpa [prefixWord, tailWord_457044, baseEnd_457044] using wordTrace_append hprefix tailTrace_457044
  have hstable : (prefixWord ++ tailWord_457044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457044).length < 2 ^ (prefixWord ++ tailWord_457044).sum := by decide
  have hdescent : baseEnd_457044 < baseStart_457044 := by decide
  rcases family_descends (prefixWord ++ tailWord_457044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457089 : List Nat := [1, 2, 4, 3, 1, 1, 9]
def baseStart_457089 : Nat := 118140960795 + 457089 * 2 ^ 59
def prefixEnd_457089 : Nat := 4983230072969 + 3 ^ 40 * 457089 * 2
def baseEnd_457089 : Nat := 11590437475707030661007

theorem tailTrace_457089 : CollatzResearch.WordTrace tailWord_457089 prefixEnd_457089 11590437475707030661007 := by
  unfold tailWord_457089
  simp only [CollatzResearch.WordTrace]
  refine ⟨16671405441052092431270321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11114270294034728287513547 16671405441052092431270321)
  ·
    refine ⟨12503554080789069323452741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16671405441052092431270321 12503554080789069323452741)
    ·
      refine ⟨2344416390147950498147389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12503554080789069323452741 2344416390147950498147389)
      ·
        refine ⟨879156146305481436805271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2344416390147950498147389 879156146305481436805271)
        ·
          refine ⟨1318734219458222155207907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879156146305481436805271 1318734219458222155207907)
          ·
            refine ⟨1978101329187333232811861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318734219458222155207907 1978101329187333232811861)
            ·
              refine ⟨11590437475707030661007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1978101329187333232811861 11590437475707030661007)
              ·
                rfl

theorem cell21_457089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 9].length) (baseStart_457089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457089 prefixEnd_457089 := by exact prefixLift 457089
  have htrace : WordTrace (prefixWord ++ tailWord_457089) baseStart_457089 baseEnd_457089 := by
    simpa [prefixWord, tailWord_457089, baseEnd_457089] using wordTrace_append hprefix tailTrace_457089
  have hstable : (prefixWord ++ tailWord_457089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457089).length < 2 ^ (prefixWord ++ tailWord_457089).sum := by decide
  have hdescent : baseEnd_457089 < baseStart_457089 := by decide
  rcases family_descends (prefixWord ++ tailWord_457089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457210 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_457210 : Nat := 118140960795 + 457210 * 2 ^ 59
def prefixEnd_457210 : Nat := 4983230072969 + 3 ^ 40 * 457210 * 2
def baseEnd_457210 : Nat := 104341551129893954432149

theorem tailTrace_457210 : CollatzResearch.WordTrace tailWord_457210 prefixEnd_457210 104341551129893954432149 := by
  unfold tailWord_457210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168954668403432524106271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11117212449075820064283389 4168954668403432524106271)
  ·
    refine ⟨6253432002605148786159407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4168954668403432524106271 6253432002605148786159407)
    ·
      refine ⟨9380148003907723179239111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6253432002605148786159407 9380148003907723179239111)
      ·
        refine ⟨14070222005861584768858667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9380148003907723179239111 14070222005861584768858667)
        ·
          refine ⟨21105333008792377153288001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14070222005861584768858667 21105333008792377153288001)
          ·
            refine ⟨15828999756594282864966001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21105333008792377153288001 15828999756594282864966001)
            ·
              refine ⟨11871749817445712148724501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15828999756594282864966001 11871749817445712148724501)
              ·
                refine ⟨556488272692767756971461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11871749817445712148724501 556488272692767756971461)
                ·
                  refine ⟨104341551129893954432149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556488272692767756971461 104341551129893954432149)
                  ·
                    rfl

theorem cell21_457210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_457210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457210 prefixEnd_457210 := by exact prefixLift 457210
  have htrace : WordTrace (prefixWord ++ tailWord_457210) baseStart_457210 baseEnd_457210 := by
    simpa [prefixWord, tailWord_457210, baseEnd_457210] using wordTrace_append hprefix tailTrace_457210
  have hstable : (prefixWord ++ tailWord_457210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457210).length < 2 ^ (prefixWord ++ tailWord_457210).sum := by decide
  have hdescent : baseEnd_457210 < baseStart_457210 := by decide
  rcases family_descends (prefixWord ++ tailWord_457210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457224 : List Nat := [2, 1, 3, 2, 1, 1, 1, 10]
def baseStart_457224 : Nat := 118140960795 + 457224 * 2 ^ 59
def prefixEnd_457224 : Nat := 4983230072969 + 3 ^ 40 * 457224 * 2
def baseEnd_457224 : Nat := 34781582040211013732929

theorem tailTrace_457224 : CollatzResearch.WordTrace tailWord_457224 prefixEnd_457224 34781582040211013732929 := by
  unfold tailWord_457224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338164647781505243717363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11117552863708673658289817 8338164647781505243717363)
  ·
    refine ⟨12507246971672257865576045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8338164647781505243717363 12507246971672257865576045)
    ·
      refine ⟨4690217614377096699591017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12507246971672257865576045 4690217614377096699591017)
      ·
        refine ⟨3517663210782822524693263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4690217614377096699591017 3517663210782822524693263)
        ·
          refine ⟨5276494816174233787039895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3517663210782822524693263 5276494816174233787039895)
          ·
            refine ⟨7914742224261350680559843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276494816174233787039895 7914742224261350680559843)
            ·
              refine ⟨11872113336392026020839765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7914742224261350680559843 11872113336392026020839765)
              ·
                refine ⟨34781582040211013732929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11872113336392026020839765 34781582040211013732929)
                ·
                  rfl

theorem cell21_457224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_457224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457224 prefixEnd_457224 := by exact prefixLift 457224
  have htrace : WordTrace (prefixWord ++ tailWord_457224) baseStart_457224 baseEnd_457224 := by
    simpa [prefixWord, tailWord_457224, baseEnd_457224] using wordTrace_append hprefix tailTrace_457224
  have hstable : (prefixWord ++ tailWord_457224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457224).length < 2 ^ (prefixWord ++ tailWord_457224).sum := by decide
  have hdescent : baseEnd_457224 < baseStart_457224 := by decide
  rcases family_descends (prefixWord ++ tailWord_457224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457278 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_457278 : Nat := 118140960795 + 457278 * 2 ^ 59
def prefixEnd_457278 : Nat := 4983230072969 + 3 ^ 40 * 457278 * 2
def baseEnd_457278 : Nat := 104357069656340947298677

theorem tailTrace_457278 : CollatzResearch.WordTrace tailWord_457278 prefixEnd_457278 104357069656340947298677 := by
  unfold tailWord_457278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084787354670922213737561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11118865891578251806600325 2084787354670922213737561)
  ·
    refine ⟨1563590516003191660303171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2084787354670922213737561 1563590516003191660303171)
    ·
      refine ⟨2345385774004787490454757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563590516003191660303171 2345385774004787490454757)
      ·
        refine ⟨439759832625897654460267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2345385774004787490454757 439759832625897654460267)
        ·
          refine ⟨659639748938846481690401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439759832625897654460267 659639748938846481690401)
          ·
            refine ⟨494729811704134861267801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659639748938846481690401 494729811704134861267801)
            ·
              refine ⟨371047358778101145950851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494729811704134861267801 371047358778101145950851)
              ·
                refine ⟨556571038167151718926277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371047358778101145950851 556571038167151718926277)
                ·
                  refine ⟨104357069656340947298677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556571038167151718926277 104357069656340947298677)
                  ·
                    rfl

theorem cell21_457278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_457278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457278 prefixEnd_457278 := by exact prefixLift 457278
  have htrace : WordTrace (prefixWord ++ tailWord_457278) baseStart_457278 baseEnd_457278 := by
    simpa [prefixWord, tailWord_457278, baseEnd_457278] using wordTrace_append hprefix tailTrace_457278
  have hstable : (prefixWord ++ tailWord_457278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457278).length < 2 ^ (prefixWord ++ tailWord_457278).sum := by decide
  have hdescent : baseEnd_457278 < baseStart_457278 := by decide
  rcases family_descends (prefixWord ++ tailWord_457278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457317 : List Nat := [1, 3, 1, 3, 5, 8]
def baseStart_457317 : Nat := 118140960795 + 457317 * 2 ^ 59
def prefixEnd_457317 : Nat := 4983230072969 + 3 ^ 40 * 457317 * 2
def baseEnd_457317 : Nat := 3865406295840205412911

theorem tailTrace_457317 : CollatzResearch.WordTrace tailWord_457317 prefixEnd_457317 3865406295840205412911 := by
  unfold tailWord_457317
  simp only [CollatzResearch.WordTrace]
  refine ⟨16679721284226087370570205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11119814189484058247046803 16679721284226087370570205)
  ·
    refine ⟨6254895481584782763963827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16679721284226087370570205 6254895481584782763963827)
    ·
      refine ⟨9382343222377174145945741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6254895481584782763963827 9382343222377174145945741)
      ·
        refine ⟨3518378708391440304729653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9382343222377174145945741 3518378708391440304729653)
        ·
          refine ⟨329848003911697528568405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3518378708391440304729653 329848003911697528568405)
          ·
            refine ⟨3865406295840205412911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 329848003911697528568405 3865406295840205412911)
            ·
              rfl

theorem cell21_457317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 8].length) (baseStart_457317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457317 prefixEnd_457317 := by exact prefixLift 457317
  have htrace : WordTrace (prefixWord ++ tailWord_457317) baseStart_457317 baseEnd_457317 := by
    simpa [prefixWord, tailWord_457317, baseEnd_457317] using wordTrace_append hprefix tailTrace_457317
  have hstable : (prefixWord ++ tailWord_457317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457317).length < 2 ^ (prefixWord ++ tailWord_457317).sum := by decide
  have hdescent : baseEnd_457317 < baseStart_457317 := by decide
  rcases family_descends (prefixWord ++ tailWord_457317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457320 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_457320 : Nat := 118140960795 + 457320 * 2 ^ 59
def prefixEnd_457320 : Nat := 4983230072969 + 3 ^ 40 * 457320 * 2
def baseEnd_457320 : Nat := 104366654628558207598591

theorem tailTrace_457320 : CollatzResearch.WordTrace tailWord_457320 prefixEnd_457320 104366654628558207598591 := by
  unfold tailWord_457320
  simp only [CollatzResearch.WordTrace]
  refine ⟨8339915351607609441464707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11119887135476812588619609 8339915351607609441464707)
  ·
    refine ⟨12509873027411414162197061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8339915351607609441464707 12509873027411414162197061)
    ·
      refine ⟨2345601192639640155411949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12509873027411414162197061 2345601192639640155411949)
      ·
        refine ⟨879600447239865058279481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2345601192639640155411949 879600447239865058279481)
        ·
          refine ⟨659700335429898793709611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 879600447239865058279481 659700335429898793709611)
          ·
            refine ⟨989550503144848190564417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659700335429898793709611 989550503144848190564417)
            ·
              refine ⟨742162877358636142923313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989550503144848190564417 742162877358636142923313)
              ·
                refine ⟨556622158018977107192485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742162877358636142923313 556622158018977107192485)
                ·
                  refine ⟨104366654628558207598591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556622158018977107192485 104366654628558207598591)
                  ·
                    rfl

theorem cell21_457320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_457320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457320 prefixEnd_457320 := by exact prefixLift 457320
  have htrace : WordTrace (prefixWord ++ tailWord_457320) baseStart_457320 baseEnd_457320 := by
    simpa [prefixWord, tailWord_457320, baseEnd_457320] using wordTrace_append hprefix tailTrace_457320
  have hstable : (prefixWord ++ tailWord_457320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457320).length < 2 ^ (prefixWord ++ tailWord_457320).sum := by decide
  have hdescent : baseEnd_457320 < baseStart_457320 := by decide
  rcases family_descends (prefixWord ++ tailWord_457320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457348 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_457348 : Nat := 118140960795 + 457348 * 2 ^ 59
def prefixEnd_457348 : Nat := 4983230072969 + 3 ^ 40 * 457348 * 2
def baseEnd_457348 : Nat := 104373044610036381131867

theorem tailTrace_457348 : CollatzResearch.WordTrace tailWord_457348 prefixEnd_457348 104373044610036381131867 := by
  unfold tailWord_457348
  simp only [CollatzResearch.WordTrace]
  refine ⟨8340425973556889832474349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11120567964742519776632465 8340425973556889832474349)
  ·
    refine ⟨3127659740083833687177881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8340425973556889832474349 3127659740083833687177881)
    ·
      refine ⟨2345744805062875265383411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3127659740083833687177881 2345744805062875265383411)
      ·
        refine ⟨3518617207594312898075117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345744805062875265383411 3518617207594312898075117)
        ·
          refine ⟨1319481452847867336778169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3518617207594312898075117 1319481452847867336778169)
          ·
            refine ⟨989611089635900502583627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319481452847867336778169 989611089635900502583627)
            ·
              refine ⟨1484416634453850753875441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989611089635900502583627 1484416634453850753875441)
              ·
                refine ⟨1113312475840388065406581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484416634453850753875441 1113312475840388065406581)
                ·
                  refine ⟨104373044610036381131867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1113312475840388065406581 104373044610036381131867)
                  ·
                    rfl

theorem cell21_457348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_457348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457348 prefixEnd_457348 := by exact prefixLift 457348
  have htrace : WordTrace (prefixWord ++ tailWord_457348) baseStart_457348 baseEnd_457348 := by
    simpa [prefixWord, tailWord_457348, baseEnd_457348] using wordTrace_append hprefix tailTrace_457348
  have hstable : (prefixWord ++ tailWord_457348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457348).length < 2 ^ (prefixWord ++ tailWord_457348).sum := by decide
  have hdescent : baseEnd_457348 < baseStart_457348 := by decide
  rcases family_descends (prefixWord ++ tailWord_457348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457407 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 5]
def baseStart_457407 : Nat := 118140960795 + 457407 * 2 ^ 59
def prefixEnd_457407 : Nat := 4983230072969 + 3 ^ 40 * 457407 * 2
def baseEnd_457407 : Nat := 104386509213865389648413

theorem tailTrace_457407 : CollatzResearch.WordTrace tailWord_457407 prefixEnd_457407 104386509213865389648413 := by
  unfold tailWord_457407
  simp only [CollatzResearch.WordTrace]
  refine ⟨16683003853900032741346475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11122002569266688494230983 16683003853900032741346475)
  ·
    refine ⟨25024505780850049112019713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16683003853900032741346475 25024505780850049112019713)
    ·
      refine ⟨18768379335637536834014785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25024505780850049112019713 18768379335637536834014785)
      ·
        refine ⟨14076284501728152625511089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18768379335637536834014785 14076284501728152625511089)
        ·
          refine ⟨10557213376296114469133317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14076284501728152625511089 10557213376296114469133317)
          ·
            refine ⟨1979477508055521462962497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10557213376296114469133317 1979477508055521462962497)
            ·
              refine ⟨1484608131041641097221873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1979477508055521462962497 1484608131041641097221873)
              ·
                refine ⟨1113456098281230822916405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484608131041641097221873 1113456098281230822916405)
                ·
                  refine ⟨104386509213865389648413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1113456098281230822916405 104386509213865389648413)
                  ·
                    rfl

theorem cell21_457407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_457407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457407 prefixEnd_457407 := by exact prefixLift 457407
  have htrace : WordTrace (prefixWord ++ tailWord_457407) baseStart_457407 baseEnd_457407 := by
    simpa [prefixWord, tailWord_457407, baseEnd_457407] using wordTrace_append hprefix tailTrace_457407
  have hstable : (prefixWord ++ tailWord_457407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457407).length < 2 ^ (prefixWord ++ tailWord_457407).sum := by decide
  have hdescent : baseEnd_457407 < baseStart_457407 := by decide
  rcases family_descends (prefixWord ++ tailWord_457407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457455 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 4]
def baseStart_457455 : Nat := 118140960795 + 457455 * 2 ^ 59
def prefixEnd_457455 : Nat := 4983230072969 + 3 ^ 40 * 457455 * 2
def baseEnd_457455 : Nat := 104397463467827972848315

theorem tailTrace_457455 : CollatzResearch.WordTrace tailWord_457455 prefixEnd_457455 104397463467827972848315 := by
  unfold tailWord_457455
  simp only [CollatzResearch.WordTrace]
  refine ⟨16684754557726136939093819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11123169705150757959395879 16684754557726136939093819)
  ·
    refine ⟨25027131836589205408640729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16684754557726136939093819 25027131836589205408640729)
    ·
      refine ⟨18770348877441904056480547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25027131836589205408640729 18770348877441904056480547)
      ·
        refine ⟨28155523316162856084720821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18770348877441904056480547 28155523316162856084720821)
        ·
          refine ⟨2639580310890267757942577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28155523316162856084720821 2639580310890267757942577)
          ·
            refine ⟨1979685233167700818456933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2639580310890267757942577 1979685233167700818456933)
            ·
              refine ⟨371190981218943903460675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1979685233167700818456933 371190981218943903460675)
              ·
                refine ⟨556786471828415855191013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371190981218943903460675 556786471828415855191013)
                ·
                  refine ⟨104397463467827972848315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556786471828415855191013 104397463467827972848315)
                  ·
                    rfl

theorem cell21_457455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 4].length) (baseStart_457455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457455 prefixEnd_457455 := by exact prefixLift 457455
  have htrace : WordTrace (prefixWord ++ tailWord_457455) baseStart_457455 baseEnd_457455 := by
    simpa [prefixWord, tailWord_457455, baseEnd_457455] using wordTrace_append hprefix tailTrace_457455
  have hstable : (prefixWord ++ tailWord_457455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457455).length < 2 ^ (prefixWord ++ tailWord_457455).sum := by decide
  have hdescent : baseEnd_457455 < baseStart_457455 := by decide
  rcases family_descends (prefixWord ++ tailWord_457455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457534 : List Nat := [4, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_457534 : Nat := 118140960795 + 457534 * 2 ^ 59
def prefixEnd_457534 : Nat := 4983230072969 + 3 ^ 40 * 457534 * 2
def baseEnd_457534 : Nat := 104415492344141391031487

theorem tailTrace_457534 : CollatzResearch.WordTrace tailWord_457534 prefixEnd_457534 104415492344141391031487 := by
  unfold tailWord_457534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2085954490554991678902457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11125090616293288954146437 2085954490554991678902457)
  ·
    refine ⟨1564465867916243759176843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2085954490554991678902457 1564465867916243759176843)
    ·
      refine ⟨2346698801874365638765265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564465867916243759176843 2346698801874365638765265)
      ·
        refine ⟨1760024101405774229073949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2346698801874365638765265 1760024101405774229073949)
        ·
          refine ⟨660009038027165335902731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1760024101405774229073949 660009038027165335902731)
          ·
            refine ⟨990013557040748003854097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660009038027165335902731 990013557040748003854097)
            ·
              refine ⟨742510167780561002890573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990013557040748003854097 742510167780561002890573)
              ·
                refine ⟨278441312917710376083965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742510167780561002890573 278441312917710376083965)
                ·
                  refine ⟨104415492344141391031487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278441312917710376083965 104415492344141391031487)
                  ·
                    rfl

theorem cell21_457534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_457534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457534 prefixEnd_457534 := by exact prefixLift 457534
  have htrace : WordTrace (prefixWord ++ tailWord_457534) baseStart_457534 baseEnd_457534 := by
    simpa [prefixWord, tailWord_457534, baseEnd_457534] using wordTrace_append hprefix tailTrace_457534
  have hstable : (prefixWord ++ tailWord_457534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457534).length < 2 ^ (prefixWord ++ tailWord_457534).sum := by decide
  have hdescent : baseEnd_457534 < baseStart_457534 := by decide
  rcases family_descends (prefixWord ++ tailWord_457534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457559 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 5]
def baseStart_457559 : Nat := 118140960795 + 457559 * 2 ^ 59
def prefixEnd_457559 : Nat := 4983230072969 + 3 ^ 40 * 457559 * 2
def baseEnd_457559 : Nat := 104421197684746903114769

theorem tailTrace_457559 : CollatzResearch.WordTrace tailWord_457559 prefixEnd_457559 104421197684746903114769 := by
  unfold tailWord_457559
  simp only [CollatzResearch.WordTrace]
  refine ⟨16688547749349362700879731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11125698499566241800586487 16688547749349362700879731)
  ·
    refine ⟨25032821624024044051319597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16688547749349362700879731 25032821624024044051319597)
    ·
      refine ⟨9387308109009016519244849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25032821624024044051319597 9387308109009016519244849)
      ·
        refine ⟨7040481081756762389433637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9387308109009016519244849 7040481081756762389433637)
        ·
          refine ⟨1320090202829392948018807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7040481081756762389433637 1320090202829392948018807)
          ·
            refine ⟨1980135304244089422028211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320090202829392948018807 1980135304244089422028211)
            ·
              refine ⟨2970202956366134133042317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980135304244089422028211 2970202956366134133042317)
              ·
                refine ⟨1113826108637300299890869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2970202956366134133042317 1113826108637300299890869)
                ·
                  refine ⟨104421197684746903114769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1113826108637300299890869 104421197684746903114769)
                  ·
                    rfl

theorem cell21_457559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_457559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457559 prefixEnd_457559 := by exact prefixLift 457559
  have htrace : WordTrace (prefixWord ++ tailWord_457559) baseStart_457559 baseEnd_457559 := by
    simpa [prefixWord, tailWord_457559, baseEnd_457559] using wordTrace_append hprefix tailTrace_457559
  have hstable : (prefixWord ++ tailWord_457559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457559).length < 2 ^ (prefixWord ++ tailWord_457559).sum := by decide
  have hdescent : baseEnd_457559 < baseStart_457559 := by decide
  rcases family_descends (prefixWord ++ tailWord_457559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457593 : List Nat := [1, 2, 1, 3, 2, 5, 1, 3, 3]
def baseStart_457593 : Nat := 118140960795 + 457593 * 2 ^ 59
def prefixEnd_457593 : Nat := 4983230072969 + 3 ^ 40 * 457593 * 2
def baseEnd_457593 : Nat := 104428956947970399548033

theorem tailTrace_457593 : CollatzResearch.WordTrace tailWord_457593 prefixEnd_457593 104428956947970399548033 := by
  unfold tailWord_457593
  simp only [CollatzResearch.WordTrace]
  refine ⟨16689787831226186507617433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11126525220817457671744955 16689787831226186507617433)
  ·
    refine ⟨12517340873419639880713075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16689787831226186507617433 12517340873419639880713075)
    ·
      refine ⟨18776011310129459821069613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12517340873419639880713075 18776011310129459821069613)
      ·
        refine ⟨7041004241298547432901105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18776011310129459821069613 7041004241298547432901105)
        ·
          refine ⟨5280753180973910574675829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7041004241298547432901105 5280753180973910574675829)
          ·
            refine ⟨495070610716304116375859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5280753180973910574675829 495070610716304116375859)
            ·
              refine ⟨742605916074456174563789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495070610716304116375859 742605916074456174563789)
              ·
                refine ⟨278477218527921065461421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742605916074456174563789 278477218527921065461421)
                ·
                  refine ⟨104428956947970399548033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278477218527921065461421 104428956947970399548033)
                  ·
                    rfl

theorem cell21_457593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_457593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457593 prefixEnd_457593 := by exact prefixLift 457593
  have htrace : WordTrace (prefixWord ++ tailWord_457593) baseStart_457593 baseEnd_457593 := by
    simpa [prefixWord, tailWord_457593, baseEnd_457593] using wordTrace_append hprefix tailTrace_457593
  have hstable : (prefixWord ++ tailWord_457593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457593).length < 2 ^ (prefixWord ++ tailWord_457593).sum := by decide
  have hdescent : baseEnd_457593 < baseStart_457593 := by decide
  rcases family_descends (prefixWord ++ tailWord_457593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457610 : List Nat := [3, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_457610 : Nat := 118140960795 + 457610 * 2 ^ 59
def prefixEnd_457610 : Nat := 4983230072969 + 3 ^ 40 * 457610 * 2
def baseEnd_457610 : Nat := 104432836579582147764665

theorem tailTrace_457610 : CollatzResearch.WordTrace tailWord_457610 prefixEnd_457610 104432836579582147764665 := by
  unfold tailWord_457610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172601968041149602746571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11126938581443065607324189 4172601968041149602746571)
  ·
    refine ⟨6258902952061724404119857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4172601968041149602746571 6258902952061724404119857)
    ·
      refine ⟨4694177214046293303089893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6258902952061724404119857 4694177214046293303089893)
      ·
        refine ⟨880158227633679994329355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4694177214046293303089893 880158227633679994329355)
        ·
          refine ⟨1320237341450519991494033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880158227633679994329355 1320237341450519991494033)
          ·
            refine ⟨990178006087889993620525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320237341450519991494033 990178006087889993620525)
            ·
              refine ⟨371316752282958747607697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 990178006087889993620525 371316752282958747607697)
              ·
                refine ⟨278487564212219060705773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371316752282958747607697 278487564212219060705773)
                ·
                  refine ⟨104432836579582147764665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278487564212219060705773 104432836579582147764665)
                  ·
                    rfl

theorem cell21_457610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_457610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457610 prefixEnd_457610 := by exact prefixLift 457610
  have htrace : WordTrace (prefixWord ++ tailWord_457610) baseStart_457610 baseEnd_457610 := by
    simpa [prefixWord, tailWord_457610, baseEnd_457610] using wordTrace_append hprefix tailTrace_457610
  have hstable : (prefixWord ++ tailWord_457610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457610).length < 2 ^ (prefixWord ++ tailWord_457610).sum := by decide
  have hdescent : baseEnd_457610 < baseStart_457610 := by decide
  rcases family_descends (prefixWord ++ tailWord_457610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457717 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 4]
def baseStart_457717 : Nat := 118140960795 + 457717 * 2 ^ 59
def prefixEnd_457717 : Nat := 4983230072969 + 3 ^ 40 * 457717 * 2
def baseEnd_457717 : Nat := 104457255437373739481113

theorem tailTrace_457717 : CollatzResearch.WordTrace tailWord_457717 prefixEnd_457717 104457255437373739481113 := by
  unfold tailWord_457717
  simp only [CollatzResearch.WordTrace]
  refine ⟨16694310482776955685131405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11129540321851303790087603 16694310482776955685131405)
  ·
    refine ⟨6260366431041358381924277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16694310482776955685131405 6260366431041358381924277)
    ·
      refine ⟨586909352910127348305401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6260366431041358381924277 586909352910127348305401)
      ·
        refine ⟨440182014682595511229051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586909352910127348305401 440182014682595511229051)
        ·
          refine ⟨660273022023893266843577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440182014682595511229051 660273022023893266843577)
          ·
            refine ⟨495204766517919950132683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660273022023893266843577 495204766517919950132683)
            ·
              refine ⟨742807149776879925199025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495204766517919950132683 742807149776879925199025)
              ·
                refine ⟨557105362332659943899269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742807149776879925199025 557105362332659943899269)
                ·
                  refine ⟨104457255437373739481113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557105362332659943899269 104457255437373739481113)
                  ·
                    rfl

theorem cell21_457717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_457717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457717 prefixEnd_457717 := by exact prefixLift 457717
  have htrace : WordTrace (prefixWord ++ tailWord_457717) baseStart_457717 baseEnd_457717 := by
    simpa [prefixWord, tailWord_457717, baseEnd_457717] using wordTrace_append hprefix tailTrace_457717
  have hstable : (prefixWord ++ tailWord_457717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457717).length < 2 ^ (prefixWord ++ tailWord_457717).sum := by decide
  have hdescent : baseEnd_457717 < baseStart_457717 := by decide
  rcases family_descends (prefixWord ++ tailWord_457717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457793 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 4]
def baseStart_457793 : Nat := 118140960795 + 457793 * 2 ^ 59
def prefixEnd_457793 : Nat := 4983230072969 + 3 ^ 40 * 457793 * 2
def baseEnd_457793 : Nat := 104474599672814496214291

theorem tailTrace_457793 : CollatzResearch.WordTrace tailWord_457793 prefixEnd_457793 104474599672814496214291 := by
  unfold tailWord_457793
  simp only [CollatzResearch.WordTrace]
  refine ⟨16697082430501620664898033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11131388287001080443265355 16697082430501620664898033)
  ·
    refine ⟨12522811822876215498673525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16697082430501620664898033 12522811822876215498673525)
    ·
      refine ⟨1174013608394645203000643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12522811822876215498673525 1174013608394645203000643)
      ·
        refine ⟨1761020412591967804500965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174013608394645203000643 1761020412591967804500965)
        ·
          refine ⟨330191327360993963343931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1761020412591967804500965 330191327360993963343931)
          ·
            refine ⟨495286991041490945015897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330191327360993963343931 495286991041490945015897)
            ·
              refine ⟨371465243281118208761923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495286991041490945015897 371465243281118208761923)
              ·
                refine ⟨557197864921677313142885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371465243281118208761923 557197864921677313142885)
                ·
                  refine ⟨104474599672814496214291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557197864921677313142885 104474599672814496214291)
                  ·
                    rfl

theorem cell21_457793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_457793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457793 prefixEnd_457793 := by exact prefixLift 457793
  have htrace : WordTrace (prefixWord ++ tailWord_457793) baseStart_457793 baseEnd_457793 := by
    simpa [prefixWord, tailWord_457793, baseEnd_457793] using wordTrace_append hprefix tailTrace_457793
  have hstable : (prefixWord ++ tailWord_457793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457793).length < 2 ^ (prefixWord ++ tailWord_457793).sum := by decide
  have hdescent : baseEnd_457793 < baseStart_457793 := by decide
  rcases family_descends (prefixWord ++ tailWord_457793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457832 : List Nat := [2, 1, 4, 4, 10]
def baseStart_457832 : Nat := 118140960795 + 457832 * 2 ^ 59
def prefixEnd_457832 : Nat := 4983230072969 + 3 ^ 40 * 457832 * 2
def baseEnd_457832 : Nat := 1289919753137766605731

theorem tailTrace_457832 : CollatzResearch.WordTrace tailWord_457832 prefixEnd_457832 1289919753137766605731 := by
  unfold tailWord_457832
  simp only [CollatzResearch.WordTrace]
  refine ⟨8349252438680165162783875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11132336584906886883711833 8349252438680165162783875)
  ·
    refine ⟨12523878658020247744175813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8349252438680165162783875 12523878658020247744175813)
    ·
      refine ⟨2348227248378796452032965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12523878658020247744175813 2348227248378796452032965)
      ·
        refine ⟨440292609071024334756181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2348227248378796452032965 440292609071024334756181)
        ·
          refine ⟨1289919753137766605731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 440292609071024334756181 1289919753137766605731)
          ·
            rfl

theorem cell21_457832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 10].length) (baseStart_457832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457832 prefixEnd_457832 := by exact prefixLift 457832
  have htrace : WordTrace (prefixWord ++ tailWord_457832) baseStart_457832 baseEnd_457832 := by
    simpa [prefixWord, tailWord_457832, baseEnd_457832] using wordTrace_append hprefix tailTrace_457832
  have hstable : (prefixWord ++ tailWord_457832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457832).length < 2 ^ (prefixWord ++ tailWord_457832).sum := by decide
  have hdescent : baseEnd_457832 < baseStart_457832 := by decide
  rcases family_descends (prefixWord ++ tailWord_457832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457838 : List Nat := [4, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_457838 : Nat := 118140960795 + 457838 * 2 ^ 59
def prefixEnd_457838 : Nat := 4983230072969 + 3 ^ 40 * 457838 * 2
def baseEnd_457838 : Nat := 104484869285904417964199

theorem tailTrace_457838 : CollatzResearch.WordTrace tailWord_457838 prefixEnd_457838 104484869285904417964199 := by
  unfold tailWord_457838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2087340464417324168785771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11132482476892395566857445 2087340464417324168785771)
  ·
    refine ⟨3131010696625986253178657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2087340464417324168785771 3131010696625986253178657)
    ·
      refine ⟨2348258022469489689883993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3131010696625986253178657 2348258022469489689883993)
      ·
        refine ⟨1761193516852117267412995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2348258022469489689883993 1761193516852117267412995)
        ·
          refine ⟨2641790275278175901119493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761193516852117267412995 2641790275278175901119493)
          ·
            refine ⟨495335676614657981459905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2641790275278175901119493 495335676614657981459905)
            ·
              refine ⟨371501757460993486094929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495335676614657981459905 371501757460993486094929)
              ·
                refine ⟨278626318095745114571197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371501757460993486094929 278626318095745114571197)
                ·
                  refine ⟨104484869285904417964199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278626318095745114571197 104484869285904417964199)
                  ·
                    rfl

theorem cell21_457838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_457838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457838 prefixEnd_457838 := by exact prefixLift 457838
  have htrace : WordTrace (prefixWord ++ tailWord_457838) baseStart_457838 baseEnd_457838 := by
    simpa [prefixWord, tailWord_457838, baseEnd_457838] using wordTrace_append hprefix tailTrace_457838
  have hstable : (prefixWord ++ tailWord_457838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457838).length < 2 ^ (prefixWord ++ tailWord_457838).sum := by decide
  have hdescent : baseEnd_457838 < baseStart_457838 := by decide
  rcases family_descends (prefixWord ++ tailWord_457838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457849 : List Nat := [1, 2, 1, 3, 5, 2, 1, 6]
def baseStart_457849 : Nat := 118140960795 + 457849 * 2 ^ 59
def prefixEnd_457849 : Nat := 4983230072969 + 3 ^ 40 * 457849 * 2
def baseEnd_457849 : Nat := 34829126545256947760281

theorem tailTrace_457849 : CollatzResearch.WordTrace tailWord_457849 prefixEnd_457849 34829126545256947760281 := by
  unfold tailWord_457849
  simp only [CollatzResearch.WordTrace]
  refine ⟨16699124918298742228936601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11132749945532494819291067 16699124918298742228936601)
  ·
    refine ⟨12524343688724056671702451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16699124918298742228936601 12524343688724056671702451)
    ·
      refine ⟨18786515533086085007553677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12524343688724056671702451 18786515533086085007553677)
      ·
        refine ⟨7044943324907281877832629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18786515533086085007553677 7044943324907281877832629)
        ·
          refine ⟨660463436710057676046809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7044943324907281877832629 660463436710057676046809)
          ·
            refine ⟨495347577532543257035107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660463436710057676046809 495347577532543257035107)
            ·
              refine ⟨743021366298814885552661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495347577532543257035107 743021366298814885552661)
              ·
                refine ⟨34829126545256947760281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 743021366298814885552661 34829126545256947760281)
                ·
                  rfl

theorem cell21_457849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 6].length) (baseStart_457849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457849 prefixEnd_457849 := by exact prefixLift 457849
  have htrace : WordTrace (prefixWord ++ tailWord_457849) baseStart_457849 baseEnd_457849 := by
    simpa [prefixWord, tailWord_457849, baseEnd_457849] using wordTrace_append hprefix tailTrace_457849
  have hstable : (prefixWord ++ tailWord_457849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457849).length < 2 ^ (prefixWord ++ tailWord_457849).sum := by decide
  have hdescent : baseEnd_457849 < baseStart_457849 := by decide
  rcases family_descends (prefixWord ++ tailWord_457849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457880 : List Nat := [2, 1, 2, 4, 2, 1, 1, 5, 3]
def baseStart_457880 : Nat := 118140960795 + 457880 * 2 ^ 59
def prefixEnd_457880 : Nat := 4983230072969 + 3 ^ 40 * 457880 * 2
def baseEnd_457880 : Nat := 104494454258121678264113

theorem tailTrace_457880 : CollatzResearch.WordTrace tailWord_457880 prefixEnd_457880 104494454258121678264113 := by
  unfold tailWord_457880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8350127790593217261657547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11133503720790956348876729 8350127790593217261657547)
  ·
    refine ⟨12525191685889825892486321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8350127790593217261657547 12525191685889825892486321)
    ·
      refine ⟨9393893764417369419364741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12525191685889825892486321 9393893764417369419364741)
      ·
        refine ⟨1761355080828256766130889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9393893764417369419364741 1761355080828256766130889)
        ·
          refine ⟨1321016310621192574598167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1761355080828256766130889 1321016310621192574598167)
          ·
            refine ⟨1981524465931788861897251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321016310621192574598167 1981524465931788861897251)
            ·
              refine ⟨2972286698897683292845877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981524465931788861897251 2972286698897683292845877)
              ·
                refine ⟨278651878021657808704301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2972286698897683292845877 278651878021657808704301)
                ·
                  refine ⟨104494454258121678264113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278651878021657808704301 104494454258121678264113)
                  ·
                    rfl

theorem cell21_457880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_457880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457880 prefixEnd_457880 := by exact prefixLift 457880
  have htrace : WordTrace (prefixWord ++ tailWord_457880) baseStart_457880 baseEnd_457880 := by
    simpa [prefixWord, tailWord_457880, baseEnd_457880] using wordTrace_append hprefix tailTrace_457880
  have hstable : (prefixWord ++ tailWord_457880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457880).length < 2 ^ (prefixWord ++ tailWord_457880).sum := by decide
  have hdescent : baseEnd_457880 < baseStart_457880 := by decide
  rcases family_descends (prefixWord ++ tailWord_457880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457942 : List Nat := [5, 2, 1, 2, 2, 2, 7]
def baseStart_457942 : Nat := 118140960795 + 457942 * 2 ^ 59
def prefixEnd_457942 : Nat := 4983230072969 + 3 ^ 40 * 457942 * 2
def baseEnd_457942 : Nat := 11612067055869260914517

theorem tailTrace_457942 : CollatzResearch.WordTrace tailWord_457942 prefixEnd_457942 11612067055869260914517 := by
  unfold tailWord_457942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043907306685113694504505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11135011271307879408048053 1043907306685113694504505)
  ·
    refine ⟨782930480013835270878379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1043907306685113694504505 782930480013835270878379)
    ·
      refine ⟨1174395720020752906317569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 782930480013835270878379 1174395720020752906317569)
      ·
        refine ⟨880796790015564679738177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1174395720020752906317569 880796790015564679738177)
        ·
          refine ⟨660597592511673509803633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880796790015564679738177 660597592511673509803633)
          ·
            refine ⟨495448194383755132352725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660597592511673509803633 495448194383755132352725)
            ·
              refine ⟨11612067055869260914517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 495448194383755132352725 11612067055869260914517)
              ·
                rfl

theorem cell21_457942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 7].length) (baseStart_457942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457942 prefixEnd_457942 := by exact prefixLift 457942
  have htrace : WordTrace (prefixWord ++ tailWord_457942) baseStart_457942 baseEnd_457942 := by
    simpa [prefixWord, tailWord_457942, baseEnd_457942] using wordTrace_append hprefix tailTrace_457942
  have hstable : (prefixWord ++ tailWord_457942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457942).length < 2 ^ (prefixWord ++ tailWord_457942).sum := by decide
  have hdescent : baseEnd_457942 < baseStart_457942 := by decide
  rcases family_descends (prefixWord ++ tailWord_457942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457953 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 6]
def baseStart_457953 : Nat := 118140960795 + 457953 * 2 ^ 59
def prefixEnd_457953 : Nat := 4983230072969 + 3 ^ 40 * 457953 * 2
def baseEnd_457953 : Nat := 104511113852689773547297

theorem tailTrace_457953 : CollatzResearch.WordTrace tailWord_457953 prefixEnd_457953 104511113852689773547297 := by
  unfold tailWord_457953
  simp only [CollatzResearch.WordTrace]
  refine ⟨16702918109921967990722513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11135278739947978660481675 16702918109921967990722513)
  ·
    refine ⟨12527188582441475993041885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16702918109921967990722513 12527188582441475993041885)
    ·
      refine ⟨4697695718415553497390707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12527188582441475993041885 4697695718415553497390707)
      ·
        refine ⟨7046543577623330246086061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697695718415553497390707 7046543577623330246086061)
        ·
          refine ⟨2642453841608748842282273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7046543577623330246086061 2642453841608748842282273)
          ·
            refine ⟨1981840381206561631711705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2642453841608748842282273 1981840381206561631711705)
            ·
              refine ⟨1486380285904921223783779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981840381206561631711705 1486380285904921223783779)
              ·
                refine ⟨2229570428857381835675669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486380285904921223783779 2229570428857381835675669)
                ·
                  refine ⟨104511113852689773547297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2229570428857381835675669 104511113852689773547297)
                  ·
                    rfl

theorem cell21_457953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_457953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_457953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_457953 prefixEnd_457953 := by exact prefixLift 457953
  have htrace : WordTrace (prefixWord ++ tailWord_457953) baseStart_457953 baseEnd_457953 := by
    simpa [prefixWord, tailWord_457953, baseEnd_457953] using wordTrace_append hprefix tailTrace_457953
  have hstable : (prefixWord ++ tailWord_457953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457953).length < 2 ^ (prefixWord ++ tailWord_457953).sum := by decide
  have hdescent : baseEnd_457953 < baseStart_457953 := by decide
  rcases family_descends (prefixWord ++ tailWord_457953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458018 : List Nat := [3, 3, 1, 1, 5, 1, 1, 6]
def baseStart_458018 : Nat := 118140960795 + 458018 * 2 ^ 59
def prefixEnd_458018 : Nat := 4983230072969 + 3 ^ 40 * 458018 * 2
def baseEnd_458018 : Nat := 34841982579421368321277

theorem tailTrace_458018 : CollatzResearch.WordTrace tailWord_458018 prefixEnd_458018 34841982579421368321277 := by
  unfold tailWord_458018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176322213671621022959677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11136859236457656061225805 4176322213671621022959677)
  ·
    refine ⟨1566120830126857883609879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4176322213671621022959677 1566120830126857883609879)
    ·
      refine ⟨2349181245190286825414819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1566120830126857883609879 2349181245190286825414819)
      ·
        refine ⟨3523771867785430238122229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2349181245190286825414819 3523771867785430238122229)
        ·
          refine ⟨330353612604884084823959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3523771867785430238122229 330353612604884084823959)
          ·
            refine ⟨495530418907326127235939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330353612604884084823959 495530418907326127235939)
            ·
              refine ⟨743295628360989190853909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495530418907326127235939 743295628360989190853909)
              ·
                refine ⟨34841982579421368321277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 743295628360989190853909 34841982579421368321277)
                ·
                  rfl

theorem cell21_458018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_458018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458018 prefixEnd_458018 := by exact prefixLift 458018
  have htrace : WordTrace (prefixWord ++ tailWord_458018) baseStart_458018 baseEnd_458018 := by
    simpa [prefixWord, tailWord_458018, baseEnd_458018] using wordTrace_append hprefix tailTrace_458018
  have hstable : (prefixWord ++ tailWord_458018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458018).length < 2 ^ (prefixWord ++ tailWord_458018).sum := by decide
  have hdescent : baseEnd_458018 < baseStart_458018 := by decide
  rcases family_descends (prefixWord ++ tailWord_458018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458049 : List Nat := [1, 2, 5, 2, 1, 2, 2, 3, 3]
def baseStart_458049 : Nat := 118140960795 + 458049 * 2 ^ 59
def prefixEnd_458049 : Nat := 4983230072969 + 3 ^ 40 * 458049 * 2
def baseEnd_458049 : Nat := 104533022360614939947101

theorem tailTrace_458049 : CollatzResearch.WordTrace tailWord_458049 prefixEnd_458049 104533022360614939947101 := by
  unfold tailWord_458049
  simp only [CollatzResearch.WordTrace]
  refine ⟨16706419517574176386217201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11137613011716117590811467 16706419517574176386217201)
  ·
    refine ⟨12529814638180632289662901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16706419517574176386217201 12529814638180632289662901)
    ·
      refine ⟨1174670122329434277155897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12529814638180632289662901 1174670122329434277155897)
      ·
        refine ⟨881002591747075707866923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1174670122329434277155897 881002591747075707866923)
        ·
          refine ⟨1321503887620613561800385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881002591747075707866923 1321503887620613561800385)
          ·
            refine ⟨991127915715460171350289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321503887620613561800385 991127915715460171350289)
            ·
              refine ⟨743345936786595128512717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991127915715460171350289 743345936786595128512717)
              ·
                refine ⟨278754726294973173192269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 743345936786595128512717 278754726294973173192269)
                ·
                  refine ⟨104533022360614939947101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278754726294973173192269 104533022360614939947101)
                  ·
                    rfl

theorem cell21_458049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_458049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458049 prefixEnd_458049 := by exact prefixLift 458049
  have htrace : WordTrace (prefixWord ++ tailWord_458049) baseStart_458049 baseEnd_458049 := by
    simpa [prefixWord, tailWord_458049, baseEnd_458049] using wordTrace_append hprefix tailTrace_458049
  have hstable : (prefixWord ++ tailWord_458049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458049).length < 2 ^ (prefixWord ++ tailWord_458049).sum := by decide
  have hdescent : baseEnd_458049 < baseStart_458049 := by decide
  rcases family_descends (prefixWord ++ tailWord_458049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458074 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_458074 : Nat := 118140960795 + 458074 * 2 ^ 59
def prefixEnd_458074 : Nat := 4983230072969 + 3 ^ 40 * 458074 * 2
def baseEnd_458074 : Nat := 104538727701220452030383

theorem tailTrace_458074 : CollatzResearch.WordTrace tailWord_458074 prefixEnd_458074 104538727701220452030383 := by
  unfold tailWord_458074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176832835620901413969319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11138220894989070437251517 4176832835620901413969319)
  ·
    refine ⟨6265249253431352120953979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4176832835620901413969319 6265249253431352120953979)
    ·
      refine ⟨9397873880147028181430969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6265249253431352120953979 9397873880147028181430969)
      ·
        refine ⟨7048405410110271136073227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9397873880147028181430969 7048405410110271136073227)
        ·
          refine ⟨10572608115165406704109841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048405410110271136073227 10572608115165406704109841)
          ·
            refine ⟨7929456086374055028082381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10572608115165406704109841 7929456086374055028082381)
            ·
              refine ⟨2973546032390270635530893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7929456086374055028082381 2973546032390270635530893)
              ·
                refine ⟨1115079762146351488324085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2973546032390270635530893 1115079762146351488324085)
                ·
                  refine ⟨104538727701220452030383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1115079762146351488324085 104538727701220452030383)
                  ·
                    rfl

theorem cell21_458074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_458074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458074 prefixEnd_458074 := by exact prefixLift 458074
  have htrace : WordTrace (prefixWord ++ tailWord_458074) baseStart_458074 baseEnd_458074 := by
    simpa [prefixWord, tailWord_458074, baseEnd_458074] using wordTrace_append hprefix tailTrace_458074
  have hstable : (prefixWord ++ tailWord_458074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458074).length < 2 ^ (prefixWord ++ tailWord_458074).sum := by decide
  have hdescent : baseEnd_458074 < baseStart_458074 := by decide
  rcases family_descends (prefixWord ++ tailWord_458074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458119 : List Nat := [1, 1, 4, 2, 2, 2, 9]
def baseStart_458119 : Nat := 118140960795 + 458119 * 2 ^ 59
def prefixEnd_458119 : Nat := 4983230072969 + 3 ^ 40 * 458119 * 2
def baseEnd_458119 : Nat := 11616555257145597086699

theorem tailTrace_458119 : CollatzResearch.WordTrace tailWord_458119 prefixEnd_458119 11616555257145597086699 := by
  unfold tailWord_458119
  simp only [CollatzResearch.WordTrace]
  refine ⟨16708972627320578341265411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11139315084880385560843607 16708972627320578341265411)
  ·
    refine ⟨25063458940980867511898117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16708972627320578341265411 25063458940980867511898117)
    ·
      refine ⟨4699398551433912658480897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25063458940980867511898117 4699398551433912658480897)
      ·
        refine ⟨3524548913575434493860673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4699398551433912658480897 3524548913575434493860673)
        ·
          refine ⟨2643411685181575870395505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3524548913575434493860673 2643411685181575870395505)
          ·
            refine ⟨1982558763886181902796629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2643411685181575870395505 1982558763886181902796629)
            ·
              refine ⟨11616555257145597086699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1982558763886181902796629 11616555257145597086699)
              ·
                rfl

theorem cell21_458119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 9].length) (baseStart_458119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458119 prefixEnd_458119 := by exact prefixLift 458119
  have htrace : WordTrace (prefixWord ++ tailWord_458119) baseStart_458119 baseEnd_458119 := by
    simpa [prefixWord, tailWord_458119, baseEnd_458119] using wordTrace_append hprefix tailTrace_458119
  have hstable : (prefixWord ++ tailWord_458119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458119).length < 2 ^ (prefixWord ++ tailWord_458119).sum := by decide
  have hdescent : baseEnd_458119 < baseStart_458119 := by decide
  rcases family_descends (prefixWord ++ tailWord_458119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458167 : List Nat := [1, 1, 3, 1, 3, 2, 2, 5, 3]
def baseStart_458167 : Nat := 118140960795 + 458167 * 2 ^ 59
def prefixEnd_458167 : Nat := 4983230072969 + 3 ^ 40 * 458167 * 2
def baseEnd_458167 : Nat := 104559951568272956980193

theorem tailTrace_458167 : CollatzResearch.WordTrace tailWord_458167 prefixEnd_458167 104559951568272956980193 := by
  unfold tailWord_458167
  simp only [CollatzResearch.WordTrace]
  refine ⟨16710723331146682539012755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11140482220764455026008503 16710723331146682539012755)
  ·
    refine ⟨25066084996720023808519133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16710723331146682539012755 25066084996720023808519133)
    ·
      refine ⟨9399781873770008928194675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25066084996720023808519133 9399781873770008928194675)
      ·
        refine ⟨14099672810655013392292013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9399781873770008928194675 14099672810655013392292013)
        ·
          refine ⟨5287377303995630022109505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14099672810655013392292013 5287377303995630022109505)
          ·
            refine ⟨3965532977996722516582129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5287377303995630022109505 3965532977996722516582129)
            ·
              refine ⟨2974149733497541887436597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3965532977996722516582129 2974149733497541887436597)
              ·
                refine ⟨278826537515394551947181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2974149733497541887436597 278826537515394551947181)
                ·
                  refine ⟨104559951568272956980193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278826537515394551947181 104559951568272956980193)
                  ·
                    rfl

theorem cell21_458167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 3].length) (baseStart_458167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458167 prefixEnd_458167 := by exact prefixLift 458167
  have htrace : WordTrace (prefixWord ++ tailWord_458167) baseStart_458167 baseEnd_458167 := by
    simpa [prefixWord, tailWord_458167, baseEnd_458167] using wordTrace_append hprefix tailTrace_458167
  have hstable : (prefixWord ++ tailWord_458167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458167).length < 2 ^ (prefixWord ++ tailWord_458167).sum := by decide
  have hdescent : baseEnd_458167 < baseStart_458167 := by decide
  rcases family_descends (prefixWord ++ tailWord_458167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458294 : List Nat := [5, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_458294 : Nat := 118140960795 + 458294 * 2 ^ 59
def prefixEnd_458294 : Nat := 4983230072969 + 3 ^ 40 * 458294 * 2
def baseEnd_458294 : Nat := 104588934698548958363267

theorem tailTrace_458294 : CollatzResearch.WordTrace tailWord_458294 prefixEnd_458294 104588934698548958363267 := by
  unfold tailWord_458294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044709712605411451805371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11143570267791055485923957 1044709712605411451805371)
  ·
    refine ⟨1567064568908117177708057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1044709712605411451805371 1567064568908117177708057)
    ·
      refine ⟨1175298426681087883281043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1567064568908117177708057 1175298426681087883281043)
      ·
        refine ⟨1762947640021631824921565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1175298426681087883281043 1762947640021631824921565)
        ·
          refine ⟨661105365008111934345587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1762947640021631824921565 661105365008111934345587)
          ·
            refine ⟨991658047512167901518381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661105365008111934345587 991658047512167901518381)
            ·
              refine ⟨371871767817062963069393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991658047512167901518381 371871767817062963069393)
              ·
                refine ⟨278903825862797222302045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371871767817062963069393 278903825862797222302045)
                ·
                  refine ⟨104588934698548958363267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278903825862797222302045 104588934698548958363267)
                  ·
                    rfl

theorem cell21_458294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_458294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458294 prefixEnd_458294 := by exact prefixLift 458294
  have htrace : WordTrace (prefixWord ++ tailWord_458294) baseStart_458294 baseEnd_458294 := by
    simpa [prefixWord, tailWord_458294, baseEnd_458294] using wordTrace_append hprefix tailTrace_458294
  have hstable : (prefixWord ++ tailWord_458294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458294).length < 2 ^ (prefixWord ++ tailWord_458294).sum := by decide
  have hdescent : baseEnd_458294 < baseStart_458294 := by decide
  rcases family_descends (prefixWord ++ tailWord_458294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458378 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_458378 : Nat := 118140960795 + 458378 * 2 ^ 59
def prefixEnd_458378 : Nat := 4983230072969 + 3 ^ 40 * 458378 * 2
def baseEnd_458378 : Nat := 104608104642983478963095

theorem tailTrace_458378 : CollatzResearch.WordTrace tailWord_458378 prefixEnd_458378 104608104642983478963095 := by
  unfold tailWord_458378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4179604783345566393735947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11145612755588177049962525 4179604783345566393735947)
  ·
    refine ⟨6269407175018349590603921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4179604783345566393735947 6269407175018349590603921)
    ·
      refine ⟨4702055381263762192952941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6269407175018349590603921 4702055381263762192952941)
      ·
        refine ⟨1763270767973910822357353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4702055381263762192952941 1763270767973910822357353)
        ·
          refine ⟨1322453075980433116768015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1763270767973910822357353 1322453075980433116768015)
          ·
            refine ⟨1983679613970649675152023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322453075980433116768015 1983679613970649675152023)
            ·
              refine ⟨2975519420955974512728035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983679613970649675152023 2975519420955974512728035)
              ·
                refine ⟨4463279131433961769092053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975519420955974512728035 4463279131433961769092053)
                ·
                  refine ⟨104608104642983478963095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4463279131433961769092053 104608104642983478963095)
                  ·
                    rfl

theorem cell21_458378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_458378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458378 prefixEnd_458378 := by exact prefixLift 458378
  have htrace : WordTrace (prefixWord ++ tailWord_458378) baseStart_458378 baseEnd_458378 := by
    simpa [prefixWord, tailWord_458378, baseEnd_458378] using wordTrace_append hprefix tailTrace_458378
  have hstable : (prefixWord ++ tailWord_458378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458378).length < 2 ^ (prefixWord ++ tailWord_458378).sum := by decide
  have hdescent : baseEnd_458378 < baseStart_458378 := by decide
  rcases family_descends (prefixWord ++ tailWord_458378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458426 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_458426 : Nat := 118140960795 + 458426 * 2 ^ 59
def prefixEnd_458426 : Nat := 4983230072969 + 3 ^ 40 * 458426 * 2
def baseEnd_458426 : Nat := 104619058896946062162997

theorem tailTrace_458426 : CollatzResearch.WordTrace tailWord_458426 prefixEnd_458426 104619058896946062162997 := by
  unfold tailWord_458426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180042459302092443172783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11146779891472246515127421 4180042459302092443172783)
  ·
    refine ⟨6270063688953138664759175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4180042459302092443172783 6270063688953138664759175)
    ·
      refine ⟨9405095533429707997138763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6270063688953138664759175 9405095533429707997138763)
      ·
        refine ⟨14107643300144561995708145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9405095533429707997138763 14107643300144561995708145)
        ·
          refine ⟨10580732475108421496781109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14107643300144561995708145 10580732475108421496781109)
          ·
            refine ⟨991943669541414515323229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10580732475108421496781109 991943669541414515323229)
            ·
              refine ⟨371978876078030443246211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991943669541414515323229 371978876078030443246211)
              ·
                refine ⟨557968314117045664869317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371978876078030443246211 557968314117045664869317)
                ·
                  refine ⟨104619058896946062162997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557968314117045664869317 104619058896946062162997)
                  ·
                    rfl

theorem cell21_458426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_458426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458426 prefixEnd_458426 := by exact prefixLift 458426
  have htrace : WordTrace (prefixWord ++ tailWord_458426) baseStart_458426 baseEnd_458426 := by
    simpa [prefixWord, tailWord_458426, baseEnd_458426] using wordTrace_append hprefix tailTrace_458426
  have hstable : (prefixWord ++ tailWord_458426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458426).length < 2 ^ (prefixWord ++ tailWord_458426).sum := by decide
  have hdescent : baseEnd_458426 < baseStart_458426 := by decide
  rcases family_descends (prefixWord ++ tailWord_458426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458468 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_458468 : Nat := 118140960795 + 458468 * 2 ^ 59
def prefixEnd_458468 : Nat := 4983230072969 + 3 ^ 40 * 458468 * 2
def baseEnd_458468 : Nat := 104628643869163322462911

theorem tailTrace_458468 : CollatzResearch.WordTrace tailWord_458468 prefixEnd_458468 104628643869163322462911 := by
  unfold tailWord_458468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8360850851528105472860029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11147801135370807297146705 8360850851528105472860029)
  ·
    refine ⟨3135319069323039552322511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8360850851528105472860029 3135319069323039552322511)
    ·
      refine ⟨4702978603984559328483767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3135319069323039552322511 4702978603984559328483767)
      ·
        refine ⟨7054467905976838992725651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4702978603984559328483767 7054467905976838992725651)
        ·
          refine ⟨10581701858965258489088477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7054467905976838992725651 10581701858965258489088477)
          ·
            refine ⟨3968138197111971933408179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10581701858965258489088477 3968138197111971933408179)
            ·
              refine ⟨5952207295667957900112269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968138197111971933408179 5952207295667957900112269)
              ·
                refine ⟨2232077735875484212542101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5952207295667957900112269 2232077735875484212542101)
                ·
                  refine ⟨104628643869163322462911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2232077735875484212542101 104628643869163322462911)
                  ·
                    rfl

theorem cell21_458468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_458468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458468 prefixEnd_458468 := by exact prefixLift 458468
  have htrace : WordTrace (prefixWord ++ tailWord_458468) baseStart_458468 baseEnd_458468 := by
    simpa [prefixWord, tailWord_458468, baseEnd_458468] using wordTrace_append hprefix tailTrace_458468
  have hstable : (prefixWord ++ tailWord_458468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458468).length < 2 ^ (prefixWord ++ tailWord_458468).sum := by decide
  have hdescent : baseEnd_458468 < baseStart_458468 := by decide
  rcases family_descends (prefixWord ++ tailWord_458468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458530 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_458530 : Nat := 118140960795 + 458530 * 2 ^ 59
def prefixEnd_458530 : Nat := 4983230072969 + 3 ^ 40 * 458530 * 2
def baseEnd_458530 : Nat := 104642793113864992429451

theorem tailTrace_458530 : CollatzResearch.WordTrace tailWord_458530 prefixEnd_458530 104642793113864992429451 := by
  unfold tailWord_458530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180990757207898883619261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11149308685887730356318029 4180990757207898883619261)
  ·
    refine ⟨1567871533952962081357223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4180990757207898883619261 1567871533952962081357223)
    ·
      refine ⟨2351807300929443122035835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1567871533952962081357223 2351807300929443122035835)
      ·
        refine ⟨3527710951394164683053753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351807300929443122035835 3527710951394164683053753)
        ·
          refine ⟨2645783213545623512290315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3527710951394164683053753 2645783213545623512290315)
          ·
            refine ⟨3968674820318435268435473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645783213545623512290315 3968674820318435268435473)
            ·
              refine ⟨2976506115238826451326605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3968674820318435268435473 2976506115238826451326605)
              ·
                refine ⟨1116189793214559919247477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2976506115238826451326605 1116189793214559919247477)
                ·
                  refine ⟨104642793113864992429451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1116189793214559919247477 104642793113864992429451)
                  ·
                    rfl

theorem cell21_458530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_458530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458530 prefixEnd_458530 := by exact prefixLift 458530
  have htrace : WordTrace (prefixWord ++ tailWord_458530) baseStart_458530 baseEnd_458530 := by
    simpa [prefixWord, tailWord_458530, baseEnd_458530] using wordTrace_append hprefix tailTrace_458530
  have hstable : (prefixWord ++ tailWord_458530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458530).length < 2 ^ (prefixWord ++ tailWord_458530).sum := by decide
  have hdescent : baseEnd_458530 < baseStart_458530 := by decide
  rcases family_descends (prefixWord ++ tailWord_458530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458578 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_458578 : Nat := 118140960795 + 458578 * 2 ^ 59
def prefixEnd_458578 : Nat := 4983230072969 + 3 ^ 40 * 458578 * 2
def baseEnd_458578 : Nat := 104653747367827575629353

theorem tailTrace_458578 : CollatzResearch.WordTrace tailWord_458578 prefixEnd_458578 104653747367827575629353 := by
  unfold tailWord_458578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181428433164424933056097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11150475821771799821482925 4181428433164424933056097)
  ·
    refine ⟨3136071324873318699792073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4181428433164424933056097 3136071324873318699792073)
    ·
      refine ⟨2352053493654989024844055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3136071324873318699792073 2352053493654989024844055)
      ·
        refine ⟨3528080240482483537266083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352053493654989024844055 3528080240482483537266083)
        ·
          refine ⟨5292120360723725305899125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3528080240482483537266083 5292120360723725305899125)
          ·
            refine ⟨496136283817849247428043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5292120360723725305899125 496136283817849247428043)
            ·
              refine ⟨744204425726773871142065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496136283817849247428043 744204425726773871142065)
              ·
                refine ⟨558153319295080403356549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744204425726773871142065 558153319295080403356549)
                ·
                  refine ⟨104653747367827575629353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 558153319295080403356549 104653747367827575629353)
                  ·
                    rfl

theorem cell21_458578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_458578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458578 prefixEnd_458578 := by exact prefixLift 458578
  have htrace : WordTrace (prefixWord ++ tailWord_458578) baseStart_458578 baseEnd_458578 := by
    simpa [prefixWord, tailWord_458578, baseEnd_458578] using wordTrace_append hprefix tailTrace_458578
  have hstable : (prefixWord ++ tailWord_458578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458578).length < 2 ^ (prefixWord ++ tailWord_458578).sum := by decide
  have hdescent : baseEnd_458578 < baseStart_458578 := by decide
  rcases family_descends (prefixWord ++ tailWord_458578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458646 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_458646 : Nat := 118140960795 + 458646 * 2 ^ 59
def prefixEnd_458646 : Nat := 4983230072969 + 3 ^ 40 * 458646 * 2
def baseEnd_458646 : Nat := 104669265894274568495881

theorem tailTrace_458646 : CollatzResearch.WordTrace tailWord_458646 prefixEnd_458646 104669265894274568495881 := by
  unfold tailWord_458646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045512118525709209106237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11152129264274231563799861 1045512118525709209106237)
  ·
    refine ⟨392067044447140953414839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1045512118525709209106237 392067044447140953414839)
    ·
      refine ⟨588100566670711430122259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392067044447140953414839 588100566670711430122259)
      ·
        refine ⟨882150850006067145183389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588100566670711430122259 882150850006067145183389)
        ·
          refine ⟨330806568752275179443771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 882150850006067145183389 330806568752275179443771)
          ·
            refine ⟨496209853128412769165657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330806568752275179443771 496209853128412769165657)
            ·
              refine ⟨372157389846309576874243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496209853128412769165657 372157389846309576874243)
              ·
                refine ⟨558236084769464365311365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372157389846309576874243 558236084769464365311365)
                ·
                  refine ⟨104669265894274568495881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 558236084769464365311365 104669265894274568495881)
                  ·
                    rfl

theorem cell21_458646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_458646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458646 prefixEnd_458646 := by exact prefixLift 458646
  have htrace : WordTrace (prefixWord ++ tailWord_458646) baseStart_458646 baseEnd_458646 := by
    simpa [prefixWord, tailWord_458646, baseEnd_458646] using wordTrace_append hprefix tailTrace_458646
  have hstable : (prefixWord ++ tailWord_458646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458646).length < 2 ^ (prefixWord ++ tailWord_458646).sum := by decide
  have hdescent : baseEnd_458646 < baseStart_458646 := by decide
  rcases family_descends (prefixWord ++ tailWord_458646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458733 : List Nat := [1, 5, 1, 4, 1, 1, 2, 3, 3]
def baseStart_458733 : Nat := 118140960795 + 458733 * 2 ^ 59
def prefixEnd_458733 : Nat := 4983230072969 + 3 ^ 40 * 458733 * 2
def baseEnd_458733 : Nat := 104689120479581750545703

theorem tailTrace_458733 : CollatzResearch.WordTrace tailWord_458733 prefixEnd_458733 104689120479581750545703 := by
  unfold tailWord_458733
  simp only [CollatzResearch.WordTrace]
  refine ⟨16731367047096161204116853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11154244698064107469411235 16731367047096161204116853)
  ·
    refine ⟨1568565660665265112885955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16731367047096161204116853 1568565660665265112885955)
    ·
      refine ⟨2352848490997897669328933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568565660665265112885955 2352848490997897669328933)
      ·
        refine ⟨441159092062105812999175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2352848490997897669328933 441159092062105812999175)
        ·
          refine ⟨661738638093158719498763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441159092062105812999175 661738638093158719498763)
          ·
            refine ⟨992607957139738079248145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661738638093158719498763 992607957139738079248145)
            ·
              refine ⟨744455967854803559436109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992607957139738079248145 744455967854803559436109)
              ·
                refine ⟨279170987945551334788541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 744455967854803559436109 279170987945551334788541)
                ·
                  refine ⟨104689120479581750545703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279170987945551334788541 104689120479581750545703)
                  ·
                    rfl

theorem cell21_458733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_458733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458733 prefixEnd_458733 := by exact prefixLift 458733
  have htrace : WordTrace (prefixWord ++ tailWord_458733) baseStart_458733 baseEnd_458733 := by
    simpa [prefixWord, tailWord_458733, baseEnd_458733] using wordTrace_append hprefix tailTrace_458733
  have hstable : (prefixWord ++ tailWord_458733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458733).length < 2 ^ (prefixWord ++ tailWord_458733).sum := by decide
  have hdescent : baseEnd_458733 < baseStart_458733 := by decide
  rcases family_descends (prefixWord ++ tailWord_458733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458978 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_458978 : Nat := 118140960795 + 458978 * 2 ^ 59
def prefixEnd_458978 : Nat := 4983230072969 + 3 ^ 40 * 458978 * 2
def baseEnd_458978 : Nat := 104745032817515768961869

theorem tailTrace_458978 : CollatzResearch.WordTrace tailWord_458978 prefixEnd_458978 104745032817515768961869 := by
  unfold tailWord_458978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4185075732802142011696397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11160201954139045364523725 4185075732802142011696397)
  ·
    refine ⟨1569403399800803254386149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4185075732802142011696397 1569403399800803254386149)
    ·
      refine ⟨294263137462650610197403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1569403399800803254386149 294263137462650610197403)
      ·
        refine ⟨441394706193975915296105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294263137462650610197403 441394706193975915296105)
        ·
          refine ⟨331046029645481936472079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441394706193975915296105 331046029645481936472079)
          ·
            refine ⟨496569044468222904708119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331046029645481936472079 496569044468222904708119)
            ·
              refine ⟨744853566702334357062179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496569044468222904708119 744853566702334357062179)
              ·
                refine ⟨1117280350053501535593269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744853566702334357062179 1117280350053501535593269)
                ·
                  refine ⟨104745032817515768961869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1117280350053501535593269 104745032817515768961869)
                  ·
                    rfl

theorem cell21_458978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_458978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_458978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_458978 prefixEnd_458978 := by exact prefixLift 458978
  have htrace : WordTrace (prefixWord ++ tailWord_458978) baseStart_458978 baseEnd_458978 := by
    simpa [prefixWord, tailWord_458978, baseEnd_458978] using wordTrace_append hprefix tailTrace_458978
  have hstable : (prefixWord ++ tailWord_458978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458978).length < 2 ^ (prefixWord ++ tailWord_458978).sum := by decide
  have hdescent : baseEnd_458978 < baseStart_458978 := by decide
  rcases family_descends (prefixWord ++ tailWord_458978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459037 : List Nat := [1, 4, 2, 3, 2, 2, 2, 2, 3]
def baseStart_459037 : Nat := 118140960795 + 459037 * 2 ^ 59
def prefixEnd_459037 : Nat := 4983230072969 + 3 ^ 40 * 459037 * 2
def baseEnd_459037 : Nat := 104758497421344777478415

theorem tailTrace_459037 : CollatzResearch.WordTrace tailWord_459037 prefixEnd_459037 104758497421344777478415 := by
  unfold tailWord_459037
  simp only [CollatzResearch.WordTrace]
  refine ⟨16742454837994821123183365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11161636558663214082122243 16742454837994821123183365)
  ·
    refine ⟨3139210282124028960596881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16742454837994821123183365 3139210282124028960596881)
    ·
      refine ⟨2354407711593021720447661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3139210282124028960596881 2354407711593021720447661)
      ·
        refine ⟨882902891847383145167873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2354407711593021720447661 882902891847383145167873)
        ·
          refine ⟨662177168885537358875905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882902891847383145167873 662177168885537358875905)
          ·
            refine ⟨496632876664153019156929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662177168885537358875905 496632876664153019156929)
            ·
              refine ⟨372474657498114764367697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496632876664153019156929 372474657498114764367697)
              ·
                refine ⟨279355993123586073275773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372474657498114764367697 279355993123586073275773)
                ·
                  refine ⟨104758497421344777478415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279355993123586073275773 104758497421344777478415)
                  ·
                    rfl

theorem cell21_459037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_459037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459037 prefixEnd_459037 := by exact prefixLift 459037
  have htrace : WordTrace (prefixWord ++ tailWord_459037) baseStart_459037 baseEnd_459037 := by
    simpa [prefixWord, tailWord_459037, baseEnd_459037] using wordTrace_append hprefix tailTrace_459037
  have hstable : (prefixWord ++ tailWord_459037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459037).length < 2 ^ (prefixWord ++ tailWord_459037).sum := by decide
  have hdescent : baseEnd_459037 < baseStart_459037 := by decide
  rcases family_descends (prefixWord ++ tailWord_459037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459048 : List Nat := [2, 1, 5, 1, 3, 2, 1, 6]
def baseStart_459048 : Nat := 118140960795 + 459048 * 2 ^ 59
def prefixEnd_459048 : Nat := 4983230072969 + 3 ^ 40 * 459048 * 2
def baseEnd_459048 : Nat := 34920335923737067598353

theorem tailTrace_459048 : CollatzResearch.WordTrace tailWord_459048 prefixEnd_459048 34920335923737067598353 := by
  unfold tailWord_459048
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371428020477485000916899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11161904027303313334555865 8371428020477485000916899)
  ·
    refine ⟨12557142030716227501375349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8371428020477485000916899 12557142030716227501375349)
    ·
      refine ⟨1177232065379646328253939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12557142030716227501375349 1177232065379646328253939)
      ·
        refine ⟨1765848098069469492380909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177232065379646328253939 1765848098069469492380909)
        ·
          refine ⟨662193036776051059642841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1765848098069469492380909 662193036776051059642841)
          ·
            refine ⟨496644777582038294732131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662193036776051059642841 496644777582038294732131)
            ·
              refine ⟨744967166373057442098197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496644777582038294732131 744967166373057442098197)
              ·
                refine ⟨34920335923737067598353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 744967166373057442098197 34920335923737067598353)
                ·
                  rfl

theorem cell21_459048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_459048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459048 prefixEnd_459048 := by exact prefixLift 459048
  have htrace : WordTrace (prefixWord ++ tailWord_459048) baseStart_459048 baseEnd_459048 := by
    simpa [prefixWord, tailWord_459048, baseEnd_459048] using wordTrace_append hprefix tailTrace_459048
  have hstable : (prefixWord ++ tailWord_459048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459048).length < 2 ^ (prefixWord ++ tailWord_459048).sum := by decide
  have hdescent : baseEnd_459048 < baseStart_459048 := by decide
  rcases family_descends (prefixWord ++ tailWord_459048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459158 : List Nat := [5, 3, 1, 2, 1, 1, 2, 6]
def baseStart_459158 : Nat := 118140960795 + 459158 * 2 ^ 59
def prefixEnd_459158 : Nat := 4983230072969 + 3 ^ 40 * 459158 * 2
def baseEnd_459158 : Nat := 34928703756625151987167

theorem tailTrace_459158 : CollatzResearch.WordTrace tailWord_459158 prefixEnd_459158 34928703756625151987167 := by
  unfold tailWord_459158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046679254409778674271133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11164578713704305858892085 1046679254409778674271133)
  ·
    refine ⟨392504720403667002851675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1046679254409778674271133 392504720403667002851675)
    ·
      refine ⟨588757080605500504277513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392504720403667002851675 588757080605500504277513)
      ·
        refine ⟨441567810454125378208135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588757080605500504277513 441567810454125378208135)
        ·
          refine ⟨662351715681188067312203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441567810454125378208135 662351715681188067312203)
          ·
            refine ⟨993527573521782100968305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662351715681188067312203 993527573521782100968305)
            ·
              refine ⟨745145680141336575726229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993527573521782100968305 745145680141336575726229)
              ·
                refine ⟨34928703756625151987167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 745145680141336575726229 34928703756625151987167)
                ·
                  rfl

theorem cell21_459158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_459158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459158 prefixEnd_459158 := by exact prefixLift 459158
  have htrace : WordTrace (prefixWord ++ tailWord_459158) baseStart_459158 baseEnd_459158 := by
    simpa [prefixWord, tailWord_459158, baseEnd_459158] using wordTrace_append hprefix tailTrace_459158
  have hstable : (prefixWord ++ tailWord_459158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459158).length < 2 ^ (prefixWord ++ tailWord_459158).sum := by decide
  have hdescent : baseEnd_459158 < baseStart_459158 := by decide
  rcases family_descends (prefixWord ++ tailWord_459158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459180 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_459180 : Nat := 118140960795 + 459180 * 2 ^ 59
def prefixEnd_459180 : Nat := 4983230072969 + 3 ^ 40 * 459180 * 2
def baseEnd_459180 : Nat := 104791131969608306594789

theorem tailTrace_459180 : CollatzResearch.WordTrace tailWord_459180 prefixEnd_459180 104791131969608306594789 := by
  unfold tailWord_459180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373835238238378272819497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11165113650984504363759329 8373835238238378272819497)
  ·
    refine ⟨6280376428678783704614623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8373835238238378272819497 6280376428678783704614623)
    ·
      refine ⟨9420564643018175556921935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6280376428678783704614623 9420564643018175556921935)
      ·
        refine ⟨14130846964527263335382903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9420564643018175556921935 14130846964527263335382903)
        ·
          refine ⟨21196270446790895003074355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14130846964527263335382903 21196270446790895003074355)
          ·
            refine ⟨31794405670186342504611533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21196270446790895003074355 31794405670186342504611533)
            ·
              refine ⟨11922902126319878439229325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31794405670186342504611533 11922902126319878439229325)
              ·
                refine ⟨4471088297369954414710997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11922902126319878439229325 4471088297369954414710997)
                ·
                  refine ⟨104791131969608306594789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4471088297369954414710997 104791131969608306594789)
                  ·
                    rfl

theorem cell21_459180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_459180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459180 prefixEnd_459180 := by exact prefixLift 459180
  have htrace : WordTrace (prefixWord ++ tailWord_459180) baseStart_459180 baseEnd_459180 := by
    simpa [prefixWord, tailWord_459180, baseEnd_459180] using wordTrace_append hprefix tailTrace_459180
  have hstable : (prefixWord ++ tailWord_459180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459180).length < 2 ^ (prefixWord ++ tailWord_459180).sum := by decide
  have hdescent : baseEnd_459180 < baseStart_459180 := by decide
  rcases family_descends (prefixWord ++ tailWord_459180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459256 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_459256 : Nat := 118140960795 + 459256 * 2 ^ 59
def prefixEnd_459256 : Nat := 4983230072969 + 3 ^ 40 * 459256 * 2
def baseEnd_459256 : Nat := 104808476205049063327967

theorem tailTrace_459256 : CollatzResearch.WordTrace tailWord_459256 prefixEnd_459256 104808476205049063327967 := by
  unfold tailWord_459256
  simp only [CollatzResearch.WordTrace]
  refine ⟨8375221212100710762702811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11166961616134281016937081 8375221212100710762702811)
  ·
    refine ⟨12562831818151066144054217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8375221212100710762702811 12562831818151066144054217)
    ·
      refine ⟨9422123863613299608040663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12562831818151066144054217 9422123863613299608040663)
      ·
        refine ⟨14133185795419949412060995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9422123863613299608040663 14133185795419949412060995)
        ·
          refine ⟨21199778693129924118091493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14133185795419949412060995 21199778693129924118091493)
          ·
            refine ⟨3974958504961860772142155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21199778693129924118091493 3974958504961860772142155)
            ·
              refine ⟨5962437757442791158213233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974958504961860772142155 5962437757442791158213233)
              ·
                refine ⟨4471828318082093368659925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962437757442791158213233 4471828318082093368659925)
                ·
                  refine ⟨104808476205049063327967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4471828318082093368659925 104808476205049063327967)
                  ·
                    rfl

theorem cell21_459256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_459256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459256 prefixEnd_459256 := by exact prefixLift 459256
  have htrace : WordTrace (prefixWord ++ tailWord_459256) baseStart_459256 baseEnd_459256 := by
    simpa [prefixWord, tailWord_459256, baseEnd_459256] using wordTrace_append hprefix tailTrace_459256
  have hstable : (prefixWord ++ tailWord_459256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459256).length < 2 ^ (prefixWord ++ tailWord_459256).sum := by decide
  have hdescent : baseEnd_459256 < baseStart_459256 := by decide
  rcases family_descends (prefixWord ++ tailWord_459256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459304 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_459304 : Nat := 118140960795 + 459304 * 2 ^ 59
def prefixEnd_459304 : Nat := 4983230072969 + 3 ^ 40 * 459304 * 2
def baseEnd_459304 : Nat := 104819430459011646527869

theorem tailTrace_459304 : CollatzResearch.WordTrace tailWord_459304 prefixEnd_459304 104819430459011646527869 := by
  unfold tailWord_459304
  simp only [CollatzResearch.WordTrace]
  refine ⟨8376096564013762861576483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11168128752018350482101977 8376096564013762861576483)
  ·
    refine ⟨12564144846020644292364725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8376096564013762861576483 12564144846020644292364725)
    ·
      refine ⟨1177888579314435402409193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12564144846020644292364725 1177888579314435402409193)
      ·
        refine ⟨883416434485826551806895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177888579314435402409193 883416434485826551806895)
        ·
          refine ⟨1325124651728739827710343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883416434485826551806895 1325124651728739827710343)
          ·
            refine ⟨1987686977593109741565515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325124651728739827710343 1987686977593109741565515)
            ·
              refine ⟨2981530466389664612348273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987686977593109741565515 2981530466389664612348273)
              ·
                refine ⟨2236147849792248459261205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2981530466389664612348273 2236147849792248459261205)
                ·
                  refine ⟨104819430459011646527869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2236147849792248459261205 104819430459011646527869)
                  ·
                    rfl

theorem cell21_459304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_459304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_459304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_459304 prefixEnd_459304 := by exact prefixLift 459304
  have htrace : WordTrace (prefixWord ++ tailWord_459304) baseStart_459304 baseEnd_459304 := by
    simpa [prefixWord, tailWord_459304, baseEnd_459304] using wordTrace_append hprefix tailTrace_459304
  have hstable : (prefixWord ++ tailWord_459304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459304).length < 2 ^ (prefixWord ++ tailWord_459304).sum := by decide
  have hdescent : baseEnd_459304 < baseStart_459304 := by decide
  rcases family_descends (prefixWord ++ tailWord_459304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
