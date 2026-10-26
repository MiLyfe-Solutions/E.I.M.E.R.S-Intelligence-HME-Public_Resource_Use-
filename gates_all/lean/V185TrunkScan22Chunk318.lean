import V185TrunkScan22Chunk317

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2838943 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 1, 7]
def baseStart_2838943 : Nat := 118140960795 + 2838943 * 2 ^ 59
def prefixEnd_2838943 : Nat := 4983230072969 + 3 ^ 40 * 2838943 * 2
def baseEnd_2838943 : Nat := 971828206478127570770963

theorem tailTrace_2838943 : CollatzResearch.WordTrace tailWord_2838943 prefixEnd_2838943 971828206478127570770963 := by
  unfold tailWord_2838943
  simp only [CollatzResearch.WordTrace]
  refine ⟨103544757754001838708401483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69029838502667892472267655 103544757754001838708401483)
  ·
    refine ⟨155317136631002758062602225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103544757754001838708401483 155317136631002758062602225)
    ·
      refine ⟨116487852473252068546951669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155317136631002758062602225 116487852473252068546951669)
      ·
        refine ⟨10920736169367381426276719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116487852473252068546951669 10920736169367381426276719)
        ·
          refine ⟨16381104254051072139415079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10920736169367381426276719 16381104254051072139415079)
          ·
            refine ⟨24571656381076608209122619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16381104254051072139415079 24571656381076608209122619)
            ·
              refine ⟨36857484571614912313683929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24571656381076608209122619 36857484571614912313683929)
              ·
                refine ⟨27643113428711184235262947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36857484571614912313683929 27643113428711184235262947)
                ·
                  refine ⟨41464670143066776352894421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27643113428711184235262947 41464670143066776352894421)
                  ·
                    refine ⟨971828206478127570770963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41464670143066776352894421 971828206478127570770963)
                    ·
                      rfl

theorem cell22_2838943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_2838943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838943 prefixEnd_2838943 := by exact prefixLift 2838943
  have htrace : WordTrace (prefixWord ++ tailWord_2838943) baseStart_2838943 baseEnd_2838943 := by
    simpa [prefixWord, tailWord_2838943, baseEnd_2838943] using wordTrace_append hprefix tailTrace_2838943
  have hstable : (prefixWord ++ tailWord_2838943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838943).length < 2 ^ (prefixWord ++ tailWord_2838943).sum := by decide
  have hdescent : baseEnd_2838943 < baseStart_2838943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839005 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2839005 : Nat := 118140960795 + 2839005 * 2 ^ 59
def prefixEnd_2839005 : Nat := 4983230072969 + 3 ^ 40 * 2839005 * 2
def baseEnd_2839005 : Nat := 971849430345180075720773

theorem tailTrace_2839005 : CollatzResearch.WordTrace tailWord_2839005 prefixEnd_2839005 971849430345180075720773 := by
  unfold tailWord_2839005
  simp only [CollatzResearch.WordTrace]
  refine ⟨103547019079777223297158469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69031346053184815531438979 103547019079777223297158469)
  ·
    refine ⟨19415066077458229368217213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103547019079777223297158469 19415066077458229368217213)
    ·
      refine ⟨7280649779046836013081455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19415066077458229368217213 7280649779046836013081455)
      ·
        refine ⟨10920974668570254019622183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7280649779046836013081455 10920974668570254019622183)
        ·
          refine ⟨16381462002855381029433275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10920974668570254019622183 16381462002855381029433275)
          ·
            refine ⟨24572193004283071544149913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16381462002855381029433275 24572193004283071544149913)
            ·
              refine ⟨18429144753212303658112435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24572193004283071544149913 18429144753212303658112435)
              ·
                refine ⟨27643717129818455487168653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18429144753212303658112435 27643717129818455487168653)
                ·
                  refine ⟨10366393923681920807688245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27643717129818455487168653 10366393923681920807688245)
                  ·
                    refine ⟨971849430345180075720773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10366393923681920807688245 971849430345180075720773)
                    ·
                      rfl

theorem cell22_2839005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2839005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839005 prefixEnd_2839005 := by exact prefixLift 2839005
  have htrace : WordTrace (prefixWord ++ tailWord_2839005) baseStart_2839005 baseEnd_2839005 := by
    simpa [prefixWord, tailWord_2839005, baseEnd_2839005] using wordTrace_append hprefix tailTrace_2839005
  have hstable : (prefixWord ++ tailWord_2839005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839005).length < 2 ^ (prefixWord ++ tailWord_2839005).sum := by decide
  have hdescent : baseEnd_2839005 < baseStart_2839005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839007 : List Nat := [1, 1, 2, 3, 3, 2, 3, 3, 4]
def baseStart_2839007 : Nat := 118140960795 + 2839007 * 2 ^ 59
def prefixEnd_2839007 : Nat := 4983230072969 + 3 ^ 40 * 2839007 * 2
def baseEnd_2839007 : Nat := 323950038328684245723589

theorem tailTrace_2839007 : CollatzResearch.WordTrace tailWord_2839007 prefixEnd_2839007 323950038328684245723589 := by
  unfold tailWord_2839007
  simp only [CollatzResearch.WordTrace]
  refine ⟨103547092025769977638731275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69031394683846651759154183 103547092025769977638731275)
  ·
    refine ⟨155320638038654966458096913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103547092025769977638731275 155320638038654966458096913)
    ·
      refine ⟨116490478528991224843572685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155320638038654966458096913 116490478528991224843572685)
      ·
        refine ⟨43683929448371709316339757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116490478528991224843572685 43683929448371709316339757)
        ·
          refine ⟨16381473543139390993627409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43683929448371709316339757 16381473543139390993627409)
          ·
            refine ⟨12286105157354543245220557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16381473543139390993627409 12286105157354543245220557)
            ·
              refine ⟨4607289434007953716957709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12286105157354543245220557 4607289434007953716957709)
              ·
                refine ⟨1727733537752982643859141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4607289434007953716957709 1727733537752982643859141)
                ·
                  refine ⟨323950038328684245723589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727733537752982643859141 323950038328684245723589)
                  ·
                    rfl

theorem cell22_2839007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 4].length) (baseStart_2839007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839007 prefixEnd_2839007 := by exact prefixLift 2839007
  have htrace : WordTrace (prefixWord ++ tailWord_2839007) baseStart_2839007 baseEnd_2839007 := by
    simpa [prefixWord, tailWord_2839007, baseEnd_2839007] using wordTrace_append hprefix tailTrace_2839007
  have hstable : (prefixWord ++ tailWord_2839007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839007).length < 2 ^ (prefixWord ++ tailWord_2839007).sum := by decide
  have hdescent : baseEnd_2839007 < baseStart_2839007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839020 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_2839020 : Nat := 118140960795 + 2839020 * 2 ^ 59
def prefixEnd_2839020 : Nat := 4983230072969 + 3 ^ 40 * 2839020 * 2
def baseEnd_2839020 : Nat := 971854565151725036595727

theorem tailTrace_2839020 : CollatzResearch.WordTrace tailWord_2839020 prefixEnd_2839020 971854565151725036595727 := by
  unfold tailWord_2839020
  simp only [CollatzResearch.WordTrace]
  refine ⟨51773783087361440429477257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69031710783148587239303009 51773783087361440429477257)
  ·
    refine ⟨38830337315521080322107943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51773783087361440429477257 38830337315521080322107943)
    ·
      refine ⟨58245505973281620483161915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38830337315521080322107943 58245505973281620483161915)
      ·
        refine ⟨87368258959922430724742873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58245505973281620483161915 87368258959922430724742873)
        ·
          refine ⟨65526194219941823043557155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87368258959922430724742873 65526194219941823043557155)
          ·
            refine ⟨98289291329912734565335733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65526194219941823043557155 98289291329912734565335733)
            ·
              refine ⟨9214621062179318865500225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98289291329912734565335733 9214621062179318865500225)
              ·
                refine ⟨6910965796634489149125169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9214621062179318865500225 6910965796634489149125169)
                ·
                  refine ⟨5183224347475866861843877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6910965796634489149125169 5183224347475866861843877)
                  ·
                    refine ⟨971854565151725036595727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5183224347475866861843877 971854565151725036595727)
                    ·
                      rfl

theorem cell22_2839020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_2839020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839020 prefixEnd_2839020 := by exact prefixLift 2839020
  have htrace : WordTrace (prefixWord ++ tailWord_2839020) baseStart_2839020 baseEnd_2839020 := by
    simpa [prefixWord, tailWord_2839020, baseEnd_2839020] using wordTrace_append hprefix tailTrace_2839020
  have hstable : (prefixWord ++ tailWord_2839020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839020).length < 2 ^ (prefixWord ++ tailWord_2839020).sum := by decide
  have hdescent : baseEnd_2839020 < baseStart_2839020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839022 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_2839022 : Nat := 118140960795 + 2839022 * 2 ^ 59
def prefixEnd_2839022 : Nat := 4983230072969 + 3 ^ 40 * 2839022 * 2
def baseEnd_2839022 : Nat := 971855249792597698045721

theorem tailTrace_2839022 : CollatzResearch.WordTrace tailWord_2839022 prefixEnd_2839022 971855249792597698045721 := by
  unfold tailWord_2839022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12943454890089454400065915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69031759413810423467018213 12943454890089454400065915)
  ·
    refine ⟨19415182335134181600098873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12943454890089454400065915 19415182335134181600098873)
    ·
      refine ⟨14561386751350636200074155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19415182335134181600098873 14561386751350636200074155)
      ·
        refine ⟨21842080127025954300111233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14561386751350636200074155 21842080127025954300111233)
        ·
          refine ⟨16381560095269465725083425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21842080127025954300111233 16381560095269465725083425)
          ·
            refine ⟨12286170071452099293812569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16381560095269465725083425 12286170071452099293812569)
            ·
              refine ⟨9214627553589074470359427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12286170071452099293812569 9214627553589074470359427)
              ·
                refine ⟨13821941330383611705539141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9214627553589074470359427 13821941330383611705539141)
                ·
                  refine ⟨2591613999446927194788589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13821941330383611705539141 2591613999446927194788589)
                  ·
                    refine ⟨971855249792597698045721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2591613999446927194788589 971855249792597698045721)
                    ·
                      rfl

theorem cell22_2839022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_2839022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839022 prefixEnd_2839022 := by exact prefixLift 2839022
  have htrace : WordTrace (prefixWord ++ tailWord_2839022) baseStart_2839022 baseEnd_2839022 := by
    simpa [prefixWord, tailWord_2839022, baseEnd_2839022] using wordTrace_append hprefix tailTrace_2839022
  have hstable : (prefixWord ++ tailWord_2839022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839022).length < 2 ^ (prefixWord ++ tailWord_2839022).sum := by decide
  have hdescent : baseEnd_2839022 < baseStart_2839022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839095 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 2, 5]
def baseStart_2839095 : Nat := 118140960795 + 2839095 * 2 ^ 59
def prefixEnd_2839095 : Nat := 4983230072969 + 3 ^ 40 * 2839095 * 2
def baseEnd_2839095 : Nat := 971880239184449840970497

theorem tailTrace_2839095 : CollatzResearch.WordTrace tailWord_2839095 prefixEnd_2839095 971880239184449840970497 := by
  unfold tailWord_2839095
  simp only [CollatzResearch.WordTrace]
  refine ⟨103550301649451168667934739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69033534432967445778623159 103550301649451168667934739)
  ·
    refine ⟨155325452474176753001902109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103550301649451168667934739 155325452474176753001902109)
    ·
      refine ⟨58247044677816282375713291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155325452474176753001902109 58247044677816282375713291)
      ·
        refine ⟨87370567016724423563569937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58247044677816282375713291 87370567016724423563569937)
        ·
          refine ⟨65527925262543317672677453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87370567016724423563569937 65527925262543317672677453)
          ·
            refine ⟨24572971973453744127254045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65527925262543317672677453 24572971973453744127254045)
            ·
              refine ⟨9214864490045154047720267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24572971973453744127254045 9214864490045154047720267)
              ·
                refine ⟨13822296735067731071580401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9214864490045154047720267 13822296735067731071580401)
                ·
                  refine ⟨10366722551300798303685301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13822296735067731071580401 10366722551300798303685301)
                  ·
                    refine ⟨971880239184449840970497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10366722551300798303685301 971880239184449840970497)
                    ·
                      rfl

theorem cell22_2839095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_2839095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839095 prefixEnd_2839095 := by exact prefixLift 2839095
  have htrace : WordTrace (prefixWord ++ tailWord_2839095) baseStart_2839095 baseEnd_2839095 := by
    simpa [prefixWord, tailWord_2839095, baseEnd_2839095] using wordTrace_append hprefix tailTrace_2839095
  have hstable : (prefixWord ++ tailWord_2839095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839095).length < 2 ^ (prefixWord ++ tailWord_2839095).sum := by decide
  have hdescent : baseEnd_2839095 < baseStart_2839095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839127 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 1, 4]
def baseStart_2839127 : Nat := 118140960795 + 2839127 * 2 ^ 59
def prefixEnd_2839127 : Nat := 4983230072969 + 3 ^ 40 * 2839127 * 2
def baseEnd_2839127 : Nat := 971891193438412424170399

theorem tailTrace_2839127 : CollatzResearch.WordTrace tailWord_2839127 prefixEnd_2839127 971891193438412424170399 := by
  unfold tailWord_2839127
  simp only [CollatzResearch.WordTrace]
  refine ⟨103551468785335238133099635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69034312523556825422066423 103551468785335238133099635)
  ·
    refine ⟨155327203178002857199649453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103551468785335238133099635 155327203178002857199649453)
    ·
      refine ⟨58247701191751071449868545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155327203178002857199649453 58247701191751071449868545)
      ·
        refine ⟨43685775893813303587401409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58247701191751071449868545 43685775893813303587401409)
        ·
          refine ⟨32764331920359977690551057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43685775893813303587401409 32764331920359977690551057)
          ·
            refine ⟨24573248940269983267913293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32764331920359977690551057 24573248940269983267913293)
            ·
              refine ⟨9214968352601243725467485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24573248940269983267913293 9214968352601243725467485)
              ·
                refine ⟨3455613132225466397050307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9214968352601243725467485 3455613132225466397050307)
                ·
                  refine ⟨5183419698338199595575461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455613132225466397050307 5183419698338199595575461)
                  ·
                    refine ⟨971891193438412424170399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5183419698338199595575461 971891193438412424170399)
                    ·
                      rfl

theorem cell22_2839127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_2839127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839127 prefixEnd_2839127 := by exact prefixLift 2839127
  have htrace : WordTrace (prefixWord ++ tailWord_2839127) baseStart_2839127 baseEnd_2839127 := by
    simpa [prefixWord, tailWord_2839127, baseEnd_2839127] using wordTrace_append hprefix tailTrace_2839127
  have hstable : (prefixWord ++ tailWord_2839127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839127).length < 2 ^ (prefixWord ++ tailWord_2839127).sum := by decide
  have hdescent : baseEnd_2839127 < baseStart_2839127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839155 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 6, 4]
def baseStart_2839155 : Nat := 118140960795 + 2839155 * 2 ^ 59
def prefixEnd_2839155 : Nat := 4983230072969 + 3 ^ 40 * 2839155 * 2
def baseEnd_2839155 : Nat := 971900778410629684470313

theorem tailTrace_2839155 : CollatzResearch.WordTrace tailWord_2839155 prefixEnd_2839155 971900778410629684470313 := by
  unfold tailWord_2839155
  simp only [CollatzResearch.WordTrace]
  refine ⟨103552490029233798915118919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69034993352822532610079279 103552490029233798915118919)
  ·
    refine ⟨155328735043850698372678379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103552490029233798915118919 155328735043850698372678379)
    ·
      refine ⟨232993102565776047559017569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155328735043850698372678379 232993102565776047559017569)
      ·
        refine ⟨174744826924332035669263177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232993102565776047559017569 174744826924332035669263177)
        ·
          refine ⟨131058620193249026751947383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174744826924332035669263177 131058620193249026751947383)
          ·
            refine ⟨196587930289873540127921075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131058620193249026751947383 196587930289873540127921075)
            ·
              refine ⟨294881895434810310191881613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196587930289873540127921075 294881895434810310191881613)
              ·
                refine ⟨110580710788053866321955605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294881895434810310191881613 110580710788053866321955605)
                ·
                  refine ⟨5183470818190024983841669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110580710788053866321955605 5183470818190024983841669)
                  ·
                    refine ⟨971900778410629684470313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5183470818190024983841669 971900778410629684470313)
                    ·
                      rfl

theorem cell22_2839155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 4].length) (baseStart_2839155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839155 prefixEnd_2839155 := by exact prefixLift 2839155
  have htrace : WordTrace (prefixWord ++ tailWord_2839155) baseStart_2839155 baseEnd_2839155 := by
    simpa [prefixWord, tailWord_2839155, baseEnd_2839155] using wordTrace_append hprefix tailTrace_2839155
  have hstable : (prefixWord ++ tailWord_2839155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839155).length < 2 ^ (prefixWord ++ tailWord_2839155).sum := by decide
  have hdescent : baseEnd_2839155 < baseStart_2839155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839172 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2839172 : Nat := 118140960795 + 2839172 * 2 ^ 59
def prefixEnd_2839172 : Nat := 4983230072969 + 3 ^ 40 * 2839172 * 2
def baseEnd_2839172 : Nat := 971906597858047306795261

theorem tailTrace_2839172 : CollatzResearch.WordTrace tailWord_2839172 prefixEnd_2839172 971906597858047306795261 := by
  unfold tailWord_2839172
  simp only [CollatzResearch.WordTrace]
  refine ⟨51776555035086105409243885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69035406713448140545658513 51776555035086105409243885)
  ·
    refine ⟨19416208138157289528466457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51776555035086105409243885 19416208138157289528466457)
    ·
      refine ⟨14562156103617967146349843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19416208138157289528466457 14562156103617967146349843)
      ·
        refine ⟨21843234155426950719524765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14562156103617967146349843 21843234155426950719524765)
        ·
          refine ⟨8191212808285106519821787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21843234155426950719524765 8191212808285106519821787)
          ·
            refine ⟨12286819212427659779732681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8191212808285106519821787 12286819212427659779732681)
            ·
              refine ⟨9215114409320744834799511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12286819212427659779732681 9215114409320744834799511)
              ·
                refine ⟨13822671613981117252199267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9215114409320744834799511 13822671613981117252199267)
                ·
                  refine ⟨20734007420971675878298901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13822671613981117252199267 20734007420971675878298901)
                  ·
                    refine ⟨971906597858047306795261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20734007420971675878298901 971906597858047306795261)
                    ·
                      rfl

theorem cell22_2839172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2839172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839172 prefixEnd_2839172 := by exact prefixLift 2839172
  have htrace : WordTrace (prefixWord ++ tailWord_2839172) baseStart_2839172 baseEnd_2839172 := by
    simpa [prefixWord, tailWord_2839172, baseEnd_2839172] using wordTrace_append hprefix tailTrace_2839172
  have hstable : (prefixWord ++ tailWord_2839172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839172).length < 2 ^ (prefixWord ++ tailWord_2839172).sum := by decide
  have hdescent : baseEnd_2839172 < baseStart_2839172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839307 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 4, 4]
def baseStart_2839307 : Nat := 118140960795 + 2839307 * 2 ^ 59
def prefixEnd_2839307 : Nat := 4983230072969 + 3 ^ 40 * 2839307 * 2
def baseEnd_2839307 : Nat := 971952811116951954669847

theorem tailTrace_2839307 : CollatzResearch.WordTrace tailWord_2839307 prefixEnd_2839307 971952811116951954669847 := by
  unfold tailWord_2839307
  simp only [CollatzResearch.WordTrace]
  refine ⟨103558033924683128874652175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69038689283122085916434783 103558033924683128874652175)
  ·
    refine ⟨155337050887024693311978263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103558033924683128874652175 155337050887024693311978263)
    ·
      refine ⟨233005576330537039967967395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155337050887024693311978263 233005576330537039967967395)
      ·
        refine ⟨349508364495805559951951093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233005576330537039967967395 349508364495805559951951093)
        ·
          refine ⟨32766409171481771245495415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 349508364495805559951951093 32766409171481771245495415)
          ·
            refine ⟨49149613757222656868243123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32766409171481771245495415 49149613757222656868243123)
            ·
              refine ⟨73724420635833985302364685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49149613757222656868243123 73724420635833985302364685)
              ·
                refine ⟨27646657738437744488386757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73724420635833985302364685 27646657738437744488386757)
                ·
                  refine ⟨5183748325957077091572517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27646657738437744488386757 5183748325957077091572517)
                  ·
                    refine ⟨971952811116951954669847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5183748325957077091572517 971952811116951954669847)
                    ·
                      rfl

theorem cell22_2839307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 4].length) (baseStart_2839307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839307 prefixEnd_2839307 := by exact prefixLift 2839307
  have htrace : WordTrace (prefixWord ++ tailWord_2839307) baseStart_2839307 baseEnd_2839307 := by
    simpa [prefixWord, tailWord_2839307, baseEnd_2839307] using wordTrace_append hprefix tailTrace_2839307
  have hstable : (prefixWord ++ tailWord_2839307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839307).length < 2 ^ (prefixWord ++ tailWord_2839307).sum := by decide
  have hdescent : baseEnd_2839307 < baseStart_2839307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839322 : List Nat := [3, 1, 1, 3, 2, 1, 2, 9]
def baseStart_2839322 : Nat := 118140960795 + 2839322 * 2 ^ 59
def prefixEnd_2839322 : Nat := 4983230072969 + 3 ^ 40 * 2839322 * 2
def baseEnd_2839322 : Nat := 107995327324832990616089

theorem tailTrace_2839322 : CollatzResearch.WordTrace tailWord_2839322 prefixEnd_2839322 107995327324832990616089 := by
  unfold tailWord_2839322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25889645254907196609112055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69039054013085857624298813 25889645254907196609112055)
  ·
    refine ⟨38834467882360794913668083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25889645254907196609112055 38834467882360794913668083)
    ·
      refine ⟨58251701823541192370502125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38834467882360794913668083 58251701823541192370502125)
      ·
        refine ⟨21844388183827947138938297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58251701823541192370502125 21844388183827947138938297)
        ·
          refine ⟨16383291137870960354203723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21844388183827947138938297 16383291137870960354203723)
          ·
            refine ⟨24574936706806440531305585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16383291137870960354203723 24574936706806440531305585)
            ·
              refine ⟨18431202530104830398479189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24574936706806440531305585 18431202530104830398479189)
              ·
                refine ⟨107995327324832990616089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18431202530104830398479189 107995327324832990616089)
                ·
                  rfl

theorem cell22_2839322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_2839322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839322 prefixEnd_2839322 := by exact prefixLift 2839322
  have htrace : WordTrace (prefixWord ++ tailWord_2839322) baseStart_2839322 baseEnd_2839322 := by
    simpa [prefixWord, tailWord_2839322, baseEnd_2839322] using wordTrace_append hprefix tailTrace_2839322
  have hstable : (prefixWord ++ tailWord_2839322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839322).length < 2 ^ (prefixWord ++ tailWord_2839322).sum := by decide
  have hdescent : baseEnd_2839322 < baseStart_2839322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839422 : List Nat := [4, 2, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2839422 : Nat := 118140960795 + 2839422 * 2 ^ 59
def prefixEnd_2839422 : Nat := 4983230072969 + 3 ^ 40 * 2839422 * 2
def baseEnd_2839422 : Nat := 971992177967129988044495

theorem tailTrace_2839422 : CollatzResearch.WordTrace tailWord_2839422 prefixEnd_2839422 971992177967129988044495 := by
  unfold tailWord_2839422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12945278539908312939386065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69041485546177669010059013 12945278539908312939386065)
  ·
    refine ⟨9708958904931234704539549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12945278539908312939386065 9708958904931234704539549)
    ·
      refine ⟨3640859589349213014202331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9708958904931234704539549 3640859589349213014202331)
      ·
        refine ⟨5461289384023819521303497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640859589349213014202331 5461289384023819521303497)
        ·
          refine ⟨4095967038017864640977623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5461289384023819521303497 4095967038017864640977623)
          ·
            refine ⟨6143950557026796961466435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095967038017864640977623 6143950557026796961466435)
            ·
              refine ⟨9215925835540195442199653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6143950557026796961466435 9215925835540195442199653)
              ·
                refine ⟨1727986094163786645412435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9215925835540195442199653 1727986094163786645412435)
                ·
                  refine ⟨2591979141245679968118653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727986094163786645412435 2591979141245679968118653)
                  ·
                    refine ⟨971992177967129988044495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2591979141245679968118653 971992177967129988044495)
                    ·
                      rfl

theorem cell22_2839422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2839422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839422 prefixEnd_2839422 := by exact prefixLift 2839422
  have htrace : WordTrace (prefixWord ++ tailWord_2839422) baseStart_2839422 baseEnd_2839422 := by
    simpa [prefixWord, tailWord_2839422, baseEnd_2839422] using wordTrace_append hprefix tailTrace_2839422
  have hstable : (prefixWord ++ tailWord_2839422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839422).length < 2 ^ (prefixWord ++ tailWord_2839422).sum := by decide
  have hdescent : baseEnd_2839422 < baseStart_2839422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839508 : List Nat := [2, 4, 1, 2, 1, 4, 2, 6]
def baseStart_2839508 : Nat := 118140960795 + 2839508 * 2 ^ 59
def prefixEnd_2839508 : Nat := 4983230072969 + 3 ^ 40 * 2839508 * 2
def baseEnd_2839508 : Nat := 108002401947183825599359

theorem tailTrace_2839508 : CollatzResearch.WordTrace tailWord_2839508 prefixEnd_2839508 108002401947183825599359 := by
  unfold tailWord_2839508
  simp only [CollatzResearch.WordTrace]
  refine ⟨51782682498477470101359589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69043576664636626801812785 51782682498477470101359589)
  ·
    refine ⟨9709252968464525644004923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51782682498477470101359589 9709252968464525644004923)
    ·
      refine ⟨14563879452696788466007385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9709252968464525644004923 14563879452696788466007385)
      ·
        refine ⟨10922909589522591349505539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14563879452696788466007385 10922909589522591349505539)
        ·
          refine ⟨16384364384283887024258309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10922909589522591349505539 16384364384283887024258309)
          ·
            refine ⟨3072068322053228817048433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16384364384283887024258309 3072068322053228817048433)
            ·
              refine ⟨2304051241539921612786325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3072068322053228817048433 2304051241539921612786325)
              ·
                refine ⟨108002401947183825599359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2304051241539921612786325 108002401947183825599359)
                ·
                  rfl

theorem cell22_2839508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 6].length) (baseStart_2839508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839508 prefixEnd_2839508 := by exact prefixLift 2839508
  have htrace : WordTrace (prefixWord ++ tailWord_2839508) baseStart_2839508 baseEnd_2839508 := by
    simpa [prefixWord, tailWord_2839508, baseEnd_2839508] using wordTrace_append hprefix tailTrace_2839508
  have hstable : (prefixWord ++ tailWord_2839508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839508).length < 2 ^ (prefixWord ++ tailWord_2839508).sum := by decide
  have hdescent : baseEnd_2839508 < baseStart_2839508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839549 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2839549 : Nat := 118140960795 + 2839549 * 2 ^ 59
def prefixEnd_2839549 : Nat := 4983230072969 + 3 ^ 40 * 2839549 * 2
def baseEnd_2839549 : Nat := 972035652662543990119105

theorem tailTrace_2839549 : CollatzResearch.WordTrace tailWord_2839549 prefixEnd_2839549 972035652662543990119105 := by
  unfold tailWord_2839549
  simp only [CollatzResearch.WordTrace]
  refine ⟨103566860389806404204961701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69044573593204269469974467 103566860389806404204961701)
  ·
    refine ⟨19418786323088700788430319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103566860389806404204961701 19418786323088700788430319)
    ·
      refine ⟨29128179484633051182645479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19418786323088700788430319 29128179484633051182645479)
      ·
        refine ⟨43692269226949576773968219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29128179484633051182645479 43692269226949576773968219)
        ·
          refine ⟨65538403840424365160952329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43692269226949576773968219 65538403840424365160952329)
          ·
            refine ⟨49153802880318273870714247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65538403840424365160952329 49153802880318273870714247)
            ·
              refine ⟨73730704320477410806071371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49153802880318273870714247 73730704320477410806071371)
              ·
                refine ⟨110596056480716116209107057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73730704320477410806071371 110596056480716116209107057)
                ·
                  refine ⟨82947042360537087156830293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110596056480716116209107057 82947042360537087156830293)
                  ·
                    refine ⟨972035652662543990119105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82947042360537087156830293 972035652662543990119105)
                    ·
                      rfl

theorem cell22_2839549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2839549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839549 prefixEnd_2839549 := by exact prefixLift 2839549
  have htrace : WordTrace (prefixWord ++ tailWord_2839549) baseStart_2839549 baseEnd_2839549 := by
    simpa [prefixWord, tailWord_2839549, baseEnd_2839549] using wordTrace_append hprefix tailTrace_2839549
  have hstable : (prefixWord ++ tailWord_2839549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839549).length < 2 ^ (prefixWord ++ tailWord_2839549).sum := by decide
  have hdescent : baseEnd_2839549 < baseStart_2839549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839553 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 5]
def baseStart_2839553 : Nat := 118140960795 + 2839553 * 2 ^ 59
def prefixEnd_2839553 : Nat := 4983230072969 + 3 ^ 40 * 2839553 * 2
def baseEnd_2839553 : Nat := 324012340648096437673031

theorem tailTrace_2839553 : CollatzResearch.WordTrace tailWord_2839553 prefixEnd_2839553 324012340648096437673031 := by
  unfold tailWord_2839553
  simp only [CollatzResearch.WordTrace]
  refine ⟨103567006281791912888107313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69044670854527941925404875 103567006281791912888107313)
  ·
    refine ⟨77675254711343934666080485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103567006281791912888107313 77675254711343934666080485)
    ·
      refine ⟨14564110258376987749890091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77675254711343934666080485 14564110258376987749890091)
      ·
        refine ⟨21846165387565481624835137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14564110258376987749890091 21846165387565481624835137)
        ·
          refine ⟨16384624040674111218626353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21846165387565481624835137 16384624040674111218626353)
          ·
            refine ⟨12288468030505583413969765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16384624040674111218626353 12288468030505583413969765)
            ·
              refine ⟨2304087755719796890119331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12288468030505583413969765 2304087755719796890119331)
              ·
                refine ⟨3456131633579695335178997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304087755719796890119331 3456131633579695335178997)
                ·
                  refine ⟨324012340648096437673031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3456131633579695335178997 324012340648096437673031)
                  ·
                    rfl

theorem cell22_2839553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 5].length) (baseStart_2839553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839553 prefixEnd_2839553 := by exact prefixLift 2839553
  have htrace : WordTrace (prefixWord ++ tailWord_2839553) baseStart_2839553 baseEnd_2839553 := by
    simpa [prefixWord, tailWord_2839553, baseEnd_2839553] using wordTrace_append hprefix tailTrace_2839553
  have hstable : (prefixWord ++ tailWord_2839553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839553).length < 2 ^ (prefixWord ++ tailWord_2839553).sum := by decide
  have hdescent : baseEnd_2839553 < baseStart_2839553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839613 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_2839613 : Nat := 118140960795 + 2839613 * 2 ^ 59
def prefixEnd_2839613 : Nat := 4983230072969 + 3 ^ 40 * 2839613 * 2
def baseEnd_2839613 : Nat := 972057561170469156518909

theorem tailTrace_2839613 : CollatzResearch.WordTrace tailWord_2839613 prefixEnd_2839613 972057561170469156518909 := by
  unfold tailWord_2839613
  simp only [CollatzResearch.WordTrace]
  refine ⟨103569194661574543135291493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69046129774383028756860995 103569194661574543135291493)
  ·
    refine ⟨19419223999045226837867155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103569194661574543135291493 19419223999045226837867155)
    ·
      refine ⟨29128835998567840256800733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19419223999045226837867155 29128835998567840256800733)
      ·
        refine ⟨10923313499462940096300275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29128835998567840256800733 10923313499462940096300275)
        ·
          refine ⟨16384970249194410144450413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10923313499462940096300275 16384970249194410144450413)
          ·
            refine ⟨6144363843447903804168905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16384970249194410144450413 6144363843447903804168905)
            ·
              refine ⟨4608272882585927853126679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6144363843447903804168905 4608272882585927853126679)
              ·
                refine ⟨6912409323878891779690019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608272882585927853126679 6912409323878891779690019)
                ·
                  refine ⟨10368613985818337669535029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6912409323878891779690019 10368613985818337669535029)
                  ·
                    refine ⟨972057561170469156518909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10368613985818337669535029 972057561170469156518909)
                    ·
                      rfl

theorem cell22_2839613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_2839613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839613 prefixEnd_2839613 := by exact prefixLift 2839613
  have htrace : WordTrace (prefixWord ++ tailWord_2839613) baseStart_2839613 baseEnd_2839613 := by
    simpa [prefixWord, tailWord_2839613, baseEnd_2839613] using wordTrace_append hprefix tailTrace_2839613
  have hstable : (prefixWord ++ tailWord_2839613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839613).length < 2 ^ (prefixWord ++ tailWord_2839613).sum := by decide
  have hdescent : baseEnd_2839613 < baseStart_2839613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839722 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_2839722 : Nat := 118140960795 + 2839722 * 2 ^ 59
def prefixEnd_2839722 : Nat := 4983230072969 + 3 ^ 40 * 2839722 * 2
def baseEnd_2839722 : Nat := 324031624699343068514525

theorem tailTrace_2839722 : CollatzResearch.WordTrace tailWord_2839722 prefixEnd_2839722 324031624699343068514525 := by
  unfold tailWord_2839722
  simp only [CollatzResearch.WordTrace]
  refine ⟨25893292554544913687752355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69048780145453103167339613 25893292554544913687752355)
  ·
    refine ⟨38839938831817370531628533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25893292554544913687752355 38839938831817370531628533)
    ·
      refine ⟨3641244265482878487340175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38839938831817370531628533 3641244265482878487340175)
      ·
        refine ⟨5461866398224317731010263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3641244265482878487340175 5461866398224317731010263)
        ·
          refine ⟨8192799597336476596515395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5461866398224317731010263 8192799597336476596515395)
          ·
            refine ⟨12289199396004714894773093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8192799597336476596515395 12289199396004714894773093)
            ·
              refine ⟨2304224886750884042769955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12289199396004714894773093 2304224886750884042769955)
              ·
                refine ⟨3456337330126326064154933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304224886750884042769955 3456337330126326064154933)
                ·
                  refine ⟨324031624699343068514525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3456337330126326064154933 324031624699343068514525)
                  ·
                    rfl

theorem cell22_2839722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_2839722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839722 prefixEnd_2839722 := by exact prefixLift 2839722
  have htrace : WordTrace (prefixWord ++ tailWord_2839722) baseStart_2839722 baseEnd_2839722 := by
    simpa [prefixWord, tailWord_2839722, baseEnd_2839722] using wordTrace_append hprefix tailTrace_2839722
  have hstable : (prefixWord ++ tailWord_2839722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839722).length < 2 ^ (prefixWord ++ tailWord_2839722).sum := by decide
  have hdescent : baseEnd_2839722 < baseStart_2839722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839878 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2839878 : Nat := 118140960795 + 2839878 * 2 ^ 59
def prefixEnd_2839878 : Nat := 4983230072969 + 3 ^ 40 * 2839878 * 2
def baseEnd_2839878 : Nat := 972148276086096798643097

theorem tailTrace_2839878 : CollatzResearch.WordTrace tailWord_2839878 prefixEnd_2839878 972148276086096798643097 := by
  unfold tailWord_2839878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236839375175452918552759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69052573337076328929125525 3236839375175452918552759)
  ·
    refine ⟨4855259062763179377829139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3236839375175452918552759 4855259062763179377829139)
    ·
      refine ⟨7282888594144769066743709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4855259062763179377829139 7282888594144769066743709)
      ·
        refine ⟨2731083222804288400028891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7282888594144769066743709 2731083222804288400028891)
        ·
          refine ⟨4096624834206432600043337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731083222804288400028891 4096624834206432600043337)
          ·
            refine ⟨3072468625654824450032503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4096624834206432600043337 3072468625654824450032503)
            ·
              refine ⟨4608702938482236675048755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072468625654824450032503 4608702938482236675048755)
              ·
                refine ⟨6913054407723355012573133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608702938482236675048755 6913054407723355012573133)
                ·
                  refine ⟨2592395402896258129714925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6913054407723355012573133 2592395402896258129714925)
                  ·
                    refine ⟨972148276086096798643097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2592395402896258129714925 972148276086096798643097)
                    ·
                      rfl

theorem cell22_2839878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2839878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839878 prefixEnd_2839878 := by exact prefixLift 2839878
  have htrace : WordTrace (prefixWord ++ tailWord_2839878) baseStart_2839878 baseEnd_2839878 := by
    simpa [prefixWord, tailWord_2839878, baseEnd_2839878] using wordTrace_append hprefix tailTrace_2839878
  have hstable : (prefixWord ++ tailWord_2839878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839878).length < 2 ^ (prefixWord ++ tailWord_2839878).sum := by decide
  have hdescent : baseEnd_2839878 < baseStart_2839878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839898 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_2839898 : Nat := 118140960795 + 2839898 * 2 ^ 59
def prefixEnd_2839898 : Nat := 4983230072969 + 3 ^ 40 * 2839898 * 2
def baseEnd_2839898 : Nat := 972155122494823413143035

theorem tailTrace_2839898 : CollatzResearch.WordTrace tailWord_2839898 prefixEnd_2839898 972155122494823413143035 := by
  unfold tailWord_2839898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25894897366385509202354087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69053059643694691206277565 25894897366385509202354087)
  ·
    refine ⟨38842346049578263803531131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25894897366385509202354087 38842346049578263803531131)
    ·
      refine ⟨58263519074367395705296697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38842346049578263803531131 58263519074367395705296697)
      ·
        refine ⟨43697639305775546778972523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58263519074367395705296697 43697639305775546778972523)
        ·
          refine ⟨65546458958663320168458785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43697639305775546778972523 65546458958663320168458785)
          ·
            refine ⟨49159844218997490126344089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65546458958663320168458785 49159844218997490126344089)
            ·
              refine ⟨36869883164248117594758067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49159844218997490126344089 36869883164248117594758067)
              ·
                refine ⟨55304824746372176392137101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36869883164248117594758067 55304824746372176392137101)
                ·
                  refine ⟨20739309279889566147051413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55304824746372176392137101 20739309279889566147051413)
                  ·
                    refine ⟨972155122494823413143035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20739309279889566147051413 972155122494823413143035)
                    ·
                      rfl

theorem cell22_2839898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_2839898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839898 prefixEnd_2839898 := by exact prefixLift 2839898
  have htrace : WordTrace (prefixWord ++ tailWord_2839898) baseStart_2839898 baseEnd_2839898 := by
    simpa [prefixWord, tailWord_2839898, baseEnd_2839898] using wordTrace_append hprefix tailTrace_2839898
  have hstable : (prefixWord ++ tailWord_2839898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839898).length < 2 ^ (prefixWord ++ tailWord_2839898).sum := by decide
  have hdescent : baseEnd_2839898 < baseStart_2839898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839962 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_2839962 : Nat := 118140960795 + 2839962 * 2 ^ 59
def prefixEnd_2839962 : Nat := 4983230072969 + 3 ^ 40 * 2839962 * 2
def baseEnd_2839962 : Nat := 972177031002748579542839

theorem tailTrace_2839962 : CollatzResearch.WordTrace tailWord_2839962 prefixEnd_2839962 972177031002748579542839 := by
  unfold tailWord_2839962
  simp only [CollatzResearch.WordTrace]
  refine ⟨25895480934327543934936535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69054615824873450493164093 25895480934327543934936535)
  ·
    refine ⟨38843221401491315902404803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25895480934327543934936535 38843221401491315902404803)
    ·
      refine ⟨58264832102236973853607205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38843221401491315902404803 58264832102236973853607205)
      ·
        refine ⟨10924656019169432597551351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58264832102236973853607205 10924656019169432597551351)
        ·
          refine ⟨16386984028754148896327027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10924656019169432597551351 16386984028754148896327027)
          ·
            refine ⟨24580476043131223344490541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16386984028754148896327027 24580476043131223344490541)
            ·
              refine ⟨9217678516174208754183953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24580476043131223344490541 9217678516174208754183953)
              ·
                refine ⟨6913258887130656565637965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9217678516174208754183953 6913258887130656565637965)
                ·
                  refine ⟨2592472082673996212114237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6913258887130656565637965 2592472082673996212114237)
                  ·
                    refine ⟨972177031002748579542839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2592472082673996212114237 972177031002748579542839)
                    ·
                      rfl

theorem cell22_2839962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_2839962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839962 prefixEnd_2839962 := by exact prefixLift 2839962
  have htrace : WordTrace (prefixWord ++ tailWord_2839962) baseStart_2839962 baseEnd_2839962 := by
    simpa [prefixWord, tailWord_2839962, baseEnd_2839962] using wordTrace_append hprefix tailTrace_2839962
  have hstable : (prefixWord ++ tailWord_2839962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839962).length < 2 ^ (prefixWord ++ tailWord_2839962).sum := by decide
  have hdescent : baseEnd_2839962 < baseStart_2839962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839964 : List Nat := [2, 2, 3, 4, 1, 1, 3, 6]
def baseStart_2839964 : Nat := 118140960795 + 2839964 * 2 ^ 59
def prefixEnd_2839964 : Nat := 4983230072969 + 3 ^ 40 * 2839964 * 2
def baseEnd_2839964 : Nat := 108019746182624582332537

theorem tailTrace_2839964 : CollatzResearch.WordTrace tailWord_2839964 prefixEnd_2839964 108019746182624582332537 := by
  unfold tailWord_2839964
  simp only [CollatzResearch.WordTrace]
  refine ⟨51790998341651465040659473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69054664455535286720879297 51790998341651465040659473)
  ·
    refine ⟨38843248756238598780494605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51790998341651465040659473 38843248756238598780494605)
    ·
      refine ⟨14566218283589474542685477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38843248756238598780494605 14566218283589474542685477)
      ·
        refine ⟨2731165928173026476753527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14566218283589474542685477 2731165928173026476753527)
        ·
          refine ⟨4096748892259539715130291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731165928173026476753527 4096748892259539715130291)
          ·
            refine ⟨6145123338389309572695437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096748892259539715130291 6145123338389309572695437)
            ·
              refine ⟨2304421251895991089760789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6145123338389309572695437 2304421251895991089760789)
              ·
                refine ⟨108019746182624582332537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2304421251895991089760789 108019746182624582332537)
                ·
                  rfl

theorem cell22_2839964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 6].length) (baseStart_2839964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839964 prefixEnd_2839964 := by exact prefixLift 2839964
  have htrace : WordTrace (prefixWord ++ tailWord_2839964) baseStart_2839964 baseEnd_2839964 := by
    simpa [prefixWord, tailWord_2839964, baseEnd_2839964] using wordTrace_append hprefix tailTrace_2839964
  have hstable : (prefixWord ++ tailWord_2839964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839964).length < 2 ^ (prefixWord ++ tailWord_2839964).sum := by decide
  have hdescent : baseEnd_2839964 < baseStart_2839964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839966 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2839966 : Nat := 118140960795 + 2839966 * 2 ^ 59
def prefixEnd_2839966 : Nat := 4983230072969 + 3 ^ 40 * 2839966 * 2
def baseEnd_2839966 : Nat := 972178400284493902442827

theorem tailTrace_2839966 : CollatzResearch.WordTrace tailWord_2839966 prefixEnd_2839966 972178400284493902442827 := by
  unfold tailWord_2839966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12947758703661960552861469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69054713086197122948594501 12947758703661960552861469)
  ·
    refine ⟨4855409513873235207323051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12947758703661960552861469 4855409513873235207323051)
    ·
      refine ⟨7283114270809852810984577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4855409513873235207323051 7283114270809852810984577)
      ·
        refine ⟨5462335703107389608238433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7283114270809852810984577 5462335703107389608238433)
        ·
          refine ⟨4096751777330542206178825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5462335703107389608238433 4096751777330542206178825)
          ·
            refine ⟨3072563832997906654634119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4096751777330542206178825 3072563832997906654634119)
            ·
              refine ⟨4608845749496859981951179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072563832997906654634119 4608845749496859981951179)
              ·
                refine ⟨6913268624245289972926769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608845749496859981951179 6913268624245289972926769)
                ·
                  refine ⟨5184951468183967479695077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6913268624245289972926769 5184951468183967479695077)
                  ·
                    refine ⟨972178400284493902442827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5184951468183967479695077 972178400284493902442827)
                    ·
                      rfl

theorem cell22_2839966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2839966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839966 prefixEnd_2839966 := by exact prefixLift 2839966
  have htrace : WordTrace (prefixWord ++ tailWord_2839966) baseStart_2839966 baseEnd_2839966 := by
    simpa [prefixWord, tailWord_2839966, baseEnd_2839966] using wordTrace_append hprefix tailTrace_2839966
  have hstable : (prefixWord ++ tailWord_2839966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839966).length < 2 ^ (prefixWord ++ tailWord_2839966).sum := by decide
  have hdescent : baseEnd_2839966 < baseStart_2839966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839975 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 7]
def baseStart_2839975 : Nat := 118140960795 + 2839975 * 2 ^ 59
def prefixEnd_2839975 : Nat := 4983230072969 + 3 ^ 40 * 2839975 * 2
def baseEnd_2839975 : Nat := 324060493722806959655933

theorem tailTrace_2839975 : CollatzResearch.WordTrace tailWord_2839975 prefixEnd_2839975 324060493722806959655933 := by
  unfold tailWord_2839975
  simp only [CollatzResearch.WordTrace]
  refine ⟨103582397886263078959969379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69054931924175385973312919 103582397886263078959969379)
  ·
    refine ⟨155373596829394618439954069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103582397886263078959969379 155373596829394618439954069)
    ·
      refine ⟨7283137351377872739372847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155373596829394618439954069 7283137351377872739372847)
      ·
        refine ⟨10924706027066809109059271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7283137351377872739372847 10924706027066809109059271)
        ·
          refine ⟨16387059040600213663588907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10924706027066809109059271 16387059040600213663588907)
          ·
            refine ⟨24580588560900320495383361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16387059040600213663588907 24580588560900320495383361)
            ·
              refine ⟨18435441420675240371537521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24580588560900320495383361 18435441420675240371537521)
              ·
                refine ⟨13826581065506430278653141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18435441420675240371537521 13826581065506430278653141)
                ·
                  refine ⟨324060493722806959655933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13826581065506430278653141 324060493722806959655933)
                  ·
                    rfl

theorem cell22_2839975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 7].length) (baseStart_2839975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2839975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2839975 prefixEnd_2839975 := by exact prefixLift 2839975
  have htrace : WordTrace (prefixWord ++ tailWord_2839975) baseStart_2839975 baseEnd_2839975 := by
    simpa [prefixWord, tailWord_2839975, baseEnd_2839975] using wordTrace_append hprefix tailTrace_2839975
  have hstable : (prefixWord ++ tailWord_2839975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839975).length < 2 ^ (prefixWord ++ tailWord_2839975).sum := by decide
  have hdescent : baseEnd_2839975 < baseStart_2839975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840002 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2840002 : Nat := 118140960795 + 2840002 * 2 ^ 59
def prefixEnd_2840002 : Nat := 4983230072969 + 3 ^ 40 * 2840002 * 2
def baseEnd_2840002 : Nat := 972190723820201808542717

theorem tailTrace_2840002 : CollatzResearch.WordTrace tailWord_2840002 prefixEnd_2840002 972190723820201808542717 := by
  unfold tailWord_2840002
  simp only [CollatzResearch.WordTrace]
  refine ⟨25895845664291315642800565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69055588438110175047468173 25895845664291315642800565)
  ·
    refine ⟨2427735531027310841512553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25895845664291315642800565 2427735531027310841512553)
    ·
      refine ⟨1820801648270483131134415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2427735531027310841512553 1820801648270483131134415)
      ·
        refine ⟨2731202472405724696701623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820801648270483131134415 2731202472405724696701623)
        ·
          refine ⟨4096803708608587045052435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731202472405724696701623 4096803708608587045052435)
          ·
            refine ⟨6145205562912880567578653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096803708608587045052435 6145205562912880567578653)
            ·
              refine ⟨2304452086092330212841995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6145205562912880567578653 2304452086092330212841995)
              ·
                refine ⟨3456678129138495319262993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304452086092330212841995 3456678129138495319262993)
                ·
                  refine ⟨2592508596853871489447245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3456678129138495319262993 2592508596853871489447245)
                  ·
                    refine ⟨972190723820201808542717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2592508596853871489447245 972190723820201808542717)
                    ·
                      rfl

theorem cell22_2840002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2840002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840002 prefixEnd_2840002 := by exact prefixLift 2840002
  have htrace : WordTrace (prefixWord ++ tailWord_2840002) baseStart_2840002 baseEnd_2840002 := by
    simpa [prefixWord, tailWord_2840002, baseEnd_2840002] using wordTrace_append hprefix tailTrace_2840002
  have hstable : (prefixWord ++ tailWord_2840002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840002).length < 2 ^ (prefixWord ++ tailWord_2840002).sum := by decide
  have hdescent : baseEnd_2840002 < baseStart_2840002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840054 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_2840054 : Nat := 118140960795 + 2840054 * 2 ^ 59
def prefixEnd_2840054 : Nat := 4983230072969 + 3 ^ 40 * 2840054 * 2
def baseEnd_2840054 : Nat := 324069508160963668747519

theorem tailTrace_2840054 : CollatzResearch.WordTrace tailWord_2840054 prefixEnd_2840054 324069508160963668747519 := by
  unfold tailWord_2840054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474079953311054715755951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69056852835317916968063477 6474079953311054715755951)
  ·
    refine ⟨9711119929966582073633927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6474079953311054715755951 9711119929966582073633927)
    ·
      refine ⟨14566679894949873110450891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9711119929966582073633927 14566679894949873110450891)
      ·
        refine ⟨21850019842424809665676337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14566679894949873110450891 21850019842424809665676337)
        ·
          refine ⟨16387514881818607249257253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21850019842424809665676337 16387514881818607249257253)
          ·
            refine ⟨3072659040340988859235735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16387514881818607249257253 3072659040340988859235735)
            ·
              refine ⟨4608988560511483288853603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072659040340988859235735 4608988560511483288853603)
              ·
                refine ⟨6913482840767224933280405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608988560511483288853603 6913482840767224933280405)
                ·
                  refine ⟨324069508160963668747519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6913482840767224933280405 324069508160963668747519)
                  ·
                    rfl

theorem cell22_2840054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_2840054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840054 prefixEnd_2840054 := by exact prefixLift 2840054
  have htrace : WordTrace (prefixWord ++ tailWord_2840054) baseStart_2840054 baseEnd_2840054 := by
    simpa [prefixWord, tailWord_2840054, baseEnd_2840054] using wordTrace_append hprefix tailTrace_2840054
  have hstable : (prefixWord ++ tailWord_2840054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840054).length < 2 ^ (prefixWord ++ tailWord_2840054).sum := by decide
  have hdescent : baseEnd_2840054 < baseStart_2840054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840127 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 5]
def baseStart_2840127 : Nat := 118140960795 + 2840127 * 2 ^ 59
def prefixEnd_2840127 : Nat := 4983230072969 + 3 ^ 40 * 2840127 * 2
def baseEnd_2840127 : Nat := 324077837958247716389111

theorem tailTrace_2840127 : CollatzResearch.WordTrace tailWord_2840127 prefixEnd_2840127 324077837958247716389111 := by
  unfold tailWord_2840127
  simp only [CollatzResearch.WordTrace]
  refine ⟨103587941781712408919502635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69058627854474939279668423 103587941781712408919502635)
  ·
    refine ⟨155381912672568613379253953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103587941781712408919502635 155381912672568613379253953)
    ·
      refine ⟨116536434504426460034440465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155381912672568613379253953 116536434504426460034440465)
      ·
        refine ⟨87402325878319845025830349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116536434504426460034440465 87402325878319845025830349)
        ·
          refine ⟨32775872204369941884686381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87402325878319845025830349 32775872204369941884686381)
          ·
            refine ⟨12290952076638728206757393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32775872204369941884686381 12290952076638728206757393)
            ·
              refine ⟨9218214057479046155068045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12290952076638728206757393 9218214057479046155068045)
              ·
                refine ⟨3456830271554642308150517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9218214057479046155068045 3456830271554642308150517)
                ·
                  refine ⟨324077837958247716389111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3456830271554642308150517 324077837958247716389111)
                  ·
                    rfl

theorem cell22_2840127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 5].length) (baseStart_2840127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840127 prefixEnd_2840127 := by exact prefixLift 2840127
  have htrace : WordTrace (prefixWord ++ tailWord_2840127) baseStart_2840127 baseEnd_2840127 := by
    simpa [prefixWord, tailWord_2840127, baseEnd_2840127] using wordTrace_append hprefix tailTrace_2840127
  have hstable : (prefixWord ++ tailWord_2840127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840127).length < 2 ^ (prefixWord ++ tailWord_2840127).sum := by decide
  have hdescent : baseEnd_2840127 < baseStart_2840127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840206 : List Nat := [4, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_2840206 : Nat := 118140960795 + 2840206 * 2 ^ 59
def prefixEnd_2840206 : Nat := 4983230072969 + 3 ^ 40 * 2840206 * 2
def baseEnd_2840206 : Nat := 324086852396404425480697

theorem tailTrace_2840206 : CollatzResearch.WordTrace tailWord_2840206 prefixEnd_2840206 324086852396404425480697 := by
  unfold tailWord_2840206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12948852893553275676453559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69060548765617470274418981 12948852893553275676453559)
  ·
    refine ⟨19423279340329913514680339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12948852893553275676453559 19423279340329913514680339)
    ·
      refine ⟨29134919010494870272020509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19423279340329913514680339 29134919010494870272020509)
      ·
        refine ⟨10925594628935576352007691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29134919010494870272020509 10925594628935576352007691)
        ·
          refine ⟨16388391943403364528011537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10925594628935576352007691 16388391943403364528011537)
          ·
            refine ⟨12291293957552523396008653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16388391943403364528011537 12291293957552523396008653)
            ·
              refine ⟨4609235234082196273503245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12291293957552523396008653 4609235234082196273503245)
              ·
                refine ⟨1728463212780823602563717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4609235234082196273503245 1728463212780823602563717)
                ·
                  refine ⟨324086852396404425480697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1728463212780823602563717 324086852396404425480697)
                  ·
                    rfl

theorem cell22_2840206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_2840206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840206 prefixEnd_2840206 := by exact prefixLift 2840206
  have htrace : WordTrace (prefixWord ++ tailWord_2840206) baseStart_2840206 baseEnd_2840206 := by
    simpa [prefixWord, tailWord_2840206, baseEnd_2840206] using wordTrace_append hprefix tailTrace_2840206
  have hstable : (prefixWord ++ tailWord_2840206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840206).length < 2 ^ (prefixWord ++ tailWord_2840206).sum := by decide
  have hdescent : baseEnd_2840206 < baseStart_2840206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840223 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 6]
def baseStart_2840223 : Nat := 118140960795 + 2840223 * 2 ^ 59
def prefixEnd_2840223 : Nat := 4983230072969 + 3 ^ 40 * 2840223 * 2
def baseEnd_2840223 : Nat := 324088792212210299589013

theorem tailTrace_2840223 : CollatzResearch.WordTrace tailWord_2840223 prefixEnd_2840223 324088792212210299589013 := by
  unfold tailWord_2840223
  simp only [CollatzResearch.WordTrace]
  refine ⟨103591443189364617314997323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69060962126243078209998215 103591443189364617314997323)
  ·
    refine ⟨155387164784046925972495985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103591443189364617314997323 155387164784046925972495985)
    ·
      refine ⟨116540373588035194479371989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155387164784046925972495985 116540373588035194479371989)
      ·
        refine ⟨2731415005969574870610281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 116540373588035194479371989 2731415005969574870610281)
        ·
          refine ⟨2048561254477181152957711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2731415005969574870610281 2048561254477181152957711)
          ·
            refine ⟨3072841881715771729436567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048561254477181152957711 3072841881715771729436567)
            ·
              refine ⟨4609262822573657594154851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072841881715771729436567 4609262822573657594154851)
              ·
                refine ⟨6913894233860486391232277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4609262822573657594154851 6913894233860486391232277)
                ·
                  refine ⟨324088792212210299589013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6913894233860486391232277 324088792212210299589013)
                  ·
                    rfl

theorem cell22_2840223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 6].length) (baseStart_2840223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840223 prefixEnd_2840223 := by exact prefixLift 2840223
  have htrace : WordTrace (prefixWord ++ tailWord_2840223) baseStart_2840223 baseEnd_2840223 := by
    simpa [prefixWord, tailWord_2840223, baseEnd_2840223] using wordTrace_append hprefix tailTrace_2840223
  have hstable : (prefixWord ++ tailWord_2840223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840223).length < 2 ^ (prefixWord ++ tailWord_2840223).sum := by decide
  have hdescent : baseEnd_2840223 < baseStart_2840223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840249 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 3, 3]
def baseStart_2840249 : Nat := 118140960795 + 2840249 * 2 ^ 59
def prefixEnd_2840249 : Nat := 4983230072969 + 3 ^ 40 * 2840249 * 2
def baseEnd_2840249 : Nat := 972275276967975497616959

theorem tailTrace_2840249 : CollatzResearch.WordTrace tailWord_2840249 prefixEnd_2840249 972275276967975497616959 := by
  unfold tailWord_2840249
  simp only [CollatzResearch.WordTrace]
  refine ⟨103592391487270423755443801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69061594324846949170295867 103592391487270423755443801)
  ·
    refine ⟨77694293615452817816582851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103592391487270423755443801 77694293615452817816582851)
    ·
      refine ⟨116541440423179226724874277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77694293615452817816582851 116541440423179226724874277)
      ·
        refine ⟨21851520079346105010913927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116541440423179226724874277 21851520079346105010913927)
        ·
          refine ⟨32777280119019157516370891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21851520079346105010913927 32777280119019157516370891)
          ·
            refine ⟨49165920178528736274556337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32777280119019157516370891 49165920178528736274556337)
            ·
              refine ⟨36874440133896552205917253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49165920178528736274556337 36874440133896552205917253)
              ·
                refine ⟨6913957525105603538609485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36874440133896552205917253 6913957525105603538609485)
                ·
                  refine ⟨2592734071914601326978557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6913957525105603538609485 2592734071914601326978557)
                  ·
                    refine ⟨972275276967975497616959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2592734071914601326978557 972275276967975497616959)
                    ·
                      rfl

theorem cell22_2840249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_2840249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840249 prefixEnd_2840249 := by exact prefixLift 2840249
  have htrace : WordTrace (prefixWord ++ tailWord_2840249) baseStart_2840249 baseEnd_2840249 := by
    simpa [prefixWord, tailWord_2840249, baseEnd_2840249] using wordTrace_append hprefix tailTrace_2840249
  have hstable : (prefixWord ++ tailWord_2840249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840249).length < 2 ^ (prefixWord ++ tailWord_2840249).sum := by decide
  have hdescent : baseEnd_2840249 < baseStart_2840249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840279 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 5]
def baseStart_2840279 : Nat := 118140960795 + 2840279 * 2 ^ 59
def prefixEnd_2840279 : Nat := 4983230072969 + 3 ^ 40 * 2840279 * 2
def baseEnd_2840279 : Nat := 324095182193688473122289

theorem tailTrace_2840279 : CollatzResearch.WordTrace tailWord_2840279 prefixEnd_2840279 324095182193688473122289 := by
  unfold tailWord_2840279
  simp only [CollatzResearch.WordTrace]
  refine ⟨103593485677161738879035891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69062323784774492586023927 103593485677161738879035891)
  ·
    refine ⟨155390228515742608318553837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103593485677161738879035891 155390228515742608318553837)
    ·
      refine ⟨58271335693403478119457689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155390228515742608318553837 58271335693403478119457689)
      ·
        refine ⟨43703501770052608589593267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58271335693403478119457689 43703501770052608589593267)
        ·
          refine ⟨65555252655078912884389901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43703501770052608589593267 65555252655078912884389901)
          ·
            refine ⟨24583219745654592331646213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65555252655078912884389901 24583219745654592331646213)
            ·
              refine ⟨4609353702310236062183665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24583219745654592331646213 4609353702310236062183665)
              ·
                refine ⟨3457015276732677046637749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4609353702310236062183665 3457015276732677046637749)
                ·
                  refine ⟨324095182193688473122289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3457015276732677046637749 324095182193688473122289)
                  ·
                    rfl

theorem cell22_2840279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 5].length) (baseStart_2840279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840279 prefixEnd_2840279 := by exact prefixLift 2840279
  have htrace : WordTrace (prefixWord ++ tailWord_2840279) baseStart_2840279 baseEnd_2840279 := by
    simpa [prefixWord, tailWord_2840279, baseEnd_2840279] using wordTrace_append hprefix tailTrace_2840279
  have hstable : (prefixWord ++ tailWord_2840279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840279).length < 2 ^ (prefixWord ++ tailWord_2840279).sum := by decide
  have hdescent : baseEnd_2840279 < baseStart_2840279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840307 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 8]
def baseStart_2840307 : Nat := 118140960795 + 2840307 * 2 ^ 59
def prefixEnd_2840307 : Nat := 4983230072969 + 3 ^ 40 * 2840307 * 2
def baseEnd_2840307 : Nat := 324098377184427559888927

theorem tailTrace_2840307 : CollatzResearch.WordTrace tailWord_2840307 prefixEnd_2840307 324098377184427559888927 := by
  unfold tailWord_2840307
  simp only [CollatzResearch.WordTrace]
  refine ⟨103594506921060299661055175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69063004614040199774036783 103594506921060299661055175)
  ·
    refine ⟨155391760381590449491582763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103594506921060299661055175 155391760381590449491582763)
    ·
      refine ⟨233087640572385674237374145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155391760381590449491582763 233087640572385674237374145)
      ·
        refine ⟨174815730429289255678030609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233087640572385674237374145 174815730429289255678030609)
        ·
          refine ⟨131111797821966941758522957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174815730429289255678030609 131111797821966941758522957)
          ·
            refine ⟨49166924183237603159446109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131111797821966941758522957 49166924183237603159446109)
            ·
              refine ⟨18437596568714101184792291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49166924183237603159446109 18437596568714101184792291)
              ·
                refine ⟨27656394853071151777188437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18437596568714101184792291 27656394853071151777188437)
                ·
                  refine ⟨324098377184427559888927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27656394853071151777188437 324098377184427559888927)
                  ·
                    rfl

theorem cell22_2840307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 8].length) (baseStart_2840307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840307 prefixEnd_2840307 := by exact prefixLift 2840307
  have htrace : WordTrace (prefixWord ++ tailWord_2840307) baseStart_2840307 baseEnd_2840307 := by
    simpa [prefixWord, tailWord_2840307, baseEnd_2840307] using wordTrace_append hprefix tailTrace_2840307
  have hstable : (prefixWord ++ tailWord_2840307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840307).length < 2 ^ (prefixWord ++ tailWord_2840307).sum := by decide
  have hdescent : baseEnd_2840307 < baseStart_2840307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840341 : List Nat := [1, 3, 2, 1, 2, 3, 2, 4, 4]
def baseStart_2840341 : Nat := 118140960795 + 2840341 * 2 ^ 59
def prefixEnd_2840341 : Nat := 4983230072969 + 3 ^ 40 * 2840341 * 2
def baseEnd_2840341 : Nat := 324102256816039308105559

theorem tailTrace_2840341 : CollatzResearch.WordTrace tailWord_2840341 prefixEnd_2840341 324102256816039308105559 := by
  unfold tailWord_2840341
  simp only [CollatzResearch.WordTrace]
  refine ⟨103595747002937123467792877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69063831335291415645195251 103595747002937123467792877)
  ·
    refine ⟨38848405126101421300422329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103595747002937123467792877 38848405126101421300422329)
    ·
      refine ⟨29136303844576065975316747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38848405126101421300422329 29136303844576065975316747)
      ·
        refine ⟨43704455766864098962975121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29136303844576065975316747 43704455766864098962975121)
        ·
          refine ⟨32778341825148074222231341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43704455766864098962975121 32778341825148074222231341)
          ·
            refine ⟨12291878184430527833336753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32778341825148074222231341 12291878184430527833336753)
            ·
              refine ⟨9218908638322895875002565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12291878184430527833336753 9218908638322895875002565)
              ·
                refine ⟨1728545369685542976562981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9218908638322895875002565 1728545369685542976562981)
                ·
                  refine ⟨324102256816039308105559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1728545369685542976562981 324102256816039308105559)
                  ·
                    rfl

theorem cell22_2840341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_2840341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840341 prefixEnd_2840341 := by exact prefixLift 2840341
  have htrace : WordTrace (prefixWord ++ tailWord_2840341) baseStart_2840341 baseEnd_2840341 := by
    simpa [prefixWord, tailWord_2840341, baseEnd_2840341] using wordTrace_append hprefix tailTrace_2840341
  have hstable : (prefixWord ++ tailWord_2840341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840341).length < 2 ^ (prefixWord ++ tailWord_2840341).sum := by decide
  have hdescent : baseEnd_2840341 < baseStart_2840341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840354 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2840354 : Nat := 118140960795 + 2840354 * 2 ^ 59
def prefixEnd_2840354 : Nat := 4983230072969 + 3 ^ 40 * 2840354 * 2
def baseEnd_2840354 : Nat := 972311220613790223741637

theorem tailTrace_2840354 : CollatzResearch.WordTrace tailWord_2840354 prefixEnd_2840354 972311220613790223741637 := by
  unfold tailWord_2840354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25899055287972506672004029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69064147434593351125344077 25899055287972506672004029)
  ·
    refine ⟨9712145732989690002001511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25899055287972506672004029 9712145732989690002001511)
    ·
      refine ⟨14568218599484535003002267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9712145732989690002001511 14568218599484535003002267)
      ·
        refine ⟨21852327899226802504503401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14568218599484535003002267 21852327899226802504503401)
        ·
          refine ⟨16389245924420101878377551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21852327899226802504503401 16389245924420101878377551)
          ·
            refine ⟨24583868886630152817566327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16389245924420101878377551 24583868886630152817566327)
            ·
              refine ⟨36875803329945229226349491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24583868886630152817566327 36875803329945229226349491)
              ·
                refine ⟨55313704994917843839524237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36875803329945229226349491 55313704994917843839524237)
                ·
                  refine ⟨20742639373094191439821589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55313704994917843839524237 20742639373094191439821589)
                  ·
                    refine ⟨972311220613790223741637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20742639373094191439821589 972311220613790223741637)
                    ·
                      rfl

theorem cell22_2840354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2840354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840354 prefixEnd_2840354 := by exact prefixLift 2840354
  have htrace : WordTrace (prefixWord ++ tailWord_2840354) baseStart_2840354 baseEnd_2840354 := by
    simpa [prefixWord, tailWord_2840354, baseEnd_2840354] using wordTrace_append hprefix tailTrace_2840354
  have hstable : (prefixWord ++ tailWord_2840354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840354).length < 2 ^ (prefixWord ++ tailWord_2840354).sum := by decide
  have hdescent : baseEnd_2840354 < baseStart_2840354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840356 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_2840356 : Nat := 118140960795 + 2840356 * 2 ^ 59
def prefixEnd_2840356 : Nat := 4983230072969 + 3 ^ 40 * 2840356 * 2
def baseEnd_2840356 : Nat := 972311905254662885191631

theorem tailTrace_2840356 : CollatzResearch.WordTrace tailWord_2840356 prefixEnd_2840356 972311905254662885191631 := by
  unfold tailWord_2840356
  simp only [CollatzResearch.WordTrace]
  refine ⟨51798147048941390514794461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69064196065255187353059281 51798147048941390514794461)
  ·
    refine ⟨19424305143353021443047923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51798147048941390514794461 19424305143353021443047923)
    ·
      refine ⟨29136457715029532164571885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19424305143353021443047923 29136457715029532164571885)
      ·
        refine ⟨10926171643136074561714457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29136457715029532164571885 10926171643136074561714457)
        ·
          refine ⟨8194628732352055921285843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10926171643136074561714457 8194628732352055921285843)
          ·
            refine ⟨12291943098528083881928765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8194628732352055921285843 12291943098528083881928765)
            ·
              refine ⟨4609478661948031455723287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12291943098528083881928765 4609478661948031455723287)
              ·
                refine ⟨6914217992922047183584931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4609478661948031455723287 6914217992922047183584931)
                ·
                  refine ⟨10371326989383070775377397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6914217992922047183584931 10371326989383070775377397)
                  ·
                    refine ⟨972311905254662885191631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10371326989383070775377397 972311905254662885191631)
                    ·
                      rfl

theorem cell22_2840356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_2840356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840356 prefixEnd_2840356 := by exact prefixLift 2840356
  have htrace : WordTrace (prefixWord ++ tailWord_2840356) baseStart_2840356 baseEnd_2840356 := by
    simpa [prefixWord, tailWord_2840356, baseEnd_2840356] using wordTrace_append hprefix tailTrace_2840356
  have hstable : (prefixWord ++ tailWord_2840356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840356).length < 2 ^ (prefixWord ++ tailWord_2840356).sum := by decide
  have hdescent : baseEnd_2840356 < baseStart_2840356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840369 : List Nat := [1, 2, 2, 3, 2, 3, 1, 8]
def baseStart_2840369 : Nat := 118140960795 + 2840369 * 2 ^ 59
def prefixEnd_2840369 : Nat := 4983230072969 + 3 ^ 40 * 2840369 * 2
def baseEnd_2840369 : Nat := 108035150602259464957399

theorem tailTrace_2840369 : CollatzResearch.WordTrace tailWord_2840369 prefixEnd_2840369 108035150602259464957399 := by
  unfold tailWord_2840369
  simp only [CollatzResearch.WordTrace]
  refine ⟨103596768246835684249812161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69064512164557122833208107 103596768246835684249812161)
  ·
    refine ⟨77697576185126763187359121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103596768246835684249812161 77697576185126763187359121)
    ·
      refine ⟨58273182138845072390519341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77697576185126763187359121 58273182138845072390519341)
      ·
        refine ⟨21852443302066902146444753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58273182138845072390519341 21852443302066902146444753)
        ·
          refine ⟨16389332476550176609833565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21852443302066902146444753 16389332476550176609833565)
          ·
            refine ⟨6145999678706316228687587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16389332476550176609833565 6145999678706316228687587)
            ·
              refine ⟨9218999518059474343031381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145999678706316228687587 9218999518059474343031381)
              ·
                refine ⟨108035150602259464957399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9218999518059474343031381 108035150602259464957399)
                ·
                  rfl

theorem cell22_2840369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 8].length) (baseStart_2840369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840369 prefixEnd_2840369 := by exact prefixLift 2840369
  have htrace : WordTrace (prefixWord ++ tailWord_2840369) baseStart_2840369 baseEnd_2840369 := by
    simpa [prefixWord, tailWord_2840369, baseEnd_2840369] using wordTrace_append hprefix tailTrace_2840369
  have hstable : (prefixWord ++ tailWord_2840369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840369).length < 2 ^ (prefixWord ++ tailWord_2840369).sum := by decide
  have hdescent : baseEnd_2840369 < baseStart_2840369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840390 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2840390 : Nat := 118140960795 + 2840390 * 2 ^ 59
def prefixEnd_2840390 : Nat := 4983230072969 + 3 ^ 40 * 2840390 * 2
def baseEnd_2840390 : Nat := 972323544149498129841527

theorem tailTrace_2840390 : CollatzResearch.WordTrace tailWord_2840390 prefixEnd_2840390 972323544149498129841527 := by
  unfold tailWord_2840390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237422943117487651135207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69065022786506403224217749 3237422943117487651135207)
  ·
    refine ⟨4856134414676231476702811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3237422943117487651135207 4856134414676231476702811)
    ·
      refine ⟨7284201622014347215054217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4856134414676231476702811 7284201622014347215054217)
      ·
        refine ⟨5463151216510760411290663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7284201622014347215054217 5463151216510760411290663)
        ·
          refine ⟨8194726824766140616935995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5463151216510760411290663 8194726824766140616935995)
          ·
            refine ⟨12292090237149210925403993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8194726824766140616935995 12292090237149210925403993)
            ·
              refine ⟨9219067677861908194052995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12292090237149210925403993 9219067677861908194052995)
              ·
                refine ⟨13828601516792862291079493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9219067677861908194052995 13828601516792862291079493)
                ·
                  refine ⟨2592862784398661679577405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13828601516792862291079493 2592862784398661679577405)
                  ·
                    refine ⟨972323544149498129841527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2592862784398661679577405 972323544149498129841527)
                    ·
                      rfl

theorem cell22_2840390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2840390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840390 prefixEnd_2840390 := by exact prefixLift 2840390
  have htrace : WordTrace (prefixWord ++ tailWord_2840390) baseStart_2840390 baseEnd_2840390 := by
    simpa [prefixWord, tailWord_2840390, baseEnd_2840390] using wordTrace_append hprefix tailTrace_2840390
  have hstable : (prefixWord ++ tailWord_2840390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840390).length < 2 ^ (prefixWord ++ tailWord_2840390).sum := by decide
  have hdescent : baseEnd_2840390 < baseStart_2840390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840407 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 2, 3]
def baseStart_2840407 : Nat := 118140960795 + 2840407 * 2 ^ 59
def prefixEnd_2840407 : Nat := 4983230072969 + 3 ^ 40 * 2840407 * 2
def baseEnd_2840407 : Nat := 972329363596915752166475

theorem tailTrace_2840407 : CollatzResearch.WordTrace tailWord_2840407 prefixEnd_2840407 972329363596915752166475 := by
  unfold tailWord_2840407
  simp only [CollatzResearch.WordTrace]
  refine ⟨103598154220698016739695475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69065436147132011159796983 103598154220698016739695475)
  ·
    refine ⟨155397231331047025109543213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103598154220698016739695475 155397231331047025109543213)
    ·
      refine ⟨58273961749142634416078705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155397231331047025109543213 58273961749142634416078705)
      ·
        refine ⟨43705471311856975812059029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58273961749142634416078705 43705471311856975812059029)
        ·
          refine ⟨2048693967743295741190267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43705471311856975812059029 2048693967743295741190267)
          ·
            refine ⟨3073040951614943611785401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048693967743295741190267 3073040951614943611785401)
            ·
              refine ⟨2304780713711207708839051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073040951614943611785401 2304780713711207708839051)
              ·
                refine ⟨3457171070566811563258577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304780713711207708839051 3457171070566811563258577)
                ·
                  refine ⟨2592878302925108672443933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457171070566811563258577 2592878302925108672443933)
                  ·
                    refine ⟨972329363596915752166475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2592878302925108672443933 972329363596915752166475)
                    ·
                      rfl

theorem cell22_2840407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_2840407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840407 prefixEnd_2840407 := by exact prefixLift 2840407
  have htrace : WordTrace (prefixWord ++ tailWord_2840407) baseStart_2840407 baseEnd_2840407 := by
    simpa [prefixWord, tailWord_2840407, baseEnd_2840407] using wordTrace_append hprefix tailTrace_2840407
  have hstable : (prefixWord ++ tailWord_2840407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840407).length < 2 ^ (prefixWord ++ tailWord_2840407).sum := by decide
  have hdescent : baseEnd_2840407 < baseStart_2840407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840459 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 6]
def baseStart_2840459 : Nat := 118140960795 + 2840459 * 2 ^ 59
def prefixEnd_2840459 : Nat := 4983230072969 + 3 ^ 40 * 2840459 * 2
def baseEnd_2840459 : Nat := 324115721419868316622105

theorem tailTrace_2840459 : CollatzResearch.WordTrace tailWord_2840459 prefixEnd_2840459 324115721419868316622105 := by
  unfold tailWord_2840459
  simp only [CollatzResearch.WordTrace]
  refine ⟨103600050816509629620588431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69066700544339753080392287 103600050816509629620588431)
  ·
    refine ⟨155400076224764444430882647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103600050816509629620588431 155400076224764444430882647)
    ·
      refine ⟨233100114337146666646323971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155400076224764444430882647 233100114337146666646323971)
      ·
        refine ⟨349650171505719999969485957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233100114337146666646323971 349650171505719999969485957)
        ·
          refine ⟨65559407157322499994278617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349650171505719999969485957 65559407157322499994278617)
          ·
            refine ⟨49169555367991874995708963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65559407157322499994278617 49169555367991874995708963)
            ·
              refine ⟨73754333051987812493563445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49169555367991874995708963 73754333051987812493563445)
              ·
                refine ⟨6914468723623857421271573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73754333051987812493563445 6914468723623857421271573)
                ·
                  refine ⟨324115721419868316622105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6914468723623857421271573 324115721419868316622105)
                  ·
                    rfl

theorem cell22_2840459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 6].length) (baseStart_2840459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840459 prefixEnd_2840459 := by exact prefixLift 2840459
  have htrace : WordTrace (prefixWord ++ tailWord_2840459) baseStart_2840459 baseEnd_2840459 := by
    simpa [prefixWord, tailWord_2840459, baseEnd_2840459] using wordTrace_append hprefix tailTrace_2840459
  have hstable : (prefixWord ++ tailWord_2840459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840459).length < 2 ^ (prefixWord ++ tailWord_2840459).sum := by decide
  have hdescent : baseEnd_2840459 < baseStart_2840459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840476 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 8]
def baseStart_2840476 : Nat := 118140960795 + 2840476 * 2 ^ 59
def prefixEnd_2840476 : Nat := 4983230072969 + 3 ^ 40 * 2840476 * 2
def baseEnd_2840476 : Nat := 324117661235674190730421

theorem tailTrace_2840476 : CollatzResearch.WordTrace tailWord_2840476 prefixEnd_2840476 324117661235674190730421 := by
  unfold tailWord_2840476
  simp only [CollatzResearch.WordTrace]
  refine ⟨51800335428724020761978641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69067113904965361015971521 51800335428724020761978641)
  ·
    refine ⟨38850251571543015571483981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51800335428724020761978641 38850251571543015571483981)
    ·
      refine ⟨14568844339328630839306493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38850251571543015571483981 14568844339328630839306493)
      ·
        refine ⟨5463316627248236564739935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14568844339328630839306493 5463316627248236564739935)
        ·
          refine ⟨8194974940872354847109903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5463316627248236564739935 8194974940872354847109903)
          ·
            refine ⟨12292462411308532270664855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8194974940872354847109903 12292462411308532270664855)
            ·
              refine ⟨18438693616962798405997283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12292462411308532270664855 18438693616962798405997283)
              ·
                refine ⟨27658040425444197608995925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18438693616962798405997283 27658040425444197608995925)
                ·
                  refine ⟨324117661235674190730421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27658040425444197608995925 324117661235674190730421)
                  ·
                    rfl

theorem cell22_2840476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_2840476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840476 prefixEnd_2840476 := by exact prefixLift 2840476
  have htrace : WordTrace (prefixWord ++ tailWord_2840476) baseStart_2840476 baseEnd_2840476 := by
    simpa [prefixWord, tailWord_2840476, baseEnd_2840476] using wordTrace_append hprefix tailTrace_2840476
  have hstable : (prefixWord ++ tailWord_2840476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840476).length < 2 ^ (prefixWord ++ tailWord_2840476).sum := by decide
  have hdescent : baseEnd_2840476 < baseStart_2840476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840504 : List Nat := [2, 1, 2, 1, 2, 3, 11]
def baseStart_2840504 : Nat := 118140960795 + 2840504 * 2 ^ 59
def prefixEnd_2840504 : Nat := 4983230072969 + 3 ^ 40 * 2840504 * 2
def baseEnd_2840504 : Nat := 36013428469601475277451

theorem tailTrace_2840504 : CollatzResearch.WordTrace tailWord_2840504 prefixEnd_2840504 36013428469601475277451 := by
  unfold tailWord_2840504
  simp only [CollatzResearch.WordTrace]
  refine ⟨51800846050673301152988283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69067794734231068203984377 51800846050673301152988283)
  ·
    refine ⟨77701269076009951729482425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51800846050673301152988283 77701269076009951729482425)
    ·
      refine ⟨58275951807007463797111819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77701269076009951729482425 58275951807007463797111819)
      ·
        refine ⟨87413927710511195695667729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58275951807007463797111819 87413927710511195695667729)
        ·
          refine ⟨65560445782883396771750797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87413927710511195695667729 65560445782883396771750797)
          ·
            refine ⟨24585167168581273789406549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65560445782883396771750797 24585167168581273789406549)
            ·
              refine ⟨36013428469601475277451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24585167168581273789406549 36013428469601475277451)
              ·
                rfl

theorem cell22_2840504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 11].length) (baseStart_2840504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840504 prefixEnd_2840504 := by exact prefixLift 2840504
  have htrace : WordTrace (prefixWord ++ tailWord_2840504) baseStart_2840504 baseEnd_2840504 := by
    simpa [prefixWord, tailWord_2840504, baseEnd_2840504] using wordTrace_append hprefix tailTrace_2840504
  have hstable : (prefixWord ++ tailWord_2840504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840504).length < 2 ^ (prefixWord ++ tailWord_2840504).sum := by decide
  have hdescent : baseEnd_2840504 < baseStart_2840504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840583 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 5]
def baseStart_2840583 : Nat := 118140960795 + 2840583 * 2 ^ 59
def prefixEnd_2840583 : Nat := 4983230072969 + 3 ^ 40 * 2840583 * 2
def baseEnd_2840583 : Nat := 324129870664569986588645

theorem tailTrace_2840583 : CollatzResearch.WordTrace tailWord_2840583 prefixEnd_2840583 324129870664569986588645 := by
  unfold tailWord_2840583
  simp only [CollatzResearch.WordTrace]
  refine ⟨103604573468060398798102403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69069715645373599198734935 103604573468060398798102403)
  ·
    refine ⟨155406860202090598197153605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103604573468060398798102403 155406860202090598197153605)
    ·
      refine ⟨29138786287891987161966301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155406860202090598197153605 29138786287891987161966301)
      ·
        refine ⟨10927044857959495185737363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29138786287891987161966301 10927044857959495185737363)
        ·
          refine ⟨16390567286939242778606045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10927044857959495185737363 16390567286939242778606045)
          ·
            refine ⟨6146462732602216041977267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16390567286939242778606045 6146462732602216041977267)
            ·
              refine ⟨9219694098903324062965901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6146462732602216041977267 9219694098903324062965901)
              ·
                refine ⟨3457385287088746523612213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9219694098903324062965901 3457385287088746523612213)
                ·
                  refine ⟨324129870664569986588645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3457385287088746523612213 324129870664569986588645)
                  ·
                    rfl

theorem cell22_2840583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 5].length) (baseStart_2840583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840583 prefixEnd_2840583 := by exact prefixLift 2840583
  have htrace : WordTrace (prefixWord ++ tailWord_2840583) baseStart_2840583 baseEnd_2840583 := by
    simpa [prefixWord, tailWord_2840583, baseEnd_2840583] using wordTrace_append hprefix tailTrace_2840583
  have hstable : (prefixWord ++ tailWord_2840583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840583).length < 2 ^ (prefixWord ++ tailWord_2840583).sum := by decide
  have hdescent : baseEnd_2840583 < baseStart_2840583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840677 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_2840677 : Nat := 118140960795 + 2840677 * 2 ^ 59
def prefixEnd_2840677 : Nat := 4983230072969 + 3 ^ 40 * 2840677 * 2
def baseEnd_2840677 : Nat := 972421790114725047915647

theorem tailTrace_2840677 : CollatzResearch.WordTrace tailWord_2840677 prefixEnd_2840677 972421790114725047915647 := by
  unfold tailWord_2840677
  simp only [CollatzResearch.WordTrace]
  refine ⟨103608001929719852852024285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69072001286479901901349523 103608001929719852852024285)
  ·
    refine ⟨38853000723644944819509107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103608001929719852852024285 38853000723644944819509107)
    ·
      refine ⟨58279501085467417229263661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38853000723644944819509107 58279501085467417229263661)
      ·
        refine ⟨21854812907050281460973873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58279501085467417229263661 21854812907050281460973873)
        ·
          refine ⟨16391109680287711095730405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21854812907050281460973873 16391109680287711095730405)
          ·
            refine ⟨3073333065053945830449451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16391109680287711095730405 3073333065053945830449451)
            ·
              refine ⟨4609999597580918745674177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073333065053945830449451 4609999597580918745674177)
              ·
                refine ⟨3457499698185689059255633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4609999597580918745674177 3457499698185689059255633)
                ·
                  refine ⟨2593124773639266794441725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457499698185689059255633 2593124773639266794441725)
                  ·
                    refine ⟨972421790114725047915647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593124773639266794441725 972421790114725047915647)
                    ·
                      rfl

theorem cell22_2840677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_2840677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840677 prefixEnd_2840677 := by exact prefixLift 2840677
  have htrace : WordTrace (prefixWord ++ tailWord_2840677) baseStart_2840677 baseEnd_2840677 := by
    simpa [prefixWord, tailWord_2840677, baseEnd_2840677] using wordTrace_append hprefix tailTrace_2840677
  have hstable : (prefixWord ++ tailWord_2840677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840677).length < 2 ^ (prefixWord ++ tailWord_2840677).sum := by decide
  have hdescent : baseEnd_2840677 < baseStart_2840677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840694 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_2840694 : Nat := 118140960795 + 2840694 * 2 ^ 59
def prefixEnd_2840694 : Nat := 4983230072969 + 3 ^ 40 * 2840694 * 2
def baseEnd_2840694 : Nat := 972427609562142670240595

theorem tailTrace_2840694 : CollatzResearch.WordTrace tailWord_2840694 prefixEnd_2840694 972427609562142670240595 := by
  unfold tailWord_2840694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475538873166141547212071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69072414647105509836928757 6475538873166141547212071)
  ·
    refine ⟨9713308309749212320818107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6475538873166141547212071 9713308309749212320818107)
    ·
      refine ⟨14569962464623818481227161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9713308309749212320818107 14569962464623818481227161)
      ·
        refine ⟨10927471848467863860920371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14569962464623818481227161 10927471848467863860920371)
        ·
          refine ⟨16391207772701795791380557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10927471848467863860920371 16391207772701795791380557)
          ·
            refine ⟨6146702914763173421767709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16391207772701795791380557 6146702914763173421767709)
            ·
              refine ⟨2305013593036190033162891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6146702914763173421767709 2305013593036190033162891)
              ·
                refine ⟨3457520389554285049744337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305013593036190033162891 3457520389554285049744337)
                ·
                  refine ⟨2593140292165713787308253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457520389554285049744337 2593140292165713787308253)
                  ·
                    refine ⟨972427609562142670240595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593140292165713787308253 972427609562142670240595)
                    ·
                      rfl

theorem cell22_2840694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_2840694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840694 prefixEnd_2840694 := by exact prefixLift 2840694
  have htrace : WordTrace (prefixWord ++ tailWord_2840694) baseStart_2840694 baseEnd_2840694 := by
    simpa [prefixWord, tailWord_2840694, baseEnd_2840694] using wordTrace_append hprefix tailTrace_2840694
  have hstable : (prefixWord ++ tailWord_2840694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840694).length < 2 ^ (prefixWord ++ tailWord_2840694).sum := by decide
  have hdescent : baseEnd_2840694 < baseStart_2840694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840795 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 2, 3]
def baseStart_2840795 : Nat := 118140960795 + 2840795 * 2 ^ 59
def prefixEnd_2840795 : Nat := 4983230072969 + 3 ^ 40 * 2840795 * 2
def baseEnd_2840795 : Nat := 972462183926212073465285

theorem tailTrace_2840795 : CollatzResearch.WordTrace tailWord_2840795 prefixEnd_2840795 972462183926212073465285 := by
  unfold tailWord_2840795
  simp only [CollatzResearch.WordTrace]
  refine ⟨103612305743292359004819839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69074870495528239336546559 103612305743292359004819839)
  ·
    refine ⟨155418458614938538507229759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103612305743292359004819839 155418458614938538507229759)
    ·
      refine ⟨233127687922407807760844639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155418458614938538507229759 233127687922407807760844639)
      ·
        refine ⟨349691531883611711641266959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233127687922407807760844639 349691531883611711641266959)
        ·
          refine ⟨524537297825417567461900439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349691531883611711641266959 524537297825417567461900439)
          ·
            refine ⟨786805946738126351192850659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524537297825417567461900439 786805946738126351192850659)
            ·
              refine ⟨1180208920107189526789275989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786805946738126351192850659 1180208920107189526789275989)
              ·
                refine ⟨3457643320626531816765457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1180208920107189526789275989 3457643320626531816765457)
                ·
                  refine ⟨2593232490469898862574093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457643320626531816765457 2593232490469898862574093)
                  ·
                    refine ⟨972462183926212073465285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593232490469898862574093 972462183926212073465285)
                    ·
                      rfl

theorem cell22_2840795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 3].length) (baseStart_2840795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840795 prefixEnd_2840795 := by exact prefixLift 2840795
  have htrace : WordTrace (prefixWord ++ tailWord_2840795) baseStart_2840795 baseEnd_2840795 := by
    simpa [prefixWord, tailWord_2840795, baseEnd_2840795] using wordTrace_append hprefix tailTrace_2840795
  have hstable : (prefixWord ++ tailWord_2840795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840795).length < 2 ^ (prefixWord ++ tailWord_2840795).sum := by decide
  have hdescent : baseEnd_2840795 < baseStart_2840795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840964 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_2840964 : Nat := 118140960795 + 2840964 * 2 ^ 59
def prefixEnd_2840964 : Nat := 4983230072969 + 3 ^ 40 * 2840964 * 2
def baseEnd_2840964 : Nat := 972520036079951965989767

theorem tailTrace_2840964 : CollatzResearch.WordTrace tailWord_2840964 prefixEnd_2840964 972520036079951965989767 := by
  unfold tailWord_2840964
  simp only [CollatzResearch.WordTrace]
  refine ⟨51809234839840050433860973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69078979786453400578481297 51809234839840050433860973)
  ·
    refine ⟨19428463064940018912697865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51809234839840050433860973 19428463064940018912697865)
    ·
      refine ⟨14571347298705014184523399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19428463064940018912697865 14571347298705014184523399)
      ·
        refine ⟨21857020948057521276785099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14571347298705014184523399 21857020948057521276785099)
        ·
          refine ⟨32785531422086281915177649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21857020948057521276785099 32785531422086281915177649)
          ·
            refine ⟨24589148566564711436383237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32785531422086281915177649 24589148566564711436383237)
            ·
              refine ⟨4610465356230883394321857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24589148566564711436383237 4610465356230883394321857)
              ·
                refine ⟨3457849017173162545741393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610465356230883394321857 3457849017173162545741393)
                ·
                  refine ⟨2593386762879871909306045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457849017173162545741393 2593386762879871909306045)
                  ·
                    refine ⟨972520036079951965989767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593386762879871909306045 972520036079951965989767)
                    ·
                      rfl

theorem cell22_2840964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_2840964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840964 prefixEnd_2840964 := by exact prefixLift 2840964
  have htrace : WordTrace (prefixWord ++ tailWord_2840964) baseStart_2840964 baseEnd_2840964 := by
    simpa [prefixWord, tailWord_2840964, baseEnd_2840964] using wordTrace_append hprefix tailTrace_2840964
  have hstable : (prefixWord ++ tailWord_2840964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840964).length < 2 ^ (prefixWord ++ tailWord_2840964).sum := by decide
  have hdescent : baseEnd_2840964 < baseStart_2840964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840992 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 5, 3]
def baseStart_2840992 : Nat := 118140960795 + 2840992 * 2 ^ 59
def prefixEnd_2840992 : Nat := 4983230072969 + 3 ^ 40 * 2840992 * 2
def baseEnd_2840992 : Nat := 972529621052169226289681

theorem tailTrace_2840992 : CollatzResearch.WordTrace tailWord_2840992 prefixEnd_2840992 972529621052169226289681 := by
  unfold tailWord_2840992
  simp only [CollatzResearch.WordTrace]
  refine ⟨51809745461789330824870615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69079660615719107766494153 51809745461789330824870615)
  ·
    refine ⟨77714618192683996237305923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51809745461789330824870615 77714618192683996237305923)
    ·
      refine ⟨116571927289025994355958885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77714618192683996237305923 116571927289025994355958885)
      ·
        refine ⟨21857236366692373941742291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116571927289025994355958885 21857236366692373941742291)
        ·
          refine ⟨32785854550038560912613437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21857236366692373941742291 32785854550038560912613437)
          ·
            refine ⟨12294695456264460342230039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32785854550038560912613437 12294695456264460342230039)
            ·
              refine ⟨18442043184396690513345059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12294695456264460342230039 18442043184396690513345059)
              ·
                refine ⟨27663064776595035770017589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18442043184396690513345059 27663064776595035770017589)
                ·
                  refine ⟨2593412322805784603439149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27663064776595035770017589 2593412322805784603439149)
                  ·
                    refine ⟨972529621052169226289681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593412322805784603439149 972529621052169226289681)
                    ·
                      rfl

theorem cell22_2840992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_2840992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2840992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2840992 prefixEnd_2840992 := by exact prefixLift 2840992
  have htrace : WordTrace (prefixWord ++ tailWord_2840992) baseStart_2840992 baseEnd_2840992 := by
    simpa [prefixWord, tailWord_2840992, baseEnd_2840992] using wordTrace_append hprefix tailTrace_2840992
  have hstable : (prefixWord ++ tailWord_2840992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840992).length < 2 ^ (prefixWord ++ tailWord_2840992).sum := by decide
  have hdescent : baseEnd_2840992 < baseStart_2840992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841002 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2841002 : Nat := 118140960795 + 2841002 * 2 ^ 59
def prefixEnd_2841002 : Nat := 4983230072969 + 3 ^ 40 * 2841002 * 2
def baseEnd_2841002 : Nat := 972533044256532533539651

theorem tailTrace_2841002 : CollatzResearch.WordTrace tailWord_2841002 prefixEnd_2841002 972533044256532533539651 := by
  unfold tailWord_2841002
  simp only [CollatzResearch.WordTrace]
  refine ⟨25904963913385608339401315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69079903769028288905070173 25904963913385608339401315)
  ·
    refine ⟨38857445870078412509101973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25904963913385608339401315 38857445870078412509101973)
    ·
      refine ⟨1821442775159925586364155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38857445870078412509101973 1821442775159925586364155)
      ·
        refine ⟨2732164162739888379546233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821442775159925586364155 2732164162739888379546233)
        ·
          refine ⟨2049123122054916284659675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732164162739888379546233 2049123122054916284659675)
          ·
            refine ⟨3073684683082374426989513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049123122054916284659675 3073684683082374426989513)
            ·
              refine ⟨2305263512311780820242135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073684683082374426989513 2305263512311780820242135)
              ·
                refine ⟨3457895268467671230363203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305263512311780820242135 3457895268467671230363203)
                ·
                  refine ⟨5186842902701506845544805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457895268467671230363203 5186842902701506845544805)
                  ·
                    refine ⟨972533044256532533539651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5186842902701506845544805 972533044256532533539651)
                    ·
                      rfl

theorem cell22_2841002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2841002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841002 prefixEnd_2841002 := by exact prefixLift 2841002
  have htrace : WordTrace (prefixWord ++ tailWord_2841002) baseStart_2841002 baseEnd_2841002 := by
    simpa [prefixWord, tailWord_2841002, baseEnd_2841002] using wordTrace_append hprefix tailTrace_2841002
  have hstable : (prefixWord ++ tailWord_2841002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841002).length < 2 ^ (prefixWord ++ tailWord_2841002).sum := by decide
  have hdescent : baseEnd_2841002 < baseStart_2841002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841090 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2841090 : Nat := 118140960795 + 2841090 * 2 ^ 59
def prefixEnd_2841090 : Nat := 4983230072969 + 3 ^ 40 * 2841090 * 2
def baseEnd_2841090 : Nat := 324187722818309879113127

theorem tailTrace_2841090 : CollatzResearch.WordTrace tailWord_2841090 prefixEnd_2841090 324187722818309879113127 := by
  unfold tailWord_2841090
  simp only [CollatzResearch.WordTrace]
  refine ⟨25905766319305906096702181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69082043518149082924539149 25905766319305906096702181)
  ·
    refine ⟨4857331184869857393131659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25905766319305906096702181 4857331184869857393131659)
    ·
      refine ⟨7285996777304786089697489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4857331184869857393131659 7285996777304786089697489)
      ·
        refine ⟨5464497582978589567273117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7285996777304786089697489 5464497582978589567273117)
        ·
          refine ⟨2049186593616971087727419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5464497582978589567273117 2049186593616971087727419)
          ·
            refine ⟨3073779890425456631591129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049186593616971087727419 3073779890425456631591129)
            ·
              refine ⟨2305334917819092473693347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073779890425456631591129 2305334917819092473693347)
              ·
                refine ⟨3458002376728638710540021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305334917819092473693347 3458002376728638710540021)
                ·
                  refine ⟨324187722818309879113127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3458002376728638710540021 324187722818309879113127)
                  ·
                    rfl

theorem cell22_2841090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2841090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841090 prefixEnd_2841090 := by exact prefixLift 2841090
  have htrace : WordTrace (prefixWord ++ tailWord_2841090) baseStart_2841090 baseEnd_2841090 := by
    simpa [prefixWord, tailWord_2841090, baseEnd_2841090] using wordTrace_append hprefix tailTrace_2841090
  have hstable : (prefixWord ++ tailWord_2841090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841090).length < 2 ^ (prefixWord ++ tailWord_2841090).sum := by decide
  have hdescent : baseEnd_2841090 < baseStart_2841090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841112 : List Nat := [2, 1, 2, 3, 3, 1, 2, 8]
def baseStart_2841112 : Nat := 118140960795 + 2841112 * 2 ^ 59
def prefixEnd_2841112 : Nat := 4983230072969 + 3 ^ 40 * 2841112 * 2
def baseEnd_2841112 : Nat := 108063411056058768143257

theorem tailTrace_2841112 : CollatzResearch.WordTrace tailWord_2841112 prefixEnd_2841112 108063411056058768143257 := by
  unfold tailWord_2841112
  simp only [CollatzResearch.WordTrace]
  refine ⟨51811933841571961072054795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69082578455429281429406393 51811933841571961072054795)
  ·
    refine ⟨77717900762357941608082193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51811933841571961072054795 77717900762357941608082193)
    ·
      refine ⟨58288425571768456206061645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77717900762357941608082193 58288425571768456206061645)
      ·
        refine ⟨21858159589413171077273117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58288425571768456206061645 21858159589413171077273117)
        ·
          refine ⟨8196809846029939153977419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21858159589413171077273117 8196809846029939153977419)
          ·
            refine ⟨12295214769044908730966129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8196809846029939153977419 12295214769044908730966129)
            ·
              refine ⟨9221411076783681548224597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12295214769044908730966129 9221411076783681548224597)
              ·
                refine ⟨108063411056058768143257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9221411076783681548224597 108063411056058768143257)
                ·
                  rfl

theorem cell22_2841112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 8].length) (baseStart_2841112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841112 prefixEnd_2841112 := by exact prefixLift 2841112
  have htrace : WordTrace (prefixWord ++ tailWord_2841112) baseStart_2841112 baseEnd_2841112 := by
    simpa [prefixWord, tailWord_2841112, baseEnd_2841112] using wordTrace_append hprefix tailTrace_2841112
  have hstable : (prefixWord ++ tailWord_2841112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841112).length < 2 ^ (prefixWord ++ tailWord_2841112).sum := by decide
  have hdescent : baseEnd_2841112 < baseStart_2841112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841144 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 3, 3]
def baseStart_2841144 : Nat := 118140960795 + 2841144 * 2 ^ 59
def prefixEnd_2841144 : Nat := 4983230072969 + 3 ^ 40 * 2841144 * 2
def baseEnd_2841144 : Nat := 972581653758491496489215

theorem tailTrace_2841144 : CollatzResearch.WordTrace tailWord_2841144 prefixEnd_2841144 972581653758491496489215 := by
  unfold tailWord_2841144
  simp only [CollatzResearch.WordTrace]
  refine ⟨51812517409513995804637243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69083356546018661072849657 51812517409513995804637243)
  ·
    refine ⟨77718776114270993706955865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51812517409513995804637243 77718776114270993706955865)
    ·
      refine ⟨58289082085703245280216899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77718776114270993706955865 58289082085703245280216899)
      ·
        refine ⟨87433623128554867920325349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58289082085703245280216899 87433623128554867920325349)
        ·
          refine ⟨16393804336604037735061003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87433623128554867920325349 16393804336604037735061003)
          ·
            refine ⟨24590706504906056602591505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16393804336604037735061003 24590706504906056602591505)
            ·
              refine ⟨18443029878679542451943629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24590706504906056602591505 18443029878679542451943629)
              ·
                refine ⟨6916136204504828419478861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18443029878679542451943629 6916136204504828419478861)
                ·
                  refine ⟨2593551076689310657304573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6916136204504828419478861 2593551076689310657304573)
                  ·
                    refine ⟨972581653758491496489215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593551076689310657304573 972581653758491496489215)
                    ·
                      rfl

theorem cell22_2841144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_2841144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841144 prefixEnd_2841144 := by exact prefixLift 2841144
  have htrace : WordTrace (prefixWord ++ tailWord_2841144) baseStart_2841144 baseEnd_2841144 := by
    simpa [prefixWord, tailWord_2841144, baseEnd_2841144] using wordTrace_append hprefix tailTrace_2841144
  have hstable : (prefixWord ++ tailWord_2841144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841144).length < 2 ^ (prefixWord ++ tailWord_2841144).sum := by decide
  have hdescent : baseEnd_2841144 < baseStart_2841144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841221 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_2841221 : Nat := 118140960795 + 2841221 * 2 ^ 59
def prefixEnd_2841221 : Nat := 4983230072969 + 3 ^ 40 * 2841221 * 2
def baseEnd_2841221 : Nat := 972608012432088962313979

theorem tailTrace_2841221 : CollatzResearch.WordTrace tailWord_2841221 prefixEnd_2841221 972608012432088962313979 := by
  unfold tailWord_2841221
  simp only [CollatzResearch.WordTrace]
  refine ⟨103627843239749033759827517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69085228826499355839885011 103627843239749033759827517)
  ·
    refine ⟨38860441214905887659935319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103627843239749033759827517 38860441214905887659935319)
    ·
      refine ⟨58290661822358831489902979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38860441214905887659935319 58290661822358831489902979)
      ·
        refine ⟨87435992733538247234854469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58290661822358831489902979 87435992733538247234854469)
        ·
          refine ⟨16394248637538421356535213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87435992733538247234854469 16394248637538421356535213)
          ·
            refine ⟨6147843239076908008700705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16394248637538421356535213 6147843239076908008700705)
            ·
              refine ⟨4610882429307681006525529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6147843239076908008700705 4610882429307681006525529)
              ·
                refine ⟨3458161821980760754894147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610882429307681006525529 3458161821980760754894147)
                ·
                  refine ⟨5187242732971141132341221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458161821980760754894147 5187242732971141132341221)
                  ·
                    refine ⟨972608012432088962313979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187242732971141132341221 972608012432088962313979)
                    ·
                      rfl

theorem cell22_2841221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_2841221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841221 prefixEnd_2841221 := by exact prefixLift 2841221
  have htrace : WordTrace (prefixWord ++ tailWord_2841221) baseStart_2841221 baseEnd_2841221 := by
    simpa [prefixWord, tailWord_2841221, baseEnd_2841221] using wordTrace_append hprefix tailTrace_2841221
  have hstable : (prefixWord ++ tailWord_2841221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841221).length < 2 ^ (prefixWord ++ tailWord_2841221).sum := by decide
  have hdescent : baseEnd_2841221 < baseStart_2841221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841326 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_2841326 : Nat := 118140960795 + 2841326 * 2 ^ 59
def prefixEnd_2841326 : Nat := 4983230072969 + 3 ^ 40 * 2841326 * 2
def baseEnd_2841326 : Nat := 324214652025967896146219

theorem tailTrace_2841326 : CollatzResearch.WordTrace tailWord_2841326 prefixEnd_2841326 324214652025967896146219 := by
  unfold tailWord_2841326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12953959113046079586549979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69087781936245757794933221 12953959113046079586549979)
  ·
    refine ⟨19430938669569119379824969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12953959113046079586549979 19430938669569119379824969)
    ·
      refine ⟨14573204002176839534868727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19430938669569119379824969 14573204002176839534868727)
      ·
        refine ⟨21859806003265259302303091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14573204002176839534868727 21859806003265259302303091)
        ·
          refine ⟨32789709004897888953454637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21859806003265259302303091 32789709004897888953454637)
          ·
            refine ⟨12296140876836708357545489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32789709004897888953454637 12296140876836708357545489)
            ·
              refine ⟨9222105657627531268159117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12296140876836708357545489 9222105657627531268159117)
              ·
                refine ⟨3458289621610324225559669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9222105657627531268159117 3458289621610324225559669)
                ·
                  refine ⟨324214652025967896146219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3458289621610324225559669 324214652025967896146219)
                  ·
                    rfl

theorem cell22_2841326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_2841326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841326 prefixEnd_2841326 := by exact prefixLift 2841326
  have htrace : WordTrace (prefixWord ++ tailWord_2841326) baseStart_2841326 baseEnd_2841326 := by
    simpa [prefixWord, tailWord_2841326, baseEnd_2841326] using wordTrace_append hprefix tailTrace_2841326
  have hstable : (prefixWord ++ tailWord_2841326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841326).length < 2 ^ (prefixWord ++ tailWord_2841326).sum := by decide
  have hdescent : baseEnd_2841326 < baseStart_2841326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841354 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_2841354 : Nat := 118140960795 + 2841354 * 2 ^ 59
def prefixEnd_2841354 : Nat := 4983230072969 + 3 ^ 40 * 2841354 * 2
def baseEnd_2841354 : Nat := 324217847016706982912857

theorem tailTrace_2841354 : CollatzResearch.WordTrace tailWord_2841354 prefixEnd_2841354 324217847016706982912857 := by
  unfold tailWord_2841354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25908173537066799368604779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69088462765511464982946077 25908173537066799368604779)
  ·
    refine ⟨38862260305600199052907169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25908173537066799368604779 38862260305600199052907169)
    ·
      refine ⟨29146695229200149289680377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38862260305600199052907169 29146695229200149289680377)
      ·
        refine ⟨21860021421900111967260283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29146695229200149289680377 21860021421900111967260283)
        ·
          refine ⟨32790032132850167950890425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21860021421900111967260283 32790032132850167950890425)
          ·
            refine ⟨24592524099637625963167819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32790032132850167950890425 24592524099637625963167819)
            ·
              refine ⟨36888786149456438944751729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24592524099637625963167819 36888786149456438944751729)
              ·
                refine ⟨27666589612092329208563797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36888786149456438944751729 27666589612092329208563797)
                ·
                  refine ⟨324217847016706982912857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27666589612092329208563797 324217847016706982912857)
                  ·
                    rfl

theorem cell22_2841354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_2841354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841354 prefixEnd_2841354 := by exact prefixLift 2841354
  have htrace : WordTrace (prefixWord ++ tailWord_2841354) baseStart_2841354 baseEnd_2841354 := by
    simpa [prefixWord, tailWord_2841354, baseEnd_2841354] using wordTrace_append hprefix tailTrace_2841354
  have hstable : (prefixWord ++ tailWord_2841354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841354).length < 2 ^ (prefixWord ++ tailWord_2841354).sum := by decide
  have hdescent : baseEnd_2841354 < baseStart_2841354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841390 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2841390 : Nat := 118140960795 + 2841390 * 2 ^ 59
def prefixEnd_2841390 : Nat := 4983230072969 + 3 ^ 40 * 2841390 * 2
def baseEnd_2841390 : Nat := 972665864585828854838461

theorem tailTrace_2841390 : CollatzResearch.WordTrace tailWord_2841390 prefixEnd_2841390 972665864585828854838461 := by
  unfold tailWord_2841390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12954250897017096952841203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69089338117424517081819749 12954250897017096952841203)
  ·
    refine ⟨19431376345525645429261805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12954250897017096952841203 19431376345525645429261805)
    ·
      refine ⟨7286766129572117035973177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19431376345525645429261805 7286766129572117035973177)
      ·
        refine ⟨5465074597179087776979883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7286766129572117035973177 5465074597179087776979883)
        ·
          refine ⟨8197611895768631665469825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5465074597179087776979883 8197611895768631665469825)
          ·
            refine ⟨6148208921826473749102369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8197611895768631665469825 6148208921826473749102369)
            ·
              refine ⟨4611156691369855311826777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6148208921826473749102369 4611156691369855311826777)
              ·
                refine ⟨3458367518527391483870083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4611156691369855311826777 3458367518527391483870083)
                ·
                  refine ⟨5187551277791087225805125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458367518527391483870083 5187551277791087225805125)
                  ·
                    refine ⟨972665864585828854838461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187551277791087225805125 972665864585828854838461)
                    ·
                      rfl

theorem cell22_2841390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2841390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841390 prefixEnd_2841390 := by exact prefixLift 2841390
  have htrace : WordTrace (prefixWord ++ tailWord_2841390) baseStart_2841390 baseEnd_2841390 := by
    simpa [prefixWord, tailWord_2841390, baseEnd_2841390] using wordTrace_append hprefix tailTrace_2841390
  have hstable : (prefixWord ++ tailWord_2841390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841390).length < 2 ^ (prefixWord ++ tailWord_2841390).sum := by decide
  have hdescent : baseEnd_2841390 < baseStart_2841390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841399 : List Nat := [1, 1, 3, 1, 2, 1, 5, 8]
def baseStart_2841399 : Nat := 118140960795 + 2841399 * 2 ^ 59
def prefixEnd_2841399 : Nat := 4983230072969 + 3 ^ 40 * 2841399 * 2
def baseEnd_2841399 : Nat := 108074327274417314595937

theorem tailTrace_2841399 : CollatzResearch.WordTrace tailWord_2841399 prefixEnd_2841399 108074327274417314595937 := by
  unfold tailWord_2841399
  simp only [CollatzResearch.WordTrace]
  refine ⟨103634335433104170159807251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69089556955402780106538167 103634335433104170159807251)
  ·
    refine ⟨155451503149656255239710877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103634335433104170159807251 155451503149656255239710877)
    ·
      refine ⟨58294313681121095714891579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155451503149656255239710877 58294313681121095714891579)
      ·
        refine ⟨87441470521681643572337369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58294313681121095714891579 87441470521681643572337369)
        ·
          refine ⟨65581102891261232679253027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87441470521681643572337369 65581102891261232679253027)
          ·
            refine ⟨98371654336891849018879541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65581102891261232679253027 98371654336891849018879541)
            ·
              refine ⟨9222342594083610845519957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98371654336891849018879541 9222342594083610845519957)
              ·
                refine ⟨108074327274417314595937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9222342594083610845519957 108074327274417314595937)
                ·
                  rfl

theorem cell22_2841399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 8].length) (baseStart_2841399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841399 prefixEnd_2841399 := by exact prefixLift 2841399
  have htrace : WordTrace (prefixWord ++ tailWord_2841399) baseStart_2841399 baseEnd_2841399 := by
    simpa [prefixWord, tailWord_2841399, baseEnd_2841399] using wordTrace_append hprefix tailTrace_2841399
  have hstable : (prefixWord ++ tailWord_2841399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841399).length < 2 ^ (prefixWord ++ tailWord_2841399).sum := by decide
  have hdescent : baseEnd_2841399 < baseStart_2841399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841476 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2841476 : Nat := 118140960795 + 2841476 * 2 ^ 59
def prefixEnd_2841476 : Nat := 4983230072969 + 3 ^ 40 * 2841476 * 2
def baseEnd_2841476 : Nat := 972695304143353297188197

theorem tailTrace_2841476 : CollatzResearch.WordTrace tailWord_2841476 prefixEnd_2841476 972695304143353297188197 := by
  unfold tailWord_2841476
  simp only [CollatzResearch.WordTrace]
  refine ⟨51818571926912606155180141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69091429235883474873573521 51818571926912606155180141)
  ·
    refine ⟨19431964472592227308192553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51818571926912606155180141 19431964472592227308192553)
    ·
      refine ⟨14573973354444170481144415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19431964472592227308192553 14573973354444170481144415)
      ·
        refine ⟨21860960031666255721716623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14573973354444170481144415 21860960031666255721716623)
        ·
          refine ⟨32791440047499383582574935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21860960031666255721716623 32791440047499383582574935)
          ·
            refine ⟨49187160071249075373862403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32791440047499383582574935 49187160071249075373862403)
            ·
              refine ⟨73780740106873613060793605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49187160071249075373862403 73780740106873613060793605)
              ·
                refine ⟨13833888770038802448898801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73780740106873613060793605 13833888770038802448898801)
                ·
                  refine ⟨10375416577529101836674101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13833888770038802448898801 10375416577529101836674101)
                  ·
                    refine ⟨972695304143353297188197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10375416577529101836674101 972695304143353297188197)
                    ·
                      rfl

theorem cell22_2841476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2841476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841476 prefixEnd_2841476 := by exact prefixLift 2841476
  have htrace : WordTrace (prefixWord ++ tailWord_2841476) baseStart_2841476 baseEnd_2841476 := by
    simpa [prefixWord, tailWord_2841476, baseEnd_2841476] using wordTrace_append hprefix tailTrace_2841476
  have hstable : (prefixWord ++ tailWord_2841476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841476).length < 2 ^ (prefixWord ++ tailWord_2841476).sum := by decide
  have hdescent : baseEnd_2841476 < baseStart_2841476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841482 : List Nat := [3, 1, 2, 4, 1, 2, 1, 4, 1, 3]
def baseStart_2841482 : Nat := 118140960795 + 2841482 * 2 ^ 59
def prefixEnd_2841482 : Nat := 4983230072969 + 3 ^ 40 * 2841482 * 2
def baseEnd_2841482 : Nat := 972697358065971281538179

theorem tailTrace_2841482 : CollatzResearch.WordTrace tailWord_2841482 prefixEnd_2841482 972697358065971281538179 := by
  unfold tailWord_2841482
  simp only [CollatzResearch.WordTrace]
  refine ⟨25909340672950868833769675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69091575127868983556719133 25909340672950868833769675)
  ·
    refine ⟨38864011009426303250654513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25909340672950868833769675 38864011009426303250654513)
    ·
      refine ⟨29148008257069727437990885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38864011009426303250654513 29148008257069727437990885)
      ·
        refine ⟨5465251548200573894623291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29148008257069727437990885 5465251548200573894623291)
        ·
          refine ⟨8197877322300860841934937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5465251548200573894623291 8197877322300860841934937)
          ·
            refine ⟨6148407991725645631451203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8197877322300860841934937 6148407991725645631451203)
            ·
              refine ⟨9222611987588468447176805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6148407991725645631451203 9222611987588468447176805)
              ·
                refine ⟨1729239747672837833845651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9222611987588468447176805 1729239747672837833845651)
                ·
                  refine ⟨2593859621509256750768477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729239747672837833845651 2593859621509256750768477)
                  ·
                    refine ⟨972697358065971281538179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593859621509256750768477 972697358065971281538179)
                    ·
                      rfl

theorem cell22_2841482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_2841482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841482 prefixEnd_2841482 := by exact prefixLift 2841482
  have htrace : WordTrace (prefixWord ++ tailWord_2841482) baseStart_2841482 baseEnd_2841482 := by
    simpa [prefixWord, tailWord_2841482, baseEnd_2841482] using wordTrace_append hprefix tailTrace_2841482
  have hstable : (prefixWord ++ tailWord_2841482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841482).length < 2 ^ (prefixWord ++ tailWord_2841482).sum := by decide
  have hdescent : baseEnd_2841482 < baseStart_2841482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841508 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_2841508 : Nat := 118140960795 + 2841508 * 2 ^ 59
def prefixEnd_2841508 : Nat := 4983230072969 + 3 ^ 40 * 2841508 * 2
def baseEnd_2841508 : Nat := 972706258397315880388099

theorem tailTrace_2841508 : CollatzResearch.WordTrace tailWord_2841508 prefixEnd_2841508 972706258397315880388099 := by
  unfold tailWord_2841508
  simp only [CollatzResearch.WordTrace]
  refine ⟨51819155494854640887762589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69092207326472854517016785 51819155494854640887762589)
  ·
    refine ⟨19432183310570490332910971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51819155494854640887762589 19432183310570490332910971)
    ·
      refine ⟨29148274965855735499366457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19432183310570490332910971 29148274965855735499366457)
      ·
        refine ⟨21861206224391801624524843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29148274965855735499366457 21861206224391801624524843)
        ·
          refine ⟨32791809336587702436787265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21861206224391801624524843 32791809336587702436787265)
          ·
            refine ⟨24593857002440776827590449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32791809336587702436787265 24593857002440776827590449)
            ·
              refine ⟨18445392751830582620692837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24593857002440776827590449 18445392751830582620692837)
              ·
                refine ⟨3458511140968234241379907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18445392751830582620692837 3458511140968234241379907)
                ·
                  refine ⟨5187766711452351362069861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458511140968234241379907 5187766711452351362069861)
                  ·
                    refine ⟨972706258397315880388099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187766711452351362069861 972706258397315880388099)
                    ·
                      rfl

theorem cell22_2841508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_2841508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841508 prefixEnd_2841508 := by exact prefixLift 2841508
  have htrace : WordTrace (prefixWord ++ tailWord_2841508) baseStart_2841508 baseEnd_2841508 := by
    simpa [prefixWord, tailWord_2841508, baseEnd_2841508] using wordTrace_append hprefix tailTrace_2841508
  have hstable : (prefixWord ++ tailWord_2841508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841508).length < 2 ^ (prefixWord ++ tailWord_2841508).sum := by decide
  have hdescent : baseEnd_2841508 < baseStart_2841508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841570 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2841570 : Nat := 118140960795 + 2841570 * 2 ^ 59
def prefixEnd_2841570 : Nat := 4983230072969 + 3 ^ 40 * 2841570 * 2
def baseEnd_2841570 : Nat := 972727482264368385337909

theorem tailTrace_2841570 : CollatzResearch.WordTrace tailWord_2841570 prefixEnd_2841570 972727482264368385337909 := by
  unfold tailWord_2841570
  simp only [CollatzResearch.WordTrace]
  refine ⟨25910143078871166591070541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69093714876989777576188109 25910143078871166591070541)
  ·
    refine ⟨9716303654576687471651453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25910143078871166591070541 9716303654576687471651453)
    ·
      refine ⟨3643613870466257801869295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9716303654576687471651453 3643613870466257801869295)
      ·
        refine ⟨5465420805699386702803943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3643613870466257801869295 5465420805699386702803943)
        ·
          refine ⟨8198131208549080054205915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5465420805699386702803943 8198131208549080054205915)
          ·
            refine ⟨12297196812823620081308873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8198131208549080054205915 12297196812823620081308873)
            ·
              refine ⟨9222897609617715060981655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12297196812823620081308873 9222897609617715060981655)
              ·
                refine ⟨13834346414426572591472483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9222897609617715060981655 13834346414426572591472483)
                ·
                  refine ⟨20751519621639858887208725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13834346414426572591472483 20751519621639858887208725)
                  ·
                    refine ⟨972727482264368385337909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20751519621639858887208725 972727482264368385337909)
                    ·
                      rfl

theorem cell22_2841570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2841570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841570 prefixEnd_2841570 := by exact prefixLift 2841570
  have htrace : WordTrace (prefixWord ++ tailWord_2841570) baseStart_2841570 baseEnd_2841570 := by
    simpa [prefixWord, tailWord_2841570, baseEnd_2841570] using wordTrace_append hprefix tailTrace_2841570
  have hstable : (prefixWord ++ tailWord_2841570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841570).length < 2 ^ (prefixWord ++ tailWord_2841570).sum := by decide
  have hdescent : baseEnd_2841570 < baseStart_2841570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841602 : List Nat := [3, 4, 1, 3, 1, 1, 2, 7]
def baseStart_2841602 : Nat := 118140960795 + 2841602 * 2 ^ 59
def prefixEnd_2841602 : Nat := 4983230072969 + 3 ^ 40 * 2841602 * 2
def baseEnd_2841602 : Nat := 108082048502036774281979

theorem tailTrace_2841602 : CollatzResearch.WordTrace tailWord_2841602 prefixEnd_2841602 108082048502036774281979 := by
  unfold tailWord_2841602
  simp only [CollatzResearch.WordTrace]
  refine ⟨25910434862842183957361765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69094492967579157219631373 25910434862842183957361765)
  ·
    refine ⟨4858206536782909492005331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25910434862842183957361765 4858206536782909492005331)
    ·
      refine ⟨7287309805174364238007997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4858206536782909492005331 7287309805174364238007997)
      ·
        refine ⟨2732741176940386589252999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7287309805174364238007997 2732741176940386589252999)
        ·
          refine ⟨4099111765410579883879499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2732741176940386589252999 4099111765410579883879499)
          ·
            refine ⟨6148667648115869825819249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4099111765410579883879499 6148667648115869825819249)
            ·
              refine ⟨4611500736086902369364437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6148667648115869825819249 4611500736086902369364437)
              ·
                refine ⟨108082048502036774281979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4611500736086902369364437 108082048502036774281979)
                ·
                  rfl

theorem cell22_2841602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_2841602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841602 prefixEnd_2841602 := by exact prefixLift 2841602
  have htrace : WordTrace (prefixWord ++ tailWord_2841602) baseStart_2841602 baseEnd_2841602 := by
    simpa [prefixWord, tailWord_2841602, baseEnd_2841602] using wordTrace_append hprefix tailTrace_2841602
  have hstable : (prefixWord ++ tailWord_2841602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841602).length < 2 ^ (prefixWord ++ tailWord_2841602).sum := by decide
  have hdescent : baseEnd_2841602 < baseStart_2841602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841688 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_2841688 : Nat := 118140960795 + 2841688 * 2 ^ 59
def prefixEnd_2841688 : Nat := 4983230072969 + 3 ^ 40 * 2841688 * 2
def baseEnd_2841688 : Nat := 972767876075855410887547

theorem tailTrace_2841688 : CollatzResearch.WordTrace tailWord_2841688 prefixEnd_2841688 972767876075855410887547 := by
  unfold tailWord_2841688
  simp only [CollatzResearch.WordTrace]
  refine ⟨51822438064528586258538859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69096584086038115011385145 51822438064528586258538859)
  ·
    refine ⟨77733657096792879387808289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51822438064528586258538859 77733657096792879387808289)
    ·
      refine ⟨58300242822594659540856217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77733657096792879387808289 58300242822594659540856217)
      ·
        refine ⟨43725182116945994655642163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58300242822594659540856217 43725182116945994655642163)
        ·
          refine ⟨65587773175418991983463245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43725182116945994655642163 65587773175418991983463245)
          ·
            refine ⟨24595414940782121993798717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65587773175418991983463245 24595414940782121993798717)
            ·
              refine ⟨9223280602793295747674519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24595414940782121993798717 9223280602793295747674519)
              ·
                refine ⟨13834920904189943621511779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9223280602793295747674519 13834920904189943621511779)
                ·
                  refine ⟨20752381356284915432267669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13834920904189943621511779 20752381356284915432267669)
                  ·
                    refine ⟨972767876075855410887547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20752381356284915432267669 972767876075855410887547)
                    ·
                      rfl

theorem cell22_2841688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_2841688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841688 prefixEnd_2841688 := by exact prefixLift 2841688
  have htrace : WordTrace (prefixWord ++ tailWord_2841688) baseStart_2841688 baseEnd_2841688 := by
    simpa [prefixWord, tailWord_2841688, baseEnd_2841688] using wordTrace_append hprefix tailTrace_2841688
  have hstable : (prefixWord ++ tailWord_2841688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841688).length < 2 ^ (prefixWord ++ tailWord_2841688).sum := by decide
  have hdescent : baseEnd_2841688 < baseStart_2841688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841692 : List Nat := [2, 2, 4, 1, 1, 1, 4, 3, 4]
def baseStart_2841692 : Nat := 118140960795 + 2841692 * 2 ^ 59
def prefixEnd_2841692 : Nat := 4983230072969 + 3 ^ 40 * 2841692 * 2
def baseEnd_2841692 : Nat := 324256415119200244595845

theorem tailTrace_2841692 : CollatzResearch.WordTrace tailWord_2841692 prefixEnd_2841692 324256415119200244595845 := by
  unfold tailWord_2841692
  simp only [CollatzResearch.WordTrace]
  refine ⟨51822511010521340600111665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69096681347361787466815553 51822511010521340600111665)
  ·
    refine ⟨38866883257891005450083749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51822511010521340600111665 38866883257891005450083749)
    ·
      refine ⟨7287540610854563521890703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38866883257891005450083749 7287540610854563521890703)
      ·
        refine ⟨10931310916281845282836055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7287540610854563521890703 10931310916281845282836055)
        ·
          refine ⟨16396966374422767924254083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10931310916281845282836055 16396966374422767924254083)
          ·
            refine ⟨24595449561634151886381125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16396966374422767924254083 24595449561634151886381125)
            ·
              refine ⟨4611646792806403478696461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24595449561634151886381125 4611646792806403478696461)
              ·
                refine ⟨1729367547302401304511173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4611646792806403478696461 1729367547302401304511173)
                ·
                  refine ⟨324256415119200244595845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729367547302401304511173 324256415119200244595845)
                  ·
                    rfl

theorem cell22_2841692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_2841692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841692 prefixEnd_2841692 := by exact prefixLift 2841692
  have htrace : WordTrace (prefixWord ++ tailWord_2841692) baseStart_2841692 baseEnd_2841692 := by
    simpa [prefixWord, tailWord_2841692, baseEnd_2841692] using wordTrace_append hprefix tailTrace_2841692
  have hstable : (prefixWord ++ tailWord_2841692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841692).length < 2 ^ (prefixWord ++ tailWord_2841692).sum := by decide
  have hdescent : baseEnd_2841692 < baseStart_2841692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841703 : List Nat := [1, 1, 5, 1, 1, 4, 9]
def baseStart_2841703 : Nat := 118140960795 + 2841703 * 2 ^ 59
def prefixEnd_2841703 : Nat := 4983230072969 + 3 ^ 40 * 2841703 * 2
def baseEnd_2841703 : Nat := 36028630032681495250463

theorem tailTrace_2841703 : CollatzResearch.WordTrace tailWord_2841703 prefixEnd_2841703 36028630032681495250463 := by
  unfold tailWord_2841703
  simp only [CollatzResearch.WordTrace]
  refine ⟨103645423224002830078873763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69096948816001886719249175 103645423224002830078873763)
  ·
    refine ⟨155468134836004245118310645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103645423224002830078873763 155468134836004245118310645)
    ·
      refine ⟨14575137640875397979841623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155468134836004245118310645 14575137640875397979841623)
      ·
        refine ⟨21862706461313096969762435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14575137640875397979841623 21862706461313096969762435)
        ·
          refine ⟨32794059691969645454643653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21862706461313096969762435 32794059691969645454643653)
          ·
            refine ⟨6148886192244308522745685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32794059691969645454643653 6148886192244308522745685)
            ·
              refine ⟨36028630032681495250463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6148886192244308522745685 36028630032681495250463)
              ·
                rfl

theorem cell22_2841703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 9].length) (baseStart_2841703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841703 prefixEnd_2841703 := by exact prefixLift 2841703
  have htrace : WordTrace (prefixWord ++ tailWord_2841703) baseStart_2841703 baseEnd_2841703 := by
    simpa [prefixWord, tailWord_2841703, baseEnd_2841703] using wordTrace_append hprefix tailTrace_2841703
  have hstable : (prefixWord ++ tailWord_2841703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841703).length < 2 ^ (prefixWord ++ tailWord_2841703).sum := by decide
  have hdescent : baseEnd_2841703 < baseStart_2841703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841763 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 4, 5]
def baseStart_2841763 : Nat := 118140960795 + 2841763 * 2 ^ 59
def prefixEnd_2841763 : Nat := 4983230072969 + 3 ^ 40 * 2841763 * 2
def baseEnd_2841763 : Nat := 972793550108580215262317

theorem tailTrace_2841763 : CollatzResearch.WordTrace tailWord_2841763 prefixEnd_2841763 972793550108580215262317 := by
  unfold tailWord_2841763
  simp only [CollatzResearch.WordTrace]
  refine ⟨103647611603785460326057943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69098407735856973550705295 103647611603785460326057943)
  ·
    refine ⟨155471417405678190489086915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103647611603785460326057943 155471417405678190489086915)
    ·
      refine ⟨233207126108517285733630373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155471417405678190489086915 233207126108517285733630373)
      ·
        refine ⟨43726336145346991075055695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233207126108517285733630373 43726336145346991075055695)
        ·
          refine ⟨65589504218020486612583543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43726336145346991075055695 65589504218020486612583543)
          ·
            refine ⟨98384256327030729918875315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65589504218020486612583543 98384256327030729918875315)
            ·
              refine ⟨147576384490546094878312973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98384256327030729918875315 147576384490546094878312973)
              ·
                refine ⟨55341144183954785579367365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147576384490546094878312973 55341144183954785579367365)
                ·
                  refine ⟨10376464534491522296131381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55341144183954785579367365 10376464534491522296131381)
                  ·
                    refine ⟨972793550108580215262317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10376464534491522296131381 972793550108580215262317)
                    ·
                      rfl

theorem cell22_2841763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_2841763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841763 prefixEnd_2841763 := by exact prefixLift 2841763
  have htrace : WordTrace (prefixWord ++ tailWord_2841763) baseStart_2841763 baseEnd_2841763 := by
    simpa [prefixWord, tailWord_2841763, baseEnd_2841763] using wordTrace_append hprefix tailTrace_2841763
  have hstable : (prefixWord ++ tailWord_2841763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841763).length < 2 ^ (prefixWord ++ tailWord_2841763).sum := by decide
  have hdescent : baseEnd_2841763 < baseStart_2841763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841795 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 1, 4]
def baseStart_2841795 : Nat := 118140960795 + 2841795 * 2 ^ 59
def prefixEnd_2841795 : Nat := 4983230072969 + 3 ^ 40 * 2841795 * 2
def baseEnd_2841795 : Nat := 972804504362542798462219

theorem tailTrace_2841795 : CollatzResearch.WordTrace tailWord_2841795 prefixEnd_2841795 972804504362542798462219 := by
  unfold tailWord_2841795
  simp only [CollatzResearch.WordTrace]
  refine ⟨103648778739669529791222839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69099185826446353194148559 103648778739669529791222839)
  ·
    refine ⟨155473168109504294686834259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103648778739669529791222839 155473168109504294686834259)
    ·
      refine ⟨233209752164256442030251389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155473168109504294686834259 233209752164256442030251389)
      ·
        refine ⟨87453657061596165761344271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233209752164256442030251389 87453657061596165761344271)
        ·
          refine ⟨131180485592394248642016407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87453657061596165761344271 131180485592394248642016407)
          ·
            refine ⟨196770728388591372963024611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131180485592394248642016407 196770728388591372963024611)
            ·
              refine ⟨295156092582887059444536917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196770728388591372963024611 295156092582887059444536917)
              ·
                refine ⟨3458860459955707727865667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 295156092582887059444536917 3458860459955707727865667)
                ·
                  refine ⟨5188290689933561591798501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458860459955707727865667 5188290689933561591798501)
                  ·
                    refine ⟨972804504362542798462219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5188290689933561591798501 972804504362542798462219)
                    ·
                      rfl

theorem cell22_2841795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 4].length) (baseStart_2841795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841795 prefixEnd_2841795 := by exact prefixLift 2841795
  have htrace : WordTrace (prefixWord ++ tailWord_2841795) baseStart_2841795 baseEnd_2841795 := by
    simpa [prefixWord, tailWord_2841795, baseEnd_2841795] using wordTrace_append hprefix tailTrace_2841795
  have hstable : (prefixWord ++ tailWord_2841795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841795).length < 2 ^ (prefixWord ++ tailWord_2841795).sum := by decide
  have hdescent : baseEnd_2841795 < baseStart_2841795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841857 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_2841857 : Nat := 118140960795 + 2841857 * 2 ^ 59
def prefixEnd_2841857 : Nat := 4983230072969 + 3 ^ 40 * 2841857 * 2
def baseEnd_2841857 : Nat := 972825728229595303412029

theorem tailTrace_2841857 : CollatzResearch.WordTrace tailWord_2841857 prefixEnd_2841857 972825728229595303412029 := by
  unfold tailWord_2841857
  simp only [CollatzResearch.WordTrace]
  refine ⟨103651040065444914379979825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69100693376963276253319883 103651040065444914379979825)
  ·
    refine ⟨77738280049083685784984869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103651040065444914379979825 77738280049083685784984869)
    ·
      refine ⟨14575927509203191084684663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77738280049083685784984869 14575927509203191084684663)
      ·
        refine ⟨21863891263804786627026995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14575927509203191084684663 21863891263804786627026995)
        ·
          refine ⟨32795836895707179940540493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21863891263804786627026995 32795836895707179940540493)
          ·
            refine ⟨12298438835890192477702685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32795836895707179940540493 12298438835890192477702685)
            ·
              refine ⟨4611914563458822179138507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12298438835890192477702685 4611914563458822179138507)
              ·
                refine ⟨6917871845188233268707761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4611914563458822179138507 6917871845188233268707761)
                ·
                  refine ⟨5188403883891174951530821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6917871845188233268707761 5188403883891174951530821)
                  ·
                    refine ⟨972825728229595303412029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5188403883891174951530821 972825728229595303412029)
                    ·
                      rfl

theorem cell22_2841857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_2841857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841857 prefixEnd_2841857 := by exact prefixLift 2841857
  have htrace : WordTrace (prefixWord ++ tailWord_2841857) baseStart_2841857 baseEnd_2841857 := by
    simpa [prefixWord, tailWord_2841857, baseEnd_2841857] using wordTrace_append hprefix tailTrace_2841857
  have hstable : (prefixWord ++ tailWord_2841857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841857).length < 2 ^ (prefixWord ++ tailWord_2841857).sum := by decide
  have hdescent : baseEnd_2841857 < baseStart_2841857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841964 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_2841964 : Nat := 118140960795 + 2841964 * 2 ^ 59
def prefixEnd_2841964 : Nat := 4983230072969 + 3 ^ 40 * 2841964 * 2
def baseEnd_2841964 : Nat := 972862356516282690986701

theorem tailTrace_2841964 : CollatzResearch.WordTrace tailWord_2841964 prefixEnd_2841964 972862356516282690986701 := by
  unfold tailWord_2841964
  simp only [CollatzResearch.WordTrace]
  refine ⟨51827471338028635827062473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69103295117371514436083297 51827471338028635827062473)
  ·
    refine ⟨38870603503521476870296855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51827471338028635827062473 38870603503521476870296855)
    ·
      refine ⟨58305905255282215305445283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38870603503521476870296855 58305905255282215305445283)
      ·
        refine ⟨87458857882923322958167925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58305905255282215305445283 87458857882923322958167925)
        ·
          refine ⟨8199267926524061527328243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87458857882923322958167925 8199267926524061527328243)
          ·
            refine ⟨12298901889786092290992365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8199267926524061527328243 12298901889786092290992365)
            ·
              refine ⟨4612088208669784609122137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12298901889786092290992365 4612088208669784609122137)
              ·
                refine ⟨3459066156502338456841603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4612088208669784609122137 3459066156502338456841603)
                ·
                  refine ⟨5188599234753507685262405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459066156502338456841603 5188599234753507685262405)
                  ·
                    refine ⟨972862356516282690986701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5188599234753507685262405 972862356516282690986701)
                    ·
                      rfl

theorem cell22_2841964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_2841964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841964 prefixEnd_2841964 := by exact prefixLift 2841964
  have htrace : WordTrace (prefixWord ++ tailWord_2841964) baseStart_2841964 baseEnd_2841964 := by
    simpa [prefixWord, tailWord_2841964, baseEnd_2841964] using wordTrace_append hprefix tailTrace_2841964
  have hstable : (prefixWord ++ tailWord_2841964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841964).length < 2 ^ (prefixWord ++ tailWord_2841964).sum := by decide
  have hdescent : baseEnd_2841964 < baseStart_2841964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841977 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 6, 3]
def baseStart_2841977 : Nat := 118140960795 + 2841977 * 2 ^ 59
def prefixEnd_2841977 : Nat := 4983230072969 + 3 ^ 40 * 2841977 * 2
def baseEnd_2841977 : Nat := 972866806681954990411661

theorem tailTrace_2841977 : CollatzResearch.WordTrace tailWord_2841977 prefixEnd_2841977 972866806681954990411661 := by
  unfold tailWord_2841977
  simp only [CollatzResearch.WordTrace]
  refine ⟨103655416825010174874348185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69103611216673449916232123 103655416825010174874348185)
  ·
    refine ⟨77741562618757631155761139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103655416825010174874348185 77741562618757631155761139)
    ·
      refine ⟨116612343928136446733641709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77741562618757631155761139 116612343928136446733641709)
      ·
        refine ⟨43729628973051167525115641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116612343928136446733641709 43729628973051167525115641)
        ·
          refine ⟨32797221729788375643836731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43729628973051167525115641 32797221729788375643836731)
          ·
            refine ⟨49195832594682563465755097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32797221729788375643836731 49195832594682563465755097)
            ·
              refine ⟨36896874446011922599316323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49195832594682563465755097 36896874446011922599316323)
              ·
                refine ⟨55345311669017883898974485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36896874446011922599316323 55345311669017883898974485)
                ·
                  refine ⟨2594311484485213307764429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55345311669017883898974485 2594311484485213307764429)
                  ·
                    refine ⟨972866806681954990411661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2594311484485213307764429 972866806681954990411661)
                    ·
                      rfl

theorem cell22_2841977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_2841977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2841977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2841977 prefixEnd_2841977 := by exact prefixLift 2841977
  have htrace : WordTrace (prefixWord ++ tailWord_2841977) baseStart_2841977 baseEnd_2841977 := by
    simpa [prefixWord, tailWord_2841977, baseEnd_2841977] using wordTrace_append hprefix tailTrace_2841977
  have hstable : (prefixWord ++ tailWord_2841977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841977).length < 2 ^ (prefixWord ++ tailWord_2841977).sum := by decide
  have hdescent : baseEnd_2841977 < baseStart_2841977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842056 : List Nat := [2, 1, 3, 1, 3, 1, 1, 6, 1, 3]
def baseStart_2842056 : Nat := 118140960795 + 2842056 * 2 ^ 59
def prefixEnd_2842056 : Nat := 4983230072969 + 3 ^ 40 * 2842056 * 2
def baseEnd_2842056 : Nat := 972893849996425117686419

theorem tailTrace_2842056 : CollatzResearch.WordTrace tailWord_2842056 prefixEnd_2842056 972893849996425117686419 := by
  unfold tailWord_2842056
  simp only [CollatzResearch.WordTrace]
  refine ⟨51829149095861985683237011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69105532127815980910982681 51829149095861985683237011)
  ·
    refine ⟨77743723643792978524855517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51829149095861985683237011 77743723643792978524855517)
    ·
      refine ⟨29153896366422366946820819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77743723643792978524855517 29153896366422366946820819)
      ·
        refine ⟨43730844549633550420231229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29153896366422366946820819 43730844549633550420231229)
        ·
          refine ⟨16399066706112581407586711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43730844549633550420231229 16399066706112581407586711)
          ·
            refine ⟨24598600059168872111380067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16399066706112581407586711 24598600059168872111380067)
            ·
              refine ⟨36897900088753308167070101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24598600059168872111380067 36897900088753308167070101)
              ·
                refine ⟨1729589066660311320331411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36897900088753308167070101 1729589066660311320331411)
                ·
                  refine ⟨2594383599990466980497117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729589066660311320331411 2594383599990466980497117)
                  ·
                    refine ⟨972893849996425117686419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2594383599990466980497117 972893849996425117686419)
                    ·
                      rfl

theorem cell22_2842056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_2842056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842056 prefixEnd_2842056 := by exact prefixLift 2842056
  have htrace : WordTrace (prefixWord ++ tailWord_2842056) baseStart_2842056 baseEnd_2842056 := by
    simpa [prefixWord, tailWord_2842056, baseEnd_2842056] using wordTrace_append hprefix tailTrace_2842056
  have hstable : (prefixWord ++ tailWord_2842056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842056).length < 2 ^ (prefixWord ++ tailWord_2842056).sum := by decide
  have hdescent : baseEnd_2842056 < baseStart_2842056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842090 : List Nat := [3, 1, 3, 1, 4, 2, 1, 3, 1, 3]
def baseStart_2842090 : Nat := 118140960795 + 2842090 * 2 ^ 59
def prefixEnd_2842090 : Nat := 4983230072969 + 3 ^ 40 * 2842090 * 2
def baseEnd_2842090 : Nat := 972905488891260362336315

theorem tailTrace_2842090 : CollatzResearch.WordTrace tailWord_2842090 prefixEnd_2842090 972905488891260362336315 := by
  unfold tailWord_2842090
  simp only [CollatzResearch.WordTrace]
  refine ⟨25914884568400198793302931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69106358849067196782141149 25914884568400198793302931)
  ·
    refine ⟨38872326852600298189954397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25914884568400198793302931 38872326852600298189954397)
    ·
      refine ⟨14577122569725111821232899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38872326852600298189954397 14577122569725111821232899)
      ·
        refine ⟨21865683854587667731849349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14577122569725111821232899 21865683854587667731849349)
        ·
          refine ⟨4099815722735187699721753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21865683854587667731849349 4099815722735187699721753)
          ·
            refine ⟨3074861792051390774791315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4099815722735187699721753 3074861792051390774791315)
            ·
              refine ⟨4612292688077086162186973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3074861792051390774791315 4612292688077086162186973)
              ·
                refine ⟨1729609758028907310820115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4612292688077086162186973 1729609758028907310820115)
                ·
                  refine ⟨2594414637043360966230173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729609758028907310820115 2594414637043360966230173)
                  ·
                    refine ⟨972905488891260362336315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2594414637043360966230173 972905488891260362336315)
                    ·
                      rfl

theorem cell22_2842090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_2842090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842090 prefixEnd_2842090 := by exact prefixLift 2842090
  have htrace : WordTrace (prefixWord ++ tailWord_2842090) baseStart_2842090 baseEnd_2842090 := by
    simpa [prefixWord, tailWord_2842090, baseEnd_2842090] using wordTrace_append hprefix tailTrace_2842090
  have hstable : (prefixWord ++ tailWord_2842090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842090).length < 2 ^ (prefixWord ++ tailWord_2842090).sum := by decide
  have hdescent : baseEnd_2842090 < baseStart_2842090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842187 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 9]
def baseStart_2842187 : Nat := 118140960795 + 2842187 * 2 ^ 59
def prefixEnd_2842187 : Nat := 4983230072969 + 3 ^ 40 * 2842187 * 2
def baseEnd_2842187 : Nat := 324312897991194814220339

theorem tailTrace_2842187 : CollatzResearch.WordTrace tailWord_2842187 prefixEnd_2842187 324312897991194814220339 := by
  unfold tailWord_2842187
  simp only [CollatzResearch.WordTrace]
  refine ⟨103663076154249380739492815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69108717436166253826328543 103663076154249380739492815)
  ·
    refine ⟨155494614231374071109239223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103663076154249380739492815 155494614231374071109239223)
    ·
      refine ⟨233241921347061106663858835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155494614231374071109239223 233241921347061106663858835)
      ·
        refine ⟨349862882020591659995788253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233241921347061106663858835 349862882020591659995788253)
        ·
          refine ⟨131198580757721872498420595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349862882020591659995788253 131198580757721872498420595)
          ·
            refine ⟨196797871136582808747630893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131198580757721872498420595 196797871136582808747630893)
            ·
              refine ⟨73799201676218553280361585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196797871136582808747630893 73799201676218553280361585)
              ·
                refine ⟨55349401257163914960271189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73799201676218553280361585 55349401257163914960271189)
                ·
                  refine ⟨324312897991194814220339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55349401257163914960271189 324312897991194814220339)
                  ·
                    rfl

theorem cell22_2842187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 9].length) (baseStart_2842187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842187 prefixEnd_2842187 := by exact prefixLift 2842187
  have htrace : WordTrace (prefixWord ++ tailWord_2842187) baseStart_2842187 baseEnd_2842187 := by
    simpa [prefixWord, tailWord_2842187, baseEnd_2842187] using wordTrace_append hprefix tailTrace_2842187
  have hstable : (prefixWord ++ tailWord_2842187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842187).length < 2 ^ (prefixWord ++ tailWord_2842187).sum := by decide
  have hdescent : baseEnd_2842187 < baseStart_2842187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842221 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2842221 : Nat := 118140960795 + 2842221 * 2 ^ 59
def prefixEnd_2842221 : Nat := 4983230072969 + 3 ^ 40 * 2842221 * 2
def baseEnd_2842221 : Nat := 324316777622806562436971

theorem tailTrace_2842221 : CollatzResearch.WordTrace tailWord_2842221 prefixEnd_2842221 324316777622806562436971 := by
  unfold tailWord_2842221
  simp only [CollatzResearch.WordTrace]
  refine ⟨103664316236126204546230517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69109544157417469697487011 103664316236126204546230517)
  ·
    refine ⟨9718529647136831676209111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103664316236126204546230517 9718529647136831676209111)
    ·
      refine ⟨14577794470705247514313667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9718529647136831676209111 14577794470705247514313667)
      ·
        refine ⟨21866691706057871271470501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14577794470705247514313667 21866691706057871271470501)
        ·
          refine ⟨4100004694885850863400719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21866691706057871271470501 4100004694885850863400719)
          ·
            refine ⟨6150007042328776295101079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100004694885850863400719 6150007042328776295101079)
            ·
              refine ⟨9225010563493164442651619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150007042328776295101079 9225010563493164442651619)
              ·
                refine ⟨13837515845239746663977429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9225010563493164442651619 13837515845239746663977429)
                ·
                  refine ⟨324316777622806562436971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13837515845239746663977429 324316777622806562436971)
                  ·
                    rfl

theorem cell22_2842221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2842221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842221 prefixEnd_2842221 := by exact prefixLift 2842221
  have htrace : WordTrace (prefixWord ++ tailWord_2842221) baseStart_2842221 baseEnd_2842221 := by
    simpa [prefixWord, tailWord_2842221, baseEnd_2842221] using wordTrace_append hprefix tailTrace_2842221
  have hstable : (prefixWord ++ tailWord_2842221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842221).length < 2 ^ (prefixWord ++ tailWord_2842221).sum := by decide
  have hdescent : baseEnd_2842221 < baseStart_2842221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842234 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_2842234 : Nat := 118140960795 + 2842234 * 2 ^ 59
def prefixEnd_2842234 : Nat := 4983230072969 + 3 ^ 40 * 2842234 * 2
def baseEnd_2842234 : Nat := 972954783034091986735873

theorem tailTrace_2842234 : CollatzResearch.WordTrace tailWord_2842234 prefixEnd_2842234 972954783034091986735873 := by
  unfold tailWord_2842234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25916197596269776941613439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69109860256719405177635837 25916197596269776941613439)
  ·
    refine ⟨38874296394404665412420159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25916197596269776941613439 38874296394404665412420159)
    ·
      refine ⟨58311444591606998118630239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38874296394404665412420159 58311444591606998118630239)
      ·
        refine ⟨87467166887410497177945359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58311444591606998118630239 87467166887410497177945359)
        ·
          refine ⟨131200750331115745766918039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87467166887410497177945359 131200750331115745766918039)
          ·
            refine ⟨196801125496673618650377059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131200750331115745766918039 196801125496673618650377059)
            ·
              refine ⟨295201688245010427975565589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196801125496673618650377059 295201688245010427975565589)
              ·
                refine ⟨13837579136484863811354637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 295201688245010427975565589 13837579136484863811354637)
                ·
                  refine ⟨5189092176181823929257989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13837579136484863811354637 5189092176181823929257989)
                  ·
                    refine ⟨972954783034091986735873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5189092176181823929257989 972954783034091986735873)
                    ·
                      rfl

theorem cell22_2842234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_2842234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842234 prefixEnd_2842234 := by exact prefixLift 2842234
  have htrace : WordTrace (prefixWord ++ tailWord_2842234) baseStart_2842234 baseEnd_2842234 := by
    simpa [prefixWord, tailWord_2842234, baseEnd_2842234] using wordTrace_append hprefix tailTrace_2842234
  have hstable : (prefixWord ++ tailWord_2842234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842234).length < 2 ^ (prefixWord ++ tailWord_2842234).sum := by decide
  have hdescent : baseEnd_2842234 < baseStart_2842234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842249 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 6]
def baseStart_2842249 : Nat := 118140960795 + 2842249 * 2 ^ 59
def prefixEnd_2842249 : Nat := 4983230072969 + 3 ^ 40 * 2842249 * 2
def baseEnd_2842249 : Nat := 324319972613545649203609

theorem tailTrace_2842249 : CollatzResearch.WordTrace tailWord_2842249 prefixEnd_2842249 324319972613545649203609 := by
  unfold tailWord_2842249
  simp only [CollatzResearch.WordTrace]
  refine ⟨103665337480024765328249801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69110224986683176885499867 103665337480024765328249801)
  ·
    refine ⟨77749003110018573996187351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103665337480024765328249801 77749003110018573996187351)
    ·
      refine ⟨116623504665027860994281027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77749003110018573996187351 116623504665027860994281027)
      ·
        refine ⟨174935256997541791491421541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116623504665027860994281027 174935256997541791491421541)
        ·
          refine ⟨32800360687039085904641539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174935256997541791491421541 32800360687039085904641539)
          ·
            refine ⟨49200541030558628856962309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32800360687039085904641539 49200541030558628856962309)
            ·
              refine ⟨9225101443229742910680433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49200541030558628856962309 9225101443229742910680433)
              ·
                refine ⟨6918826082422307183010325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9225101443229742910680433 6918826082422307183010325)
                ·
                  refine ⟨324319972613545649203609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6918826082422307183010325 324319972613545649203609)
                  ·
                    rfl

theorem cell22_2842249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_2842249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842249 prefixEnd_2842249 := by exact prefixLift 2842249
  have htrace : WordTrace (prefixWord ++ tailWord_2842249) baseStart_2842249 baseEnd_2842249 := by
    simpa [prefixWord, tailWord_2842249, baseEnd_2842249] using wordTrace_append hprefix tailTrace_2842249
  have hstable : (prefixWord ++ tailWord_2842249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842249).length < 2 ^ (prefixWord ++ tailWord_2842249).sum := by decide
  have hdescent : baseEnd_2842249 < baseStart_2842249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842251 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 1, 4]
def baseStart_2842251 : Nat := 118140960795 + 2842251 * 2 ^ 59
def prefixEnd_2842251 : Nat := 4983230072969 + 3 ^ 40 * 2842251 * 2
def baseEnd_2842251 : Nat := 972960602481509609060821

theorem tailTrace_2842251 : CollatzResearch.WordTrace tailWord_2842251 prefixEnd_2842251 972960602481509609060821 := by
  unfold tailWord_2842251
  simp only [CollatzResearch.WordTrace]
  refine ⟨103665410426017519669822607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69110273617345013113215071 103665410426017519669822607)
  ·
    refine ⟨155498115639026279504733911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103665410426017519669822607 155498115639026279504733911)
    ·
      refine ⟨233247173458539419257100867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155498115639026279504733911 233247173458539419257100867)
      ·
        refine ⟨349870760187809128885651301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233247173458539419257100867 349870760187809128885651301)
        ·
          refine ⟨65600767535214211666059619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349870760187809128885651301 65600767535214211666059619)
          ·
            refine ⟨98401151302821317499089429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65600767535214211666059619 98401151302821317499089429)
            ·
              refine ⟨4612553967319749257769817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98401151302821317499089429 4612553967319749257769817)
              ·
                refine ⟨3459415475489811943327363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4612553967319749257769817 3459415475489811943327363)
                ·
                  refine ⟨5189123213234717914991045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459415475489811943327363 5189123213234717914991045)
                  ·
                    refine ⟨972960602481509609060821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5189123213234717914991045 972960602481509609060821)
                    ·
                      rfl

theorem cell22_2842251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 4].length) (baseStart_2842251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842251 prefixEnd_2842251 := by exact prefixLift 2842251
  have htrace : WordTrace (prefixWord ++ tailWord_2842251) baseStart_2842251 baseEnd_2842251 := by
    simpa [prefixWord, tailWord_2842251, baseEnd_2842251] using wordTrace_append hprefix tailTrace_2842251
  have hstable : (prefixWord ++ tailWord_2842251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842251).length < 2 ^ (prefixWord ++ tailWord_2842251).sum := by decide
  have hdescent : baseEnd_2842251 < baseStart_2842251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842298 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_2842298 : Nat := 118140960795 + 2842298 * 2 ^ 59
def prefixEnd_2842298 : Nat := 4983230072969 + 3 ^ 40 * 2842298 * 2
def baseEnd_2842298 : Nat := 972976691542017153135677

theorem tailTrace_2842298 : CollatzResearch.WordTrace tailWord_2842298 prefixEnd_2842298 972976691542017153135677 := by
  unfold tailWord_2842298
  simp only [CollatzResearch.WordTrace]
  refine ⟨25916781164211811674195887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69111416437898164464522365 25916781164211811674195887)
  ·
    refine ⟨38875171746317717511293831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25916781164211811674195887 38875171746317717511293831)
    ·
      refine ⟨58312757619476576266940747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38875171746317717511293831 58312757619476576266940747)
      ·
        refine ⟨87469136429214864400411121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58312757619476576266940747 87469136429214864400411121)
        ·
          refine ⟨65601852321911148300308341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87469136429214864400411121 65601852321911148300308341)
          ·
            refine ⟨6150173655179170153153907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65601852321911148300308341 6150173655179170153153907)
            ·
              refine ⟨9225260482768755229730861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150173655179170153153907 9225260482768755229730861)
              ·
                refine ⟨3459472681038283211149073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9225260482768755229730861 3459472681038283211149073)
                ·
                  refine ⟨2594604510778712408361805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3459472681038283211149073 2594604510778712408361805)
                  ·
                    refine ⟨972976691542017153135677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2594604510778712408361805 972976691542017153135677)
                    ·
                      rfl

theorem cell22_2842298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_2842298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842298 prefixEnd_2842298 := by exact prefixLift 2842298
  have htrace : WordTrace (prefixWord ++ tailWord_2842298) baseStart_2842298 baseEnd_2842298 := by
    simpa [prefixWord, tailWord_2842298, baseEnd_2842298] using wordTrace_append hprefix tailTrace_2842298
  have hstable : (prefixWord ++ tailWord_2842298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842298).length < 2 ^ (prefixWord ++ tailWord_2842298).sum := by decide
  have hdescent : baseEnd_2842298 < baseStart_2842298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842332 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2842332 : Nat := 118140960795 + 2842332 * 2 ^ 59
def prefixEnd_2842332 : Nat := 4983230072969 + 3 ^ 40 * 2842332 * 2
def baseEnd_2842332 : Nat := 972988330436852397785573

theorem tailTrace_2842332 : CollatzResearch.WordTrace tailWord_2842332 prefixEnd_2842332 972988330436852397785573 := by
  unfold tailWord_2842332
  simp only [CollatzResearch.WordTrace]
  refine ⟨51834182369362035251760625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69112243159149380335680833 51834182369362035251760625)
  ·
    refine ⟨38875636777021526438820469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51834182369362035251760625 38875636777021526438820469)
    ·
      refine ⟨3644590947845768103639419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38875636777021526438820469 3644590947845768103639419)
      ·
        refine ⟨5466886421768652155459129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3644590947845768103639419 5466886421768652155459129)
        ·
          refine ⟨4100164816326489116594347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5466886421768652155459129 4100164816326489116594347)
          ·
            refine ⟨6150247224489733674891521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100164816326489116594347 6150247224489733674891521)
            ·
              refine ⟨4612685418367300256168641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6150247224489733674891521 4612685418367300256168641)
              ·
                refine ⟨3459514063775475192126481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4612685418367300256168641 3459514063775475192126481)
                ·
                  refine ⟨2594635547831606394094861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3459514063775475192126481 2594635547831606394094861)
                  ·
                    refine ⟨972988330436852397785573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2594635547831606394094861 972988330436852397785573)
                    ·
                      rfl

theorem cell22_2842332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2842332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842332 prefixEnd_2842332 := by exact prefixLift 2842332
  have htrace : WordTrace (prefixWord ++ tailWord_2842332) baseStart_2842332 baseEnd_2842332 := by
    simpa [prefixWord, tailWord_2842332, baseEnd_2842332] using wordTrace_append hprefix tailTrace_2842332
  have hstable : (prefixWord ++ tailWord_2842332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842332).length < 2 ^ (prefixWord ++ tailWord_2842332).sum := by decide
  have hdescent : baseEnd_2842332 < baseStart_2842332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842401 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 6]
def baseStart_2842401 : Nat := 118140960795 + 2842401 * 2 ^ 59
def prefixEnd_2842401 : Nat := 4983230072969 + 3 ^ 40 * 2842401 * 2
def baseEnd_2842401 : Nat := 324337316848986405936787

theorem tailTrace_2842401 : CollatzResearch.WordTrace tailWord_2842401 prefixEnd_2842401 324337316848986405936787 := by
  unfold tailWord_2842401
  simp only [CollatzResearch.WordTrace]
  refine ⟨103670881375474095287783057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69113920916982730191855371 103670881375474095287783057)
  ·
    refine ⟨77753161031605571465837293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103670881375474095287783057 77753161031605571465837293)
    ·
      refine ⟨29157435386852089299688985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77753161031605571465837293 29157435386852089299688985)
      ·
        refine ⟨21868076540139066974766739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29157435386852089299688985 21868076540139066974766739)
        ·
          refine ⟨32802114810208600462150109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21868076540139066974766739 32802114810208600462150109)
          ·
            refine ⟨12300793053828225173306291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32802114810208600462150109 12300793053828225173306291)
            ·
              refine ⟨18451189580742337759959437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12300793053828225173306291 18451189580742337759959437)
              ·
                refine ⟨6919196092778376659984789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18451189580742337759959437 6919196092778376659984789)
                ·
                  refine ⟨324337316848986405936787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6919196092778376659984789 324337316848986405936787)
                  ·
                    rfl

theorem cell22_2842401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_2842401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842401 prefixEnd_2842401 := by exact prefixLift 2842401
  have htrace : WordTrace (prefixWord ++ tailWord_2842401) baseStart_2842401 baseEnd_2842401 := by
    simpa [prefixWord, tailWord_2842401, baseEnd_2842401] using wordTrace_append hprefix tailTrace_2842401
  have hstable : (prefixWord ++ tailWord_2842401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842401).length < 2 ^ (prefixWord ++ tailWord_2842401).sum := by decide
  have hdescent : baseEnd_2842401 < baseStart_2842401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842420 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2842420 : Nat := 118140960795 + 2842420 * 2 ^ 59
def prefixEnd_2842420 : Nat := 4983230072969 + 3 ^ 40 * 2842420 * 2
def baseEnd_2842420 : Nat := 973018454635249501585303

theorem tailTrace_2842420 : CollatzResearch.WordTrace tailWord_2842420 prefixEnd_2842420 973018454635249501585303 := by
  unfold tailWord_2842420
  simp only [CollatzResearch.WordTrace]
  refine ⟨51835787181202630766362357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69114382908270174355149809 51835787181202630766362357)
  ·
    refine ⟨4859605048237746634346471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51835787181202630766362357 4859605048237746634346471)
    ·
      refine ⟨7289407572356619951519707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4859605048237746634346471 7289407572356619951519707)
      ·
        refine ⟨10934111358534929927279561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7289407572356619951519707 10934111358534929927279561)
        ·
          refine ⟨8200583518901197445459671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10934111358534929927279561 8200583518901197445459671)
          ·
            refine ⟨12300875278351796168189507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8200583518901197445459671 12300875278351796168189507)
            ·
              refine ⟨18451312917527694252284261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12300875278351796168189507 18451312917527694252284261)
              ·
                refine ⟨3459621172036442672303299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18451312917527694252284261 3459621172036442672303299)
                ·
                  refine ⟨5189431758054664008454949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459621172036442672303299 5189431758054664008454949)
                  ·
                    refine ⟨973018454635249501585303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5189431758054664008454949 973018454635249501585303)
                    ·
                      rfl

theorem cell22_2842420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2842420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842420 prefixEnd_2842420 := by exact prefixLift 2842420
  have htrace : WordTrace (prefixWord ++ tailWord_2842420) baseStart_2842420 baseEnd_2842420 := by
    simpa [prefixWord, tailWord_2842420, baseEnd_2842420] using wordTrace_append hprefix tailTrace_2842420
  have hstable : (prefixWord ++ tailWord_2842420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842420).length < 2 ^ (prefixWord ++ tailWord_2842420).sum := by decide
  have hdescent : baseEnd_2842420 < baseStart_2842420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842435 : List Nat := [1, 1, 1, 3, 1, 7, 1, 3, 4]
def baseStart_2842435 : Nat := 118140960795 + 2842435 * 2 ^ 59
def prefixEnd_2842435 : Nat := 4983230072969 + 3 ^ 40 * 2842435 * 2
def baseEnd_2842435 : Nat := 324341196480598154153419

theorem tailTrace_2842435 : CollatzResearch.WordTrace tailWord_2842435 prefixEnd_2842435 324341196480598154153419 := by
  unfold tailWord_2842435
  simp only [CollatzResearch.WordTrace]
  refine ⟨103672121457350919094520759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69114747638233946063013839 103672121457350919094520759)
  ·
    refine ⟨155508182186026378641781139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103672121457350919094520759 155508182186026378641781139)
    ·
      refine ⟨233262273279039567962671709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155508182186026378641781139 233262273279039567962671709)
      ·
        refine ⟨87473352479639837986001891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233262273279039567962671709 87473352479639837986001891)
        ·
          refine ⟨131210028719459756979002837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87473352479639837986001891 131210028719459756979002837)
          ·
            refine ⟨3075235048112338054195379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 131210028719459756979002837 3075235048112338054195379)
            ·
              refine ⟨4612852572168507081293069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3075235048112338054195379 4612852572168507081293069)
              ·
                refine ⟨1729819714563190155484901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4612852572168507081293069 1729819714563190155484901)
                ·
                  refine ⟨324341196480598154153419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729819714563190155484901 324341196480598154153419)
                  ·
                    rfl

theorem cell22_2842435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 4].length) (baseStart_2842435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842435 prefixEnd_2842435 := by exact prefixLift 2842435
  have htrace : WordTrace (prefixWord ++ tailWord_2842435) baseStart_2842435 baseEnd_2842435 := by
    simpa [prefixWord, tailWord_2842435, baseEnd_2842435] using wordTrace_append hprefix tailTrace_2842435
  have hstable : (prefixWord ++ tailWord_2842435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842435).length < 2 ^ (prefixWord ++ tailWord_2842435).sum := by decide
  have hdescent : baseEnd_2842435 < baseStart_2842435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842452 : List Nat := [2, 4, 1, 1, 3, 2, 3, 2, 4]
def baseStart_2842452 : Nat := 118140960795 + 2842452 * 2 ^ 59
def prefixEnd_2842452 : Nat := 4983230072969 + 3 ^ 40 * 2842452 * 2
def baseEnd_2842452 : Nat := 324343136296404028261735

theorem tailTrace_2842452 : CollatzResearch.WordTrace tailWord_2842452 prefixEnd_2842452 324343136296404028261735 := by
  unfold tailWord_2842452
  simp only [CollatzResearch.WordTrace]
  refine ⟨51836370749144665498944805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69115160998859553998593073 51836370749144665498944805)
  ·
    refine ⟨9719319515464624781052151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51836370749144665498944805 9719319515464624781052151)
    ·
      refine ⟨14578979273196937171578227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9719319515464624781052151 14578979273196937171578227)
      ·
        refine ⟨21868468909795405757367341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14578979273196937171578227 21868468909795405757367341)
        ·
          refine ⟨8200675841173277159012753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21868468909795405757367341 8200675841173277159012753)
          ·
            refine ⟨6150506880879957869259565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8200675841173277159012753 6150506880879957869259565)
            ·
              refine ⟨2306440080329984200972337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6150506880879957869259565 2306440080329984200972337)
              ·
                refine ⟨1729830060247488150729253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306440080329984200972337 1729830060247488150729253)
                ·
                  refine ⟨324343136296404028261735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729830060247488150729253 324343136296404028261735)
                  ·
                    rfl

theorem cell22_2842452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_2842452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842452 prefixEnd_2842452 := by exact prefixLift 2842452
  have htrace : WordTrace (prefixWord ++ tailWord_2842452) baseStart_2842452 baseEnd_2842452 := by
    simpa [prefixWord, tailWord_2842452, baseEnd_2842452] using wordTrace_append hprefix tailTrace_2842452
  have hstable : (prefixWord ++ tailWord_2842452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842452).length < 2 ^ (prefixWord ++ tailWord_2842452).sum := by decide
  have hdescent : baseEnd_2842452 < baseStart_2842452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842495 : List Nat := [1, 1, 2, 2, 1, 1, 3, 7, 1, 3]
def baseStart_2842495 : Nat := 118140960795 + 2842495 * 2 ^ 59
def prefixEnd_2842495 : Nat := 4983230072969 + 3 ^ 40 * 2842495 * 2
def baseEnd_2842495 : Nat := 973044128667974305960073

theorem tailTrace_2842495 : CollatzResearch.WordTrace tailWord_2842495 prefixEnd_2842495 973044128667974305960073 := by
  unfold tailWord_2842495
  simp only [CollatzResearch.WordTrace]
  refine ⟨103674309837133549341704939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69116206558089032894469959 103674309837133549341704939)
  ·
    refine ⟨155511464755700324012557409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103674309837133549341704939 155511464755700324012557409)
    ·
      refine ⟨116633598566775243009418057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155511464755700324012557409 116633598566775243009418057)
      ·
        refine ⟨87475198925081432257063543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116633598566775243009418057 87475198925081432257063543)
        ·
          refine ⟨131212798387622148385595315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87475198925081432257063543 131212798387622148385595315)
          ·
            refine ⟨196819197581433222578392973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131212798387622148385595315 196819197581433222578392973)
            ·
              refine ⟨73807199093037458466897365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196819197581433222578392973 73807199093037458466897365)
              ·
                refine ⟨1729856228743065432817907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73807199093037458466897365 1729856228743065432817907)
                ·
                  refine ⟨2594784343114598149226861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729856228743065432817907 2594784343114598149226861)
                  ·
                    refine ⟨973044128667974305960073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2594784343114598149226861 973044128667974305960073)
                    ·
                      rfl

theorem cell22_2842495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 3].length) (baseStart_2842495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842495 prefixEnd_2842495 := by exact prefixLift 2842495
  have htrace : WordTrace (prefixWord ++ tailWord_2842495) baseStart_2842495 baseEnd_2842495 := by
    simpa [prefixWord, tailWord_2842495, baseEnd_2842495] using wordTrace_append hprefix tailTrace_2842495
  have hstable : (prefixWord ++ tailWord_2842495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842495).length < 2 ^ (prefixWord ++ tailWord_2842495).sum := by decide
  have hdescent : baseEnd_2842495 < baseStart_2842495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842570 : List Nat := [3, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_2842570 : Nat := 118140960795 + 2842570 * 2 ^ 59
def prefixEnd_2842570 : Nat := 4983230072969 + 3 ^ 40 * 2842570 * 2
def baseEnd_2842570 : Nat := 324356600900233036778281

theorem tailTrace_2842570 : CollatzResearch.WordTrace tailWord_2842570 prefixEnd_2842570 324356600900233036778281 := by
  unfold tailWord_2842570
  simp only [CollatzResearch.WordTrace]
  refine ⟨25919261327965459287671291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69118030207907891433790109 25919261327965459287671291)
  ·
    refine ⟨38878891991948188931506937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25919261327965459287671291 38878891991948188931506937)
    ·
      refine ⟨29159168993961141698630203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38878891991948188931506937 29159168993961141698630203)
      ·
        refine ⟨43738753490941712547945305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29159168993961141698630203 43738753490941712547945305)
        ·
          refine ⟨32804065118206284410958979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43738753490941712547945305 32804065118206284410958979)
          ·
            refine ⟨49206097677309426616438469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32804065118206284410958979 49206097677309426616438469)
            ·
              refine ⟨9226143314495517490582213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49206097677309426616438469 9226143314495517490582213)
              ·
                refine ⟨1729901871467909529484165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9226143314495517490582213 1729901871467909529484165)
                ·
                  refine ⟨324356600900233036778281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729901871467909529484165 324356600900233036778281)
                  ·
                    rfl

theorem cell22_2842570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_2842570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842570 prefixEnd_2842570 := by exact prefixLift 2842570
  have htrace : WordTrace (prefixWord ++ tailWord_2842570) baseStart_2842570 baseEnd_2842570 := by
    simpa [prefixWord, tailWord_2842570, baseEnd_2842570] using wordTrace_append hprefix tailTrace_2842570
  have hstable : (prefixWord ++ tailWord_2842570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842570).length < 2 ^ (prefixWord ++ tailWord_2842570).sum := by decide
  have hdescent : baseEnd_2842570 < baseStart_2842570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842703 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 5, 5]
def baseStart_2842703 : Nat := 118140960795 + 2842703 * 2 ^ 59
def prefixEnd_2842703 : Nat := 4983230072969 + 3 ^ 40 * 2842703 * 2
def baseEnd_2842703 : Nat := 973115331318731096759435

theorem tailTrace_2842703 : CollatzResearch.WordTrace tailWord_2842703 prefixEnd_2842703 973115331318731096759435 := by
  unfold tailWord_2842703
  simp only [CollatzResearch.WordTrace]
  refine ⟨103681896220380000865276763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69121264146920000576851175 103681896220380000865276763)
  ·
    refine ⟨155522844330570001297915145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103681896220380000865276763 155522844330570001297915145)
    ·
      refine ⟨116642133247927500973436359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155522844330570001297915145 116642133247927500973436359)
      ·
        refine ⟨174963199871891251460154539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116642133247927500973436359 174963199871891251460154539)
        ·
          refine ⟨262444799807836877190231809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174963199871891251460154539 262444799807836877190231809)
          ·
            refine ⟨196833599855877657892673857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262444799807836877190231809 196833599855877657892673857)
            ·
              refine ⟨147625199891908243419505393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196833599855877657892673857 147625199891908243419505393)
              ·
                refine ⟨110718899918931182564629045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147625199891908243419505393 110718899918931182564629045)
                ·
                  refine ⟨10379896867399798365433973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110718899918931182564629045 10379896867399798365433973)
                  ·
                    refine ⟨973115331318731096759435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10379896867399798365433973 973115331318731096759435)
                    ·
                      rfl

theorem cell22_2842703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_2842703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842703 prefixEnd_2842703 := by exact prefixLift 2842703
  have htrace : WordTrace (prefixWord ++ tailWord_2842703) baseStart_2842703 baseEnd_2842703 := by
    simpa [prefixWord, tailWord_2842703, baseEnd_2842703] using wordTrace_append hprefix tailTrace_2842703
  have hstable : (prefixWord ++ tailWord_2842703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842703).length < 2 ^ (prefixWord ++ tailWord_2842703).sum := by decide
  have hdescent : baseEnd_2842703 < baseStart_2842703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842720 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_2842720 : Nat := 118140960795 + 2842720 * 2 ^ 59
def prefixEnd_2842720 : Nat := 4983230072969 + 3 ^ 40 * 2842720 * 2
def baseEnd_2842720 : Nat := 973121150766148719084383

theorem tailTrace_2842720 : CollatzResearch.WordTrace tailWord_2842720 prefixEnd_2842720 973121150766148719084383 := by
  unfold tailWord_2842720
  simp only [CollatzResearch.WordTrace]
  refine ⟨51841258130659206384322807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69121677507545608512430409 51841258130659206384322807)
  ·
    refine ⟨77761887195988809576484211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51841258130659206384322807 77761887195988809576484211)
    ·
      refine ⟨116642830793983214364726317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77761887195988809576484211 116642830793983214364726317)
      ·
        refine ⟨43741061547743705386772369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116642830793983214364726317 43741061547743705386772369)
        ·
          refine ⟨32805796160807779040079277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43741061547743705386772369 32805796160807779040079277)
          ·
            refine ⟨12302173560302917140029729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32805796160807779040079277 12302173560302917140029729)
            ·
              refine ⟨9226630170227187855022297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12302173560302917140029729 9226630170227187855022297)
              ·
                refine ⟨6919972627670390891266723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9226630170227187855022297 6919972627670390891266723)
                ·
                  refine ⟨10379958941505586336900085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6919972627670390891266723 10379958941505586336900085)
                  ·
                    refine ⟨973121150766148719084383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10379958941505586336900085 973121150766148719084383)
                    ·
                      rfl

theorem cell22_2842720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_2842720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842720 prefixEnd_2842720 := by exact prefixLift 2842720
  have htrace : WordTrace (prefixWord ++ tailWord_2842720) baseStart_2842720 baseEnd_2842720 := by
    simpa [prefixWord, tailWord_2842720, baseEnd_2842720] using wordTrace_append hprefix tailTrace_2842720
  have hstable : (prefixWord ++ tailWord_2842720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842720).length < 2 ^ (prefixWord ++ tailWord_2842720).sum := by decide
  have hdescent : baseEnd_2842720 < baseStart_2842720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842805 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2842805 : Nat := 118140960795 + 2842805 * 2 ^ 59
def prefixEnd_2842805 : Nat := 4983230072969 + 3 ^ 40 * 2842805 * 2
def baseEnd_2842805 : Nat := 973150248003236830709123

theorem tailTrace_2842805 : CollatzResearch.WordTrace tailWord_2842805 prefixEnd_2842805 973150248003236830709123 := by
  unfold tailWord_2842805
  simp only [CollatzResearch.WordTrace]
  refine ⟨103685616466010472285489869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69123744310673648190326579 103685616466010472285489869)
  ·
    refine ⟨38882106174753927107058701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103685616466010472285489869 38882106174753927107058701)
    ·
      refine ⟨14580789815532722665147013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38882106174753927107058701 14580789815532722665147013)
      ·
        refine ⟨2733898090412385499715065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14580789815532722665147013 2733898090412385499715065)
        ·
          refine ⟨2050423567809289124786299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733898090412385499715065 2050423567809289124786299)
          ·
            refine ⟨3075635351713933687179449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050423567809289124786299 3075635351713933687179449)
            ·
              refine ⟨2306726513785450265384587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3075635351713933687179449 2306726513785450265384587)
              ·
                refine ⟨3460089770678175398076881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306726513785450265384587 3460089770678175398076881)
                ·
                  refine ⟨2595067328008631548557661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3460089770678175398076881 2595067328008631548557661)
                  ·
                    refine ⟨973150248003236830709123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2595067328008631548557661 973150248003236830709123)
                    ·
                      rfl

theorem cell22_2842805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2842805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842805 prefixEnd_2842805 := by exact prefixLift 2842805
  have htrace : WordTrace (prefixWord ++ tailWord_2842805) baseStart_2842805 baseEnd_2842805 := by
    simpa [prefixWord, tailWord_2842805, baseEnd_2842805] using wordTrace_append hprefix tailTrace_2842805
  have hstable : (prefixWord ++ tailWord_2842805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842805).length < 2 ^ (prefixWord ++ tailWord_2842805).sum := by decide
  have hdescent : baseEnd_2842805 < baseStart_2842805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842810 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_2842810 : Nat := 118140960795 + 2842810 * 2 ^ 59
def prefixEnd_2842810 : Nat := 4983230072969 + 3 ^ 40 * 2842810 * 2
def baseEnd_2842810 : Nat := 973151959605418484334107

theorem tailTrace_2842810 : CollatzResearch.WordTrace tailWord_2842810 prefixEnd_2842810 973151959605418484334107 := by
  unfold tailWord_2842810
  simp only [CollatzResearch.WordTrace]
  refine ⟨25921449707748089534855471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69123865887328238759614589 25921449707748089534855471)
  ·
    refine ⟨38882174561622134302283207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25921449707748089534855471 38882174561622134302283207)
    ·
      refine ⟨58323261842433201453424811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38882174561622134302283207 58323261842433201453424811)
      ·
        refine ⟨87484892763649802180137217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58323261842433201453424811 87484892763649802180137217)
        ·
          refine ⟨65613669572737351635102913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87484892763649802180137217 65613669572737351635102913)
          ·
            refine ⟨49210252179553013726327185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65613669572737351635102913 49210252179553013726327185)
            ·
              refine ⟨36907689134664760294745389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49210252179553013726327185 36907689134664760294745389)
              ·
                refine ⟨13840383425499285110529521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36907689134664760294745389 13840383425499285110529521)
                ·
                  refine ⟨10380287569124463832897141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13840383425499285110529521 10380287569124463832897141)
                  ·
                    refine ⟨973151959605418484334107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10380287569124463832897141 973151959605418484334107)
                    ·
                      rfl

theorem cell22_2842810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_2842810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842810 prefixEnd_2842810 := by exact prefixLift 2842810
  have htrace : WordTrace (prefixWord ++ tailWord_2842810) baseStart_2842810 baseEnd_2842810 := by
    simpa [prefixWord, tailWord_2842810, baseEnd_2842810] using wordTrace_append hprefix tailTrace_2842810
  have hstable : (prefixWord ++ tailWord_2842810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842810).length < 2 ^ (prefixWord ++ tailWord_2842810).sum := by decide
  have hdescent : baseEnd_2842810 < baseStart_2842810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842842 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_2842842 : Nat := 118140960795 + 2842842 * 2 ^ 59
def prefixEnd_2842842 : Nat := 4983230072969 + 3 ^ 40 * 2842842 * 2
def baseEnd_2842842 : Nat := 973162913859381067534009

theorem tailTrace_2842842 : CollatzResearch.WordTrace tailWord_2842842 prefixEnd_2842842 973162913859381067534009 := by
  unfold tailWord_2842842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25921741491719106901146695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69124643977917618403057853 25921741491719106901146695)
  ·
    refine ⟨38882612237578660351720043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25921741491719106901146695 38882612237578660351720043)
    ·
      refine ⟨58323918356367990527580065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38882612237578660351720043 58323918356367990527580065)
      ·
        refine ⟨43742938767275992895685049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58323918356367990527580065 43742938767275992895685049)
        ·
          refine ⟨32807204075456994671763787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43742938767275992895685049 32807204075456994671763787)
          ·
            refine ⟨49210806113185492007645681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32807204075456994671763787 49210806113185492007645681)
            ·
              refine ⟨36908104584889119005734261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49210806113185492007645681 36908104584889119005734261)
              ·
                refine ⟨3460134804833354906787587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36908104584889119005734261 3460134804833354906787587)
                ·
                  refine ⟨5190202207250032360181381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460134804833354906787587 5190202207250032360181381)
                  ·
                    refine ⟨973162913859381067534009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190202207250032360181381 973162913859381067534009)
                    ·
                      rfl

theorem cell22_2842842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_2842842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842842 prefixEnd_2842842 := by exact prefixLift 2842842
  have htrace : WordTrace (prefixWord ++ tailWord_2842842) baseStart_2842842 baseEnd_2842842 := by
    simpa [prefixWord, tailWord_2842842, baseEnd_2842842] using wordTrace_append hprefix tailTrace_2842842
  have hstable : (prefixWord ++ tailWord_2842842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842842).length < 2 ^ (prefixWord ++ tailWord_2842842).sum := by decide
  have hdescent : baseEnd_2842842 < baseStart_2842842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842857 : List Nat := [1, 2, 1, 1, 1, 2, 2, 8, 4]
def baseStart_2842857 : Nat := 118140960795 + 2842857 * 2 ^ 59
def prefixEnd_2842857 : Nat := 4983230072969 + 3 ^ 40 * 2842857 * 2
def baseEnd_2842857 : Nat := 324389349555308676136321

theorem tailTrace_2842857 : CollatzResearch.WordTrace tailWord_2842857 prefixEnd_2842857 324389349555308676136321 := by
  unfold tailWord_2842857
  simp only [CollatzResearch.WordTrace]
  refine ⟨103687513061822085166382825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69125008707881390110921883 103687513061822085166382825)
  ·
    refine ⟨77765634796366563874787119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103687513061822085166382825 77765634796366563874787119)
    ·
      refine ⟨116648452194549845812180679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77765634796366563874787119 116648452194549845812180679)
      ·
        refine ⟨174972678291824768718271019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116648452194549845812180679 174972678291824768718271019)
        ·
          refine ⟨262459017437737153077406529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174972678291824768718271019 262459017437737153077406529)
          ·
            refine ⟨196844263078302864808054897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262459017437737153077406529 196844263078302864808054897)
            ·
              refine ⟨147633197308727148606041173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196844263078302864808054897 147633197308727148606041173)
              ·
                refine ⟨1730076530961646272727045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 147633197308727148606041173 1730076530961646272727045)
                ·
                  refine ⟨324389349555308676136321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1730076530961646272727045 324389349555308676136321)
                  ·
                    rfl

theorem cell22_2842857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 4].length) (baseStart_2842857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842857 prefixEnd_2842857 := by exact prefixLift 2842857
  have htrace : WordTrace (prefixWord ++ tailWord_2842857) baseStart_2842857 baseEnd_2842857 := by
    simpa [prefixWord, tailWord_2842857, baseEnd_2842857] using wordTrace_append hprefix tailTrace_2842857
  have hstable : (prefixWord ++ tailWord_2842857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842857).length < 2 ^ (prefixWord ++ tailWord_2842857).sum := by decide
  have hdescent : baseEnd_2842857 < baseStart_2842857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842962 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_2842962 : Nat := 118140960795 + 2842962 * 2 ^ 59
def prefixEnd_2842962 : Nat := 4983230072969 + 3 ^ 40 * 2842962 * 2
def baseEnd_2842962 : Nat := 973203992311740754533641

theorem tailTrace_2842962 : CollatzResearch.WordTrace tailWord_2842962 prefixEnd_2842962 973203992311740754533641 := by
  unfold tailWord_2842962
  simp only [CollatzResearch.WordTrace]
  refine ⟨25922835681610422024738785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69127561817627792065970093 25922835681610422024738785)
  ·
    refine ⟨19442126761207816518554089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25922835681610422024738785 19442126761207816518554089)
    ·
      refine ⟨14581595070905862388915567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19442126761207816518554089 14581595070905862388915567)
      ·
        refine ⟨21872392606358793583373351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14581595070905862388915567 21872392606358793583373351)
        ·
          refine ⟨32808588909538190375060027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21872392606358793583373351 32808588909538190375060027)
          ·
            refine ⟨49212883364307285562590041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32808588909538190375060027 49212883364307285562590041)
            ·
              refine ⟨36909662523230464171942531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49212883364307285562590041 36909662523230464171942531)
              ·
                refine ⟨55364493784845696257913797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36909662523230464171942531 55364493784845696257913797)
                ·
                  refine ⟨10380842584658568048358837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55364493784845696257913797 10380842584658568048358837)
                  ·
                    refine ⟨973203992311740754533641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10380842584658568048358837 973203992311740754533641)
                    ·
                      rfl

theorem cell22_2842962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_2842962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842962 prefixEnd_2842962 := by exact prefixLift 2842962
  have htrace : WordTrace (prefixWord ++ tailWord_2842962) baseStart_2842962 baseEnd_2842962 := by
    simpa [prefixWord, tailWord_2842962, baseEnd_2842962] using wordTrace_append hprefix tailTrace_2842962
  have hstable : (prefixWord ++ tailWord_2842962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842962).length < 2 ^ (prefixWord ++ tailWord_2842962).sum := by decide
  have hdescent : baseEnd_2842962 < baseStart_2842962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842981 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 5]
def baseStart_2842981 : Nat := 118140960795 + 2842981 * 2 ^ 59
def prefixEnd_2842981 : Nat := 4983230072969 + 3 ^ 40 * 2842981 * 2
def baseEnd_2842981 : Nat := 324403498800010346102861

theorem tailTrace_2842981 : CollatzResearch.WordTrace tailWord_2842981 prefixEnd_2842981 324403498800010346102861 := by
  unfold tailWord_2842981
  simp only [CollatzResearch.WordTrace]
  refine ⟨103692035713372854343896797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69128023808915236229264531 103692035713372854343896797)
  ·
    refine ⟨38884513392514820378961299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103692035713372854343896797 38884513392514820378961299)
    ·
      refine ⟨58326770088772230568441949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38884513392514820378961299 58326770088772230568441949)
      ·
        refine ⟨21872538783289586463165731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58326770088772230568441949 21872538783289586463165731)
        ·
          refine ⟨32808808174934379694748597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21872538783289586463165731 32808808174934379694748597)
          ·
            refine ⟨3075825766400098096382681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32808808174934379694748597 3075825766400098096382681)
            ·
              refine ⟨2306869324800073572287011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3075825766400098096382681 2306869324800073572287011)
              ·
                refine ⟨3460303987200110358430517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306869324800073572287011 3460303987200110358430517)
                ·
                  refine ⟨324403498800010346102861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3460303987200110358430517 324403498800010346102861)
                  ·
                    rfl

theorem cell22_2842981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_2842981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842981 prefixEnd_2842981 := by exact prefixLift 2842981
  have htrace : WordTrace (prefixWord ++ tailWord_2842981) baseStart_2842981 baseEnd_2842981 := by
    simpa [prefixWord, tailWord_2842981, baseEnd_2842981] using wordTrace_append hprefix tailTrace_2842981
  have hstable : (prefixWord ++ tailWord_2842981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842981).length < 2 ^ (prefixWord ++ tailWord_2842981).sum := by decide
  have hdescent : baseEnd_2842981 < baseStart_2842981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842994 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_2842994 : Nat := 118140960795 + 2842994 * 2 ^ 59
def prefixEnd_2842994 : Nat := 4983230072969 + 3 ^ 40 * 2842994 * 2
def baseEnd_2842994 : Nat := 973214946565703337733543

theorem tailTrace_2842994 : CollatzResearch.WordTrace tailWord_2842994 prefixEnd_2842994 973214946565703337733543 := by
  unfold tailWord_2842994
  simp only [CollatzResearch.WordTrace]
  refine ⟨25923127465581439391030009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69128339908217171709413357 25923127465581439391030009)
  ·
    refine ⟨19442345599186079543272507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25923127465581439391030009 19442345599186079543272507)
    ·
      refine ⟨29163518398779119314908761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19442345599186079543272507 29163518398779119314908761)
      ·
        refine ⟨21872638799084339486181571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29163518398779119314908761 21872638799084339486181571)
        ·
          refine ⟨32808958198626509229272357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21872638799084339486181571 32808958198626509229272357)
          ·
            refine ⟨6151679662242470480488567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32808958198626509229272357 6151679662242470480488567)
            ·
              refine ⟨9227519493363705720732851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6151679662242470480488567 9227519493363705720732851)
              ·
                refine ⟨13841279240045558581099277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9227519493363705720732851 13841279240045558581099277)
                ·
                  refine ⟨5190479715017084467912229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13841279240045558581099277 5190479715017084467912229)
                  ·
                    refine ⟨973214946565703337733543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190479715017084467912229 973214946565703337733543)
                    ·
                      rfl

theorem cell22_2842994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_2842994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2842994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2842994 prefixEnd_2842994 := by exact prefixLift 2842994
  have htrace : WordTrace (prefixWord ++ tailWord_2842994) baseStart_2842994 baseEnd_2842994 := by
    simpa [prefixWord, tailWord_2842994, baseEnd_2842994] using wordTrace_append hprefix tailTrace_2842994
  have hstable : (prefixWord ++ tailWord_2842994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842994).length < 2 ^ (prefixWord ++ tailWord_2842994).sum := by decide
  have hdescent : baseEnd_2842994 < baseStart_2842994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843007 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 1, 5]
def baseStart_2843007 : Nat := 118140960795 + 2843007 * 2 ^ 59
def prefixEnd_2843007 : Nat := 4983230072969 + 3 ^ 40 * 2843007 * 2
def baseEnd_2843007 : Nat := 973219396731375637158503

theorem tailTrace_2843007 : CollatzResearch.WordTrace tailWord_2843007 prefixEnd_2843007 973219396731375637158503 := by
  unfold tailWord_2843007
  simp only [CollatzResearch.WordTrace]
  refine ⟨103692984011278660784343275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69128656007519107189562183 103692984011278660784343275)
  ·
    refine ⟨155539476016917991176514913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103692984011278660784343275 155539476016917991176514913)
    ·
      refine ⟨116654607012688493382386185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155539476016917991176514913 116654607012688493382386185)
      ·
        refine ⟨87490955259516370036789639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116654607012688493382386185 87490955259516370036789639)
        ·
          refine ⟨131236432889274555055184459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87490955259516370036789639 131236432889274555055184459)
          ·
            refine ⟨196854649333911832582776689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131236432889274555055184459 196854649333911832582776689)
            ·
              refine ⟨147640987000433874437082517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196854649333911832582776689 147640987000433874437082517)
              ·
                refine ⟨6920671265645337864238243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147640987000433874437082517 6920671265645337864238243)
                ·
                  refine ⟨10381006898468006796357365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6920671265645337864238243 10381006898468006796357365)
                  ·
                    refine ⟨973219396731375637158503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10381006898468006796357365 973219396731375637158503)
                    ·
                      rfl

theorem cell22_2843007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_2843007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843007 prefixEnd_2843007 := by exact prefixLift 2843007
  have htrace : WordTrace (prefixWord ++ tailWord_2843007) baseStart_2843007 baseEnd_2843007 := by
    simpa [prefixWord, tailWord_2843007, baseEnd_2843007] using wordTrace_append hprefix tailTrace_2843007
  have hstable : (prefixWord ++ tailWord_2843007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843007).length < 2 ^ (prefixWord ++ tailWord_2843007).sum := by decide
  have hdescent : baseEnd_2843007 < baseStart_2843007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843030 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2843030 : Nat := 118140960795 + 2843030 * 2 ^ 59
def prefixEnd_2843030 : Nat := 4983230072969 + 3 ^ 40 * 2843030 * 2
def baseEnd_2843030 : Nat := 973227270101411243833433

theorem tailTrace_2843030 : CollatzResearch.WordTrace tailWord_2843030 prefixEnd_2843030 973227270101411243833433 := by
  unfold tailWord_2843030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6480863930637208482026909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69129215260130223808287029 6480863930637208482026909)
  ·
    refine ⟨2430323973988953180760091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6480863930637208482026909 2430323973988953180760091)
    ·
      refine ⟨3645485960983429771140137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2430323973988953180760091 3645485960983429771140137)
      ·
        refine ⟨2734114470737572328355103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3645485960983429771140137 2734114470737572328355103)
        ·
          refine ⟨4101171706106358492532655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734114470737572328355103 4101171706106358492532655)
          ·
            refine ⟨6151757559159537738798983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101171706106358492532655 6151757559159537738798983)
            ·
              refine ⟨9227636338739306608198475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6151757559159537738798983 9227636338739306608198475)
              ·
                refine ⟨13841454508108959912297713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9227636338739306608198475 13841454508108959912297713)
                ·
                  refine ⟨10381090881081719934223285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13841454508108959912297713 10381090881081719934223285)
                  ·
                    refine ⟨973227270101411243833433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10381090881081719934223285 973227270101411243833433)
                    ·
                      rfl

theorem cell22_2843030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2843030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843030 prefixEnd_2843030 := by exact prefixLift 2843030
  have htrace : WordTrace (prefixWord ++ tailWord_2843030) baseStart_2843030 baseEnd_2843030 := by
    simpa [prefixWord, tailWord_2843030, baseEnd_2843030] using wordTrace_append hprefix tailTrace_2843030
  have hstable : (prefixWord ++ tailWord_2843030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843030).length < 2 ^ (prefixWord ++ tailWord_2843030).sum := by decide
  have hdescent : baseEnd_2843030 < baseStart_2843030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843176 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2843176 : Nat := 118140960795 + 2843176 * 2 ^ 59
def prefixEnd_2843176 : Nat := 4983230072969 + 3 ^ 40 * 2843176 * 2
def baseEnd_2843176 : Nat := 973277248885115529682985

theorem tailTrace_2843176 : CollatzResearch.WordTrace tailWord_2843176 prefixEnd_2843176 973277248885115529682985 := by
  unfold tailWord_2843176
  simp only [CollatzResearch.WordTrace]
  refine ⟨51849573973833201323622691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69132765298444268431496921 51849573973833201323622691)
  ·
    refine ⟨77774360960749801985434037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51849573973833201323622691 77774360960749801985434037)
    ·
      refine ⟨7291346340070293936134441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77774360960749801985434037 7291346340070293936134441)
      ·
        refine ⟨5468509755052720452100831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7291346340070293936134441 5468509755052720452100831)
        ·
          refine ⟨8202764632579080678151247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5468509755052720452100831 8202764632579080678151247)
          ·
            refine ⟨12304146948868621017226871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8202764632579080678151247 12304146948868621017226871)
            ·
              refine ⟨18456220423302931525840307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12304146948868621017226871 18456220423302931525840307)
              ·
                refine ⟨27684330634954397288760461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18456220423302931525840307 27684330634954397288760461)
                ·
                  refine ⟨10381623988107898983285173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27684330634954397288760461 10381623988107898983285173)
                  ·
                    refine ⟨973277248885115529682985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10381623988107898983285173 973277248885115529682985)
                    ·
                      rfl

theorem cell22_2843176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2843176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843176 prefixEnd_2843176 := by exact prefixLift 2843176
  have htrace : WordTrace (prefixWord ++ tailWord_2843176) baseStart_2843176 baseEnd_2843176 := by
    simpa [prefixWord, tailWord_2843176, baseEnd_2843176] using wordTrace_append hprefix tailTrace_2843176
  have hstable : (prefixWord ++ tailWord_2843176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843176).length < 2 ^ (prefixWord ++ tailWord_2843176).sum := by decide
  have hdescent : baseEnd_2843176 < baseStart_2843176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843193 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 2, 3]
def baseStart_2843193 : Nat := 118140960795 + 2843193 * 2 ^ 59
def prefixEnd_2843193 : Nat := 4983230072969 + 3 ^ 40 * 2843193 * 2
def baseEnd_2843193 : Nat := 973283068332533152007933

theorem tailTrace_2843193 : CollatzResearch.WordTrace tailWord_2843193 prefixEnd_2843193 973283068332533152007933 := by
  unfold tailWord_2843193
  simp only [CollatzResearch.WordTrace]
  refine ⟨103699767988604814550614233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69133178659069876367076155 103699767988604814550614233)
  ·
    refine ⟨77774825991453610912960675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103699767988604814550614233 77774825991453610912960675)
    ·
      refine ⟨116662238987180416369441013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77774825991453610912960675 116662238987180416369441013)
      ·
        refine ⟨10937084905048164034635095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116662238987180416369441013 10937084905048164034635095)
        ·
          refine ⟨16405627357572246051952643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10937084905048164034635095 16405627357572246051952643)
          ·
            refine ⟨24608441036358369077928965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16405627357572246051952643 24608441036358369077928965)
            ·
              refine ⟨4614082694317194202111681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24608441036358369077928965 4614082694317194202111681)
              ·
                refine ⟨3460562020737895651583761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614082694317194202111681 3460562020737895651583761)
                ·
                  refine ⟨2595421515553421738687821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3460562020737895651583761 2595421515553421738687821)
                  ·
                    refine ⟨973283068332533152007933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2595421515553421738687821 973283068332533152007933)
                    ·
                      rfl

theorem cell22_2843193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_2843193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843193 prefixEnd_2843193 := by exact prefixLift 2843193
  have htrace : WordTrace (prefixWord ++ tailWord_2843193) baseStart_2843193 baseEnd_2843193 := by
    simpa [prefixWord, tailWord_2843193, baseEnd_2843193] using wordTrace_append hprefix tailTrace_2843193
  have hstable : (prefixWord ++ tailWord_2843193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843193).length < 2 ^ (prefixWord ++ tailWord_2843193).sum := by decide
  have hdescent : baseEnd_2843193 < baseStart_2843193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843221 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_2843221 : Nat := 118140960795 + 2843221 * 2 ^ 59
def prefixEnd_2843221 : Nat := 4983230072969 + 3 ^ 40 * 2843221 * 2
def baseEnd_2843221 : Nat := 973292653304750412307847

theorem tailTrace_2843221 : CollatzResearch.WordTrace tailWord_2843221 prefixEnd_2843221 973292653304750412307847 := by
  unfold tailWord_2843221
  simp only [CollatzResearch.WordTrace]
  refine ⟨103700789232503375332633517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69133859488335583555089011 103700789232503375332633517)
  ·
    refine ⟨38887795962188765749737569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103700789232503375332633517 38887795962188765749737569)
    ·
      refine ⟨29165846971641574312303177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38887795962188765749737569 29165846971641574312303177)
      ·
        refine ⟨21874385228731180734227383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29165846971641574312303177 21874385228731180734227383)
        ·
          refine ⟨32811577843096771101341075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21874385228731180734227383 32811577843096771101341075)
          ·
            refine ⟨49217366764645156652011613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32811577843096771101341075 49217366764645156652011613)
            ·
              refine ⟨18456512536741933744504355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49217366764645156652011613 18456512536741933744504355)
              ·
                refine ⟨27684768805112900616756533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18456512536741933744504355 27684768805112900616756533)
                ·
                  refine ⟨2595447075479334432820925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27684768805112900616756533 2595447075479334432820925)
                  ·
                    refine ⟨973292653304750412307847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2595447075479334432820925 973292653304750412307847)
                    ·
                      rfl

theorem cell22_2843221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_2843221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843221 prefixEnd_2843221 := by exact prefixLift 2843221
  have htrace : WordTrace (prefixWord ++ tailWord_2843221) baseStart_2843221 baseEnd_2843221 := by
    simpa [prefixWord, tailWord_2843221, baseEnd_2843221] using wordTrace_append hprefix tailTrace_2843221
  have hstable : (prefixWord ++ tailWord_2843221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843221).length < 2 ^ (prefixWord ++ tailWord_2843221).sum := by decide
  have hdescent : baseEnd_2843221 < baseStart_2843221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843306 : List Nat := [3, 1, 5, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2843306 : Nat := 118140960795 + 2843306 * 2 ^ 59
def prefixEnd_2843306 : Nat := 4983230072969 + 3 ^ 40 * 2843306 * 2
def baseEnd_2843306 : Nat := 973321750541838523932587

theorem tailTrace_2843306 : CollatzResearch.WordTrace tailWord_2843306 prefixEnd_2843306 973321750541838523932587 := by
  unfold tailWord_2843306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25925972359298858712369443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69135926291463623232985181 25925972359298858712369443)
  ·
    refine ⟨38888958538948288068554165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25925972359298858712369443 38888958538948288068554165)
    ·
      refine ⟨3645839863026402006426953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38888958538948288068554165 3645839863026402006426953)
      ·
        refine ⟨2734379897269801504820215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3645839863026402006426953 2734379897269801504820215)
        ·
          refine ⟨4101569845904702257230323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734379897269801504820215 4101569845904702257230323)
          ·
            refine ⟨6152354768857053385845485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101569845904702257230323 6152354768857053385845485)
            ·
              refine ⟨2307133038321395019692057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6152354768857053385845485 2307133038321395019692057)
              ·
                refine ⟨1730349778741046264769043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307133038321395019692057 1730349778741046264769043)
                ·
                  refine ⟨2595524668111569397153565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1730349778741046264769043 2595524668111569397153565)
                  ·
                    refine ⟨973321750541838523932587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2595524668111569397153565 973321750541838523932587)
                    ·
                      rfl

theorem cell22_2843306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2843306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843306 prefixEnd_2843306 := by exact prefixLift 2843306
  have htrace : WordTrace (prefixWord ++ tailWord_2843306) baseStart_2843306 baseEnd_2843306 := by
    simpa [prefixWord, tailWord_2843306, baseEnd_2843306] using wordTrace_append hprefix tailTrace_2843306
  have hstable : (prefixWord ++ tailWord_2843306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843306).length < 2 ^ (prefixWord ++ tailWord_2843306).sum := by decide
  have hdescent : baseEnd_2843306 < baseStart_2843306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843390 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2843390 : Nat := 118140960795 + 2843390 * 2 ^ 59
def prefixEnd_2843390 : Nat := 4983230072969 + 3 ^ 40 * 2843390 * 2
def baseEnd_2843390 : Nat := 973350505458490304832329

theorem tailTrace_2843390 : CollatzResearch.WordTrace tailWord_2843390 prefixEnd_2843390 973350505458490304832329 := by
  unfold tailWord_2843390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12963369146111389649441953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69137968779260744797023749 12963369146111389649441953)
  ·
    refine ⟨9722526859583542237081465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12963369146111389649441953 9722526859583542237081465)
    ·
      refine ⟨7291895144687656677811099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9722526859583542237081465 7291895144687656677811099)
      ·
        refine ⟨10937842717031485016716649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7291895144687656677811099 10937842717031485016716649)
        ·
          refine ⟨8203382037773613762537487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10937842717031485016716649 8203382037773613762537487)
          ·
            refine ⟨12305073056660420643806231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8203382037773613762537487 12305073056660420643806231)
            ·
              refine ⟨18457609584990630965709347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12305073056660420643806231 18457609584990630965709347)
              ·
                refine ⟨27686414377485946448564021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18457609584990630965709347 27686414377485946448564021)
                ·
                  refine ⟨2595601347889307479552877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27686414377485946448564021 2595601347889307479552877)
                  ·
                    refine ⟨973350505458490304832329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2595601347889307479552877 973350505458490304832329)
                    ·
                      rfl

theorem cell22_2843390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2843390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843390 prefixEnd_2843390 := by exact prefixLift 2843390
  have htrace : WordTrace (prefixWord ++ tailWord_2843390) baseStart_2843390 baseEnd_2843390 := by
    simpa [prefixWord, tailWord_2843390, baseEnd_2843390] using wordTrace_append hprefix tailTrace_2843390
  have hstable : (prefixWord ++ tailWord_2843390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843390).length < 2 ^ (prefixWord ++ tailWord_2843390).sum := by decide
  have hdescent : baseEnd_2843390 < baseStart_2843390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843420 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 5]
def baseStart_2843420 : Nat := 118140960795 + 2843420 * 2 ^ 59
def prefixEnd_2843420 : Nat := 4983230072969 + 3 ^ 40 * 2843420 * 2
def baseEnd_2843420 : Nat := 324453591690526742194079

theorem tailTrace_2843420 : CollatzResearch.WordTrace tailWord_2843420 prefixEnd_2843420 324453591690526742194079 := by
  unfold tailWord_2843420
  simp only [CollatzResearch.WordTrace]
  refine ⟨51854023679391216159563857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69138698239188288212751809 51854023679391216159563857)
  ·
    refine ⟨38890517759543412119672893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51854023679391216159563857 38890517759543412119672893)
    ·
      refine ⟨14583944159828779544877335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38890517759543412119672893 14583944159828779544877335)
      ·
        refine ⟨21875916239743169317316003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14583944159828779544877335 21875916239743169317316003)
        ·
          refine ⟨32813874359614753975974005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21875916239743169317316003 32813874359614753975974005)
          ·
            refine ⟨3076300721213883185247563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32813874359614753975974005 3076300721213883185247563)
            ·
              refine ⟨4614451081820824777871345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076300721213883185247563 4614451081820824777871345)
              ·
                refine ⟨3460838311365618583403509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614451081820824777871345 3460838311365618583403509)
                ·
                  refine ⟨324453591690526742194079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3460838311365618583403509 324453591690526742194079)
                  ·
                    rfl

theorem cell22_2843420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_2843420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843420 prefixEnd_2843420 := by exact prefixLift 2843420
  have htrace : WordTrace (prefixWord ++ tailWord_2843420) baseStart_2843420 baseEnd_2843420 := by
    simpa [prefixWord, tailWord_2843420, baseEnd_2843420] using wordTrace_append hprefix tailTrace_2843420
  have hstable : (prefixWord ++ tailWord_2843420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843420).length < 2 ^ (prefixWord ++ tailWord_2843420).sum := by decide
  have hdescent : baseEnd_2843420 < baseStart_2843420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843465 : List Nat := [1, 2, 1, 1, 2, 5, 3, 3, 4]
def baseStart_2843465 : Nat := 118140960795 + 2843465 * 2 ^ 59
def prefixEnd_2843465 : Nat := 4983230072969 + 3 ^ 40 * 2843465 * 2
def baseEnd_2843465 : Nat := 324458726497071703069033

theorem tailTrace_2843465 : CollatzResearch.WordTrace tailWord_2843465 prefixEnd_2843465 324458726497071703069033 := by
  unfold tailWord_2843465
  simp only [CollatzResearch.WordTrace]
  refine ⟨103709688643619405004515849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69139792429079603336343899 103709688643619405004515849)
  ·
    refine ⟨77782266482714553753386887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103709688643619405004515849 77782266482714553753386887)
    ·
      refine ⟨116673399724071830630080331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77782266482714553753386887 116673399724071830630080331)
      ·
        refine ⟨175010099586107745945120497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116673399724071830630080331 175010099586107745945120497)
        ·
          refine ⟨131257574689580809458840373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175010099586107745945120497 131257574689580809458840373)
          ·
            refine ⟨12305397627148200886766285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131257574689580809458840373 12305397627148200886766285)
            ·
              refine ⟨4614524110180575332537357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12305397627148200886766285 4614524110180575332537357)
              ·
                refine ⟨1730446541317715749701509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4614524110180575332537357 1730446541317715749701509)
                ·
                  refine ⟨324458726497071703069033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1730446541317715749701509 324458726497071703069033)
                  ·
                    rfl

theorem cell22_2843465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 4].length) (baseStart_2843465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843465 prefixEnd_2843465 := by exact prefixLift 2843465
  have htrace : WordTrace (prefixWord ++ tailWord_2843465) baseStart_2843465 baseEnd_2843465 := by
    simpa [prefixWord, tailWord_2843465, baseEnd_2843465] using wordTrace_append hprefix tailTrace_2843465
  have hstable : (prefixWord ++ tailWord_2843465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843465).length < 2 ^ (prefixWord ++ tailWord_2843465).sum := by decide
  have hdescent : baseEnd_2843465 < baseStart_2843465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843482 : List Nat := [3, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_2843482 : Nat := 118140960795 + 2843482 * 2 ^ 59
def prefixEnd_2843482 : Nat := 4983230072969 + 3 ^ 40 * 2843482 * 2
def baseEnd_2843482 : Nat := 324460666312877577177349

theorem tailTrace_2843482 : CollatzResearch.WordTrace tailWord_2843482 prefixEnd_2843482 324460666312877577177349 := by
  unfold tailWord_2843482
  simp only [CollatzResearch.WordTrace]
  refine ⟨25927577171139454226971175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69140205789705211271923133 25927577171139454226971175)
  ·
    refine ⟨38891365756709181340456763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25927577171139454226971175 38891365756709181340456763)
    ·
      refine ⟨58337048635063772010685145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38891365756709181340456763 58337048635063772010685145)
      ·
        refine ⟨43752786476297829008013859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58337048635063772010685145 43752786476297829008013859)
        ·
          refine ⟨65629179714446743512020789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43752786476297829008013859 65629179714446743512020789)
          ·
            refine ⟨6152735598229382204251949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65629179714446743512020789 6152735598229382204251949)
            ·
              refine ⟨2307275849336018326594481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6152735598229382204251949 2307275849336018326594481)
              ·
                refine ⟨1730456887002013744945861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307275849336018326594481 1730456887002013744945861)
                ·
                  refine ⟨324460666312877577177349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1730456887002013744945861 324460666312877577177349)
                  ·
                    rfl

theorem cell22_2843482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_2843482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843482 prefixEnd_2843482 := by exact prefixLift 2843482
  have htrace : WordTrace (prefixWord ++ tailWord_2843482) baseStart_2843482 baseEnd_2843482 := by
    simpa [prefixWord, tailWord_2843482, baseEnd_2843482] using wordTrace_append hprefix tailTrace_2843482
  have hstable : (prefixWord ++ tailWord_2843482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843482).length < 2 ^ (prefixWord ++ tailWord_2843482).sum := by decide
  have hdescent : baseEnd_2843482 < baseStart_2843482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843510 : List Nat := [5, 1, 1, 3, 1, 1, 2, 8]
def baseStart_2843510 : Nat := 118140960795 + 2843510 * 2 ^ 59
def prefixEnd_2843510 : Nat := 4983230072969 + 3 ^ 40 * 2843510 * 2
def baseEnd_2843510 : Nat := 108154620434538887981329

theorem tailTrace_2843510 : CollatzResearch.WordTrace tailWord_2843510 prefixEnd_2843510 108154620434538887981329 := by
  unfold tailWord_2843510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481958120528523605618999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69140886618970918459935989 6481958120528523605618999)
  ·
    refine ⟨9722937180792785408428499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6481958120528523605618999 9722937180792785408428499)
    ·
      refine ⟨14584405771189178112642749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9722937180792785408428499 14584405771189178112642749)
      ·
        refine ⟨5469152164195941792241031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14584405771189178112642749 5469152164195941792241031)
        ·
          refine ⟨8203728246293912688361547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5469152164195941792241031 8203728246293912688361547)
          ·
            refine ⟨12305592369440869032542321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8203728246293912688361547 12305592369440869032542321)
            ·
              refine ⟨9229194277080651774406741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12305592369440869032542321 9229194277080651774406741)
              ·
                refine ⟨108154620434538887981329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9229194277080651774406741 108154620434538887981329)
                ·
                  rfl

theorem cell22_2843510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_2843510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843510 prefixEnd_2843510 := by exact prefixLift 2843510
  have htrace : WordTrace (prefixWord ++ tailWord_2843510) baseStart_2843510 baseEnd_2843510 := by
    simpa [prefixWord, tailWord_2843510, baseEnd_2843510] using wordTrace_append hprefix tailTrace_2843510
  have hstable : (prefixWord ++ tailWord_2843510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843510).length < 2 ^ (prefixWord ++ tailWord_2843510).sum := by decide
  have hdescent : baseEnd_2843510 < baseStart_2843510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843720 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_2843720 : Nat := 118140960795 + 2843720 * 2 ^ 59
def prefixEnd_2843720 : Nat := 4983230072969 + 3 ^ 40 * 2843720 * 2
def baseEnd_2843720 : Nat := 973463471202479444081317

theorem tailTrace_2843720 : CollatzResearch.WordTrace tailWord_2843720 prefixEnd_2843720 973463471202479444081317 := by
  unfold tailWord_2843720
  simp only [CollatzResearch.WordTrace]
  refine ⟨51859494628847791777524307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69145992838463722370032409 51859494628847791777524307)
  ·
    refine ⟨77789241943271687666286461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51859494628847791777524307 77789241943271687666286461)
    ·
      refine ⟨29170965728726882874857423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77789241943271687666286461 29170965728726882874857423)
      ·
        refine ⟨43756448593090324312286135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29170965728726882874857423 43756448593090324312286135)
        ·
          refine ⟨65634672889635486468429203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43756448593090324312286135 65634672889635486468429203)
          ·
            refine ⟨98452009334453229702643805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65634672889635486468429203 98452009334453229702643805)
            ·
              refine ⟨36919503500419961138491427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98452009334453229702643805 36919503500419961138491427)
              ·
                refine ⟨55379255250629941707737141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36919503500419961138491427 55379255250629941707737141)
                ·
                  refine ⟨5191805179746557035100357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55379255250629941707737141 5191805179746557035100357)
                  ·
                    refine ⟨973463471202479444081317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5191805179746557035100357 973463471202479444081317)
                    ·
                      rfl

theorem cell22_2843720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_2843720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843720 prefixEnd_2843720 := by exact prefixLift 2843720
  have htrace : WordTrace (prefixWord ++ tailWord_2843720) baseStart_2843720 baseEnd_2843720 := by
    simpa [prefixWord, tailWord_2843720, baseEnd_2843720] using wordTrace_append hprefix tailTrace_2843720
  have hstable : (prefixWord ++ tailWord_2843720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843720).length < 2 ^ (prefixWord ++ tailWord_2843720).sum := by decide
  have hdescent : baseEnd_2843720 < baseStart_2843720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843754 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_2843754 : Nat := 118140960795 + 2843754 * 2 ^ 59
def prefixEnd_2843754 : Nat := 4983230072969 + 3 ^ 40 * 2843754 * 2
def baseEnd_2843754 : Nat := 973475110097314688731213

theorem tailTrace_2843754 : CollatzResearch.WordTrace tailWord_2843754 prefixEnd_2843754 973475110097314688731213 := by
  unfold tailWord_2843754
  simp only [CollatzResearch.WordTrace]
  refine ⟨25930057334893101840446579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69146819559714938241190877 25930057334893101840446579)
  ·
    refine ⟨38895086002339652760669869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25930057334893101840446579 38895086002339652760669869)
    ·
      refine ⟨14585657250877369785251201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38895086002339652760669869 14585657250877369785251201)
      ·
        refine ⟨10939242938158027338938401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14585657250877369785251201 10939242938158027338938401)
        ·
          refine ⟨8204432203618520504203801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10939242938158027338938401 8204432203618520504203801)
          ·
            refine ⟨6153324152713890378152851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8204432203618520504203801 6153324152713890378152851)
            ·
              refine ⟨9229986229070835567229277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153324152713890378152851 9229986229070835567229277)
              ·
                refine ⟨3461244835901563337710979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9229986229070835567229277 3461244835901563337710979)
                ·
                  refine ⟨5191867253852345006566469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461244835901563337710979 5191867253852345006566469)
                  ·
                    refine ⟨973475110097314688731213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5191867253852345006566469 973475110097314688731213)
                    ·
                      rfl

theorem cell22_2843754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_2843754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843754 prefixEnd_2843754 := by exact prefixLift 2843754
  have htrace : WordTrace (prefixWord ++ tailWord_2843754) baseStart_2843754 baseEnd_2843754 := by
    simpa [prefixWord, tailWord_2843754, baseEnd_2843754] using wordTrace_append hprefix tailTrace_2843754
  have hstable : (prefixWord ++ tailWord_2843754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843754).length < 2 ^ (prefixWord ++ tailWord_2843754).sum := by decide
  have hdescent : baseEnd_2843754 < baseStart_2843754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843767 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 4, 3]
def baseStart_2843767 : Nat := 118140960795 + 2843767 * 2 ^ 59
def prefixEnd_2843767 : Nat := 4983230072969 + 3 ^ 40 * 2843767 * 2
def baseEnd_2843767 : Nat := 973479560262986988156173

theorem tailTrace_2843767 : CollatzResearch.WordTrace tailWord_2843767 prefixEnd_2843767 973479560262986988156173 := by
  unfold tailWord_2843767
  simp only [CollatzResearch.WordTrace]
  refine ⟨103720703488525310582009555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69147135659016873721339703 103720703488525310582009555)
  ·
    refine ⟨155581055232787965873014333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103720703488525310582009555 155581055232787965873014333)
    ·
      refine ⟨58342895712295487202380375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155581055232787965873014333 58342895712295487202380375)
      ·
        refine ⟨87514343568443230803570563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58342895712295487202380375 87514343568443230803570563)
        ·
          refine ⟨131271515352664846205355845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87514343568443230803570563 131271515352664846205355845)
          ·
            refine ⟨24613409128624658663504221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131271515352664846205355845 24613409128624658663504221)
            ·
              refine ⟨9230028423234246998814083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24613409128624658663504221 9230028423234246998814083)
              ·
                refine ⟨13845042634851370498221125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9230028423234246998814083 13845042634851370498221125)
                ·
                  refine ⟨2595945494034631968416461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13845042634851370498221125 2595945494034631968416461)
                  ·
                    refine ⟨973479560262986988156173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2595945494034631968416461 973479560262986988156173)
                    ·
                      rfl

theorem cell22_2843767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_2843767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843767 prefixEnd_2843767 := by exact prefixLift 2843767
  have htrace : WordTrace (prefixWord ++ tailWord_2843767) baseStart_2843767 baseEnd_2843767 := by
    simpa [prefixWord, tailWord_2843767, baseEnd_2843767] using wordTrace_append hprefix tailTrace_2843767
  have hstable : (prefixWord ++ tailWord_2843767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843767).length < 2 ^ (prefixWord ++ tailWord_2843767).sum := by decide
  have hdescent : baseEnd_2843767 < baseStart_2843767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843936 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 4, 3]
def baseStart_2843936 : Nat := 118140960795 + 2843936 * 2 ^ 59
def prefixEnd_2843936 : Nat := 4983230072969 + 3 ^ 40 * 2843936 * 2
def baseEnd_2843936 : Nat := 973537412416726880680655

theorem tailTrace_2843936 : CollatzResearch.WordTrace tailWord_2843936 prefixEnd_2843936 973537412416726880680655 := by
  unfold tailWord_2843936
  simp only [CollatzResearch.WordTrace]
  refine ⟨51863433712456526222455831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69151244949942034963274441 51863433712456526222455831)
  ·
    refine ⟨77795150568684789333683747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51863433712456526222455831 77795150568684789333683747)
    ·
      refine ⟨116692725853027184000525621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77795150568684789333683747 116692725853027184000525621)
      ·
        refine ⟨10939943048721298500049277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116692725853027184000525621 10939943048721298500049277)
        ·
          refine ⟨4102478643270486937518479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10939943048721298500049277 4102478643270486937518479)
          ·
            refine ⟨6153717964905730406277719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4102478643270486937518479 6153717964905730406277719)
            ·
              refine ⟨9230576947358595609416579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153717964905730406277719 9230576947358595609416579)
              ·
                refine ⟨13845865421037893414124869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9230576947358595609416579 13845865421037893414124869)
                ·
                  refine ⟨2596099766444605015148413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13845865421037893414124869 2596099766444605015148413)
                  ·
                    refine ⟨973537412416726880680655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596099766444605015148413 973537412416726880680655)
                    ·
                      rfl

theorem cell22_2843936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_2843936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843936 prefixEnd_2843936 := by exact prefixLift 2843936
  have htrace : WordTrace (prefixWord ++ tailWord_2843936) baseStart_2843936 baseEnd_2843936 := by
    simpa [prefixWord, tailWord_2843936, baseEnd_2843936] using wordTrace_append hprefix tailTrace_2843936
  have hstable : (prefixWord ++ tailWord_2843936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843936).length < 2 ^ (prefixWord ++ tailWord_2843936).sum := by decide
  have hdescent : baseEnd_2843936 < baseStart_2843936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843953 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 2, 3]
def baseStart_2843953 : Nat := 118140960795 + 2843953 * 2 ^ 59
def prefixEnd_2843953 : Nat := 4983230072969 + 3 ^ 40 * 2843953 * 2
def baseEnd_2843953 : Nat := 973543231864144503005603

theorem tailTrace_2843953 : CollatzResearch.WordTrace tailWord_2843953 prefixEnd_2843953 973543231864144503005603 := by
  unfold tailWord_2843953
  simp only [CollatzResearch.WordTrace]
  refine ⟨103727487465851464348280513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69151658310567642898853675 103727487465851464348280513)
  ·
    refine ⟨77795615599388598261210385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103727487465851464348280513 77795615599388598261210385)
    ·
      refine ⟨58346711699541448695907789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77795615599388598261210385 58346711699541448695907789)
      ·
        refine ⟨21880016887328043260965421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58346711699541448695907789 21880016887328043260965421)
        ·
          refine ⟨8205006332748016222862033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21880016887328043260965421 8205006332748016222862033)
          ·
            refine ⟨6153754749561012167146525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8205006332748016222862033 6153754749561012167146525)
            ·
              refine ⟨2307658031085379562679947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6153754749561012167146525 2307658031085379562679947)
              ·
                refine ⟨3461487046628069344019921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307658031085379562679947 3461487046628069344019921)
                ·
                  refine ⟨2596115284971052008014941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3461487046628069344019921 2596115284971052008014941)
                  ·
                    refine ⟨973543231864144503005603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596115284971052008014941 973543231864144503005603)
                    ·
                      rfl

theorem cell22_2843953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_2843953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843953 prefixEnd_2843953 := by exact prefixLift 2843953
  have htrace : WordTrace (prefixWord ++ tailWord_2843953) baseStart_2843953 baseEnd_2843953 := by
    simpa [prefixWord, tailWord_2843953, baseEnd_2843953] using wordTrace_append hprefix tailTrace_2843953
  have hstable : (prefixWord ++ tailWord_2843953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843953).length < 2 ^ (prefixWord ++ tailWord_2843953).sum := by decide
  have hdescent : baseEnd_2843953 < baseStart_2843953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843977 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 7]
def baseStart_2843977 : Nat := 118140960795 + 2843977 * 2 ^ 59
def prefixEnd_2843977 : Nat := 4983230072969 + 3 ^ 40 * 2843977 * 2
def baseEnd_2843977 : Nat := 324517149184872146801843

theorem tailTrace_2843977 : CollatzResearch.WordTrace tailWord_2843977 prefixEnd_2843977 324517149184872146801843 := by
  unfold tailWord_2843977
  simp only [CollatzResearch.WordTrace]
  refine ⟨103728362817764516447154185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69152241878509677631436123 103728362817764516447154185)
  ·
    refine ⟨77796272113323387335365639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103728362817764516447154185 77796272113323387335365639)
    ·
      refine ⟨116694408169985081003048459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77796272113323387335365639 116694408169985081003048459)
      ·
        refine ⟨175041612254977621504572689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116694408169985081003048459 175041612254977621504572689)
        ·
          refine ⟨131281209191233216128429517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175041612254977621504572689 131281209191233216128429517)
          ·
            refine ⟨49230453446712456048161069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131281209191233216128429517 49230453446712456048161069)
            ·
              refine ⟨18461420042517171018060401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49230453446712456048161069 18461420042517171018060401)
              ·
                refine ⟨13846065031887878263545301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18461420042517171018060401 13846065031887878263545301)
                ·
                  refine ⟨324517149184872146801843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13846065031887878263545301 324517149184872146801843)
                  ·
                    rfl

theorem cell22_2843977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_2843977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2843977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2843977 prefixEnd_2843977 := by exact prefixLift 2843977
  have htrace : WordTrace (prefixWord ++ tailWord_2843977) baseStart_2843977 baseEnd_2843977 := by
    simpa [prefixWord, tailWord_2843977, baseEnd_2843977] using wordTrace_append hprefix tailTrace_2843977
  have hstable : (prefixWord ++ tailWord_2843977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843977).length < 2 ^ (prefixWord ++ tailWord_2843977).sum := by decide
  have hdescent : baseEnd_2843977 < baseStart_2843977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844071 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2844071 : Nat := 118140960795 + 2844071 * 2 ^ 59
def prefixEnd_2844071 : Nat := 4983230072969 + 3 ^ 40 * 2844071 * 2
def baseEnd_2844071 : Nat := 973583625675631528555241

theorem tailTrace_2844071 : CollatzResearch.WordTrace tailWord_2844071 prefixEnd_2844071 973583625675631528555241 := by
  unfold tailWord_2844071
  simp only [CollatzResearch.WordTrace]
  refine ⟨103731791279423970501076067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69154527519615980334050711 103731791279423970501076067)
  ·
    refine ⟨155597686919135955751614101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103731791279423970501076067 155597686919135955751614101)
    ·
      refine ⟨7293641574334497925856911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155597686919135955751614101 7293641574334497925856911)
      ·
        refine ⟨10940462361501746888785367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7293641574334497925856911 10940462361501746888785367)
        ·
          refine ⟨16410693542252620333178051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10940462361501746888785367 16410693542252620333178051)
          ·
            refine ⟨24616040313378930499767077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16410693542252620333178051 24616040313378930499767077)
            ·
              refine ⟨4615507558758549468706327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24616040313378930499767077 4615507558758549468706327)
              ·
                refine ⟨6923261338137824203059491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615507558758549468706327 6923261338137824203059491)
                ·
                  refine ⟨10384892007206736304589237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6923261338137824203059491 10384892007206736304589237)
                  ·
                    refine ⟨973583625675631528555241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10384892007206736304589237 973583625675631528555241)
                    ·
                      rfl

theorem cell22_2844071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2844071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844071 prefixEnd_2844071 := by exact prefixLift 2844071
  have htrace : WordTrace (prefixWord ++ tailWord_2844071) baseStart_2844071 baseEnd_2844071 := by
    simpa [prefixWord, tailWord_2844071, baseEnd_2844071] using wordTrace_append hprefix tailTrace_2844071
  have hstable : (prefixWord ++ tailWord_2844071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844071).length < 2 ^ (prefixWord ++ tailWord_2844071).sum := by decide
  have hdescent : baseEnd_2844071 < baseStart_2844071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844092 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 1, 4]
def baseStart_2844092 : Nat := 118140960795 + 2844092 * 2 ^ 59
def prefixEnd_2844092 : Nat := 4983230072969 + 3 ^ 40 * 2844092 * 2
def baseEnd_2844092 : Nat := 973590814404794473780177

theorem tailTrace_2844092 : CollatzResearch.WordTrace tailWord_2844092 prefixEnd_2844092 973590814404794473780177 := by
  unfold tailWord_2844092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51866278606173945543795265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69155038141565260725060353 51866278606173945543795265)
  ·
    refine ⟨38899708954630459157846449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51866278606173945543795265 38899708954630459157846449)
    ·
      refine ⟨29174781715972844368384837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38899708954630459157846449 29174781715972844368384837)
      ·
        refine ⟨5470271571744908319072157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29174781715972844368384837 5470271571744908319072157)
        ·
          refine ⟨2051351839404340619652059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5470271571744908319072157 2051351839404340619652059)
          ·
            refine ⟨3077027759106510929478089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051351839404340619652059 3077027759106510929478089)
            ·
              refine ⟨2307770819329883197108567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3077027759106510929478089 2307770819329883197108567)
              ·
                refine ⟨3461656228994824795662851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307770819329883197108567 3461656228994824795662851)
                ·
                  refine ⟨5192484343492237193494277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461656228994824795662851 5192484343492237193494277)
                  ·
                    refine ⟨973590814404794473780177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5192484343492237193494277 973590814404794473780177)
                    ·
                      rfl

theorem cell22_2844092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_2844092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844092 prefixEnd_2844092 := by exact prefixLift 2844092
  have htrace : WordTrace (prefixWord ++ tailWord_2844092) baseStart_2844092 baseEnd_2844092 := by
    simpa [prefixWord, tailWord_2844092, baseEnd_2844092] using wordTrace_append hprefix tailTrace_2844092
  have hstable : (prefixWord ++ tailWord_2844092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844092).length < 2 ^ (prefixWord ++ tailWord_2844092).sum := by decide
  have hdescent : baseEnd_2844092 < baseStart_2844092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844133 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_2844133 : Nat := 118140960795 + 2844133 * 2 ^ 59
def prefixEnd_2844133 : Nat := 4983230072969 + 3 ^ 40 * 2844133 * 2
def baseEnd_2844133 : Nat := 973604849542684033505051

theorem tailTrace_2844133 : CollatzResearch.WordTrace tailWord_2844133 prefixEnd_2844133 973604849542684033505051 := by
  unfold tailWord_2844133
  simp only [CollatzResearch.WordTrace]
  refine ⟨103734052605199355089833053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69156035070132903393222035 103734052605199355089833053)
  ·
    refine ⟨38900269726949758158687395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103734052605199355089833053 38900269726949758158687395)
    ·
      refine ⟨58350404590424637238031093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38900269726949758158687395 58350404590424637238031093)
      ·
        refine ⟨5470350430352309741065415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58350404590424637238031093 5470350430352309741065415)
        ·
          refine ⟨8205525645528464611598123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5470350430352309741065415 8205525645528464611598123)
          ·
            refine ⟨12308288468292696917397185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8205525645528464611598123 12308288468292696917397185)
            ·
              refine ⟨9231216351219522688047889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12308288468292696917397185 9231216351219522688047889)
              ·
                refine ⟨6923412263414642016035917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9231216351219522688047889 6923412263414642016035917)
                ·
                  refine ⟨2596279598780490756013469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6923412263414642016035917 2596279598780490756013469)
                  ·
                    refine ⟨973604849542684033505051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596279598780490756013469 973604849542684033505051)
                    ·
                      rfl

theorem cell22_2844133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_2844133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844133 prefixEnd_2844133 := by exact prefixLift 2844133
  have htrace : WordTrace (prefixWord ++ tailWord_2844133) baseStart_2844133 baseEnd_2844133 := by
    simpa [prefixWord, tailWord_2844133, baseEnd_2844133] using wordTrace_append hprefix tailTrace_2844133
  have hstable : (prefixWord ++ tailWord_2844133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844133).length < 2 ^ (prefixWord ++ tailWord_2844133).sum := by decide
  have hdescent : baseEnd_2844133 < baseStart_2844133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844146 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_2844146 : Nat := 118140960795 + 2844146 * 2 ^ 59
def prefixEnd_2844146 : Nat := 4983230072969 + 3 ^ 40 * 2844146 * 2
def baseEnd_2844146 : Nat := 324536433236118777643337

theorem tailTrace_2844146 : CollatzResearch.WordTrace tailWord_2844146 prefixEnd_2844146 324536433236118777643337 := by
  unfold tailWord_2844146
  simp only [CollatzResearch.WordTrace]
  refine ⟨25933631688538064577514073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69156351169434838873370861 25933631688538064577514073)
  ·
    refine ⟨19450223766403548433135555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25933631688538064577514073 19450223766403548433135555)
    ·
      refine ⟨29175335649605322649703333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19450223766403548433135555 29175335649605322649703333)
      ·
        refine ⟨5470375434300997996819375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29175335649605322649703333 5470375434300997996819375)
        ·
          refine ⟨8205563151451496995229063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5470375434300997996819375 8205563151451496995229063)
          ·
            refine ⟨12308344727177245492843595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8205563151451496995229063 12308344727177245492843595)
            ·
              refine ⟨18462517090765868239265393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12308344727177245492843595 18462517090765868239265393)
              ·
                refine ⟨13846887818074401179449045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18462517090765868239265393 13846887818074401179449045)
                ·
                  refine ⟨324536433236118777643337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13846887818074401179449045 324536433236118777643337)
                  ·
                    rfl

theorem cell22_2844146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_2844146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844146 prefixEnd_2844146 := by exact prefixLift 2844146
  have htrace : WordTrace (prefixWord ++ tailWord_2844146) baseStart_2844146 baseEnd_2844146 := by
    simpa [prefixWord, tailWord_2844146, baseEnd_2844146] using wordTrace_append hprefix tailTrace_2844146
  have hstable : (prefixWord ++ tailWord_2844146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844146).length < 2 ^ (prefixWord ++ tailWord_2844146).sum := by decide
  have hdescent : baseEnd_2844146 < baseStart_2844146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844167 : List Nat := [1, 1, 4, 3, 2, 2, 3, 2, 1, 3]
def baseStart_2844167 : Nat := 118140960795 + 2844167 * 2 ^ 59
def prefixEnd_2844167 : Nat := 4983230072969 + 3 ^ 40 * 2844167 * 2
def baseEnd_2844167 : Nat := 973616488437519278154947

theorem tailTrace_2844167 : CollatzResearch.WordTrace tailWord_2844167 prefixEnd_2844167 973616488437519278154947 := by
  unfold tailWord_2844167
  simp only [CollatzResearch.WordTrace]
  refine ⟨103735292687076178896570755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69156861791384119264380503 103735292687076178896570755)
  ·
    refine ⟨155602939030614268344856133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103735292687076178896570755 155602939030614268344856133)
    ·
      refine ⟨29175551068240175314660525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155602939030614268344856133 29175551068240175314660525)
      ·
        refine ⟨10940831650590065742997697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29175551068240175314660525 10940831650590065742997697)
        ·
          refine ⟨8205623737942549307248273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10940831650590065742997697 8205623737942549307248273)
          ·
            refine ⟨6154217803456911980436205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8205623737942549307248273 6154217803456911980436205)
            ·
              refine ⟨2307831676296341992663577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6154217803456911980436205 2307831676296341992663577)
              ·
                refine ⟨1730873757222256494497683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307831676296341992663577 1730873757222256494497683)
                ·
                  refine ⟨2596310635833384741746525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1730873757222256494497683 2596310635833384741746525)
                  ·
                    refine ⟨973616488437519278154947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596310635833384741746525 973616488437519278154947)
                    ·
                      rfl

theorem cell22_2844167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_2844167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844167 prefixEnd_2844167 := by exact prefixLift 2844167
  have htrace : WordTrace (prefixWord ++ tailWord_2844167) baseStart_2844167 baseEnd_2844167 := by
    simpa [prefixWord, tailWord_2844167, baseEnd_2844167] using wordTrace_append hprefix tailTrace_2844167
  have hstable : (prefixWord ++ tailWord_2844167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844167).length < 2 ^ (prefixWord ++ tailWord_2844167).sum := by decide
  have hdescent : baseEnd_2844167 < baseStart_2844167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844180 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 5]
def baseStart_2844180 : Nat := 118140960795 + 2844180 * 2 ^ 59
def prefixEnd_2844180 : Nat := 4983230072969 + 3 ^ 40 * 2844180 * 2
def baseEnd_2844180 : Nat := 324540312867730525859969

theorem tailTrace_2844180 : CollatzResearch.WordTrace tailWord_2844180 prefixEnd_2844180 324540312867730525859969 := by
  unfold tailWord_2844180
  simp only [CollatzResearch.WordTrace]
  refine ⟨51867883418014541058396997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69157177890686054744529329 51867883418014541058396997)
  ·
    refine ⟨9725228140877726448449437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51867883418014541058396997 9725228140877726448449437)
    ·
      refine ⟨3646960552829147418168539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9725228140877726448449437 3646960552829147418168539)
      ·
        refine ⟨5470440829243721127252809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3646960552829147418168539 5470440829243721127252809)
        ·
          refine ⟨4102830621932790845439607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5470440829243721127252809 4102830621932790845439607)
          ·
            refine ⟨6154245932899186268159411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4102830621932790845439607 6154245932899186268159411)
            ·
              refine ⟨9231368899348779402239117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6154245932899186268159411 9231368899348779402239117)
              ·
                refine ⟨3461763337255792275839669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9231368899348779402239117 3461763337255792275839669)
                ·
                  refine ⟨324540312867730525859969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3461763337255792275839669 324540312867730525859969)
                  ·
                    rfl

theorem cell22_2844180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_2844180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844180 prefixEnd_2844180 := by exact prefixLift 2844180
  have htrace : WordTrace (prefixWord ++ tailWord_2844180) baseStart_2844180 baseEnd_2844180 := by
    simpa [prefixWord, tailWord_2844180, baseEnd_2844180] using wordTrace_append hprefix tailTrace_2844180
  have hstable : (prefixWord ++ tailWord_2844180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844180).length < 2 ^ (prefixWord ++ tailWord_2844180).sum := by decide
  have hdescent : baseEnd_2844180 < baseStart_2844180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844193 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_2844193 : Nat := 118140960795 + 2844193 * 2 ^ 59
def prefixEnd_2844193 : Nat := 4983230072969 + 3 ^ 40 * 2844193 * 2
def baseEnd_2844193 : Nat := 973625388768863877004867

theorem tailTrace_2844193 : CollatzResearch.WordTrace tailWord_2844193 prefixEnd_2844193 973625388768863877004867 := by
  unfold tailWord_2844193
  simp only [CollatzResearch.WordTrace]
  refine ⟨103736240984981985337017233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69157493989987990224678155 103736240984981985337017233)
  ·
    refine ⟨77802180738736489002762925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103736240984981985337017233 77802180738736489002762925)
    ·
      refine ⟨29175817777026183376036097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77802180738736489002762925 29175817777026183376036097)
      ·
        refine ⟨21881863332769637532027073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29175817777026183376036097 21881863332769637532027073)
        ·
          refine ⟨16411397499577228149020305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21881863332769637532027073 16411397499577228149020305)
          ·
            refine ⟨12308548124682921111765229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16411397499577228149020305 12308548124682921111765229)
            ·
              refine ⟨4615705546756095416911961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12308548124682921111765229 4615705546756095416911961)
              ·
                refine ⟨3461779160067071562683971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4615705546756095416911961 3461779160067071562683971)
                ·
                  refine ⟨5192668740100607344025957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461779160067071562683971 5192668740100607344025957)
                  ·
                    refine ⟨973625388768863877004867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5192668740100607344025957 973625388768863877004867)
                    ·
                      rfl

theorem cell22_2844193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_2844193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844193 prefixEnd_2844193 := by exact prefixLift 2844193
  have htrace : WordTrace (prefixWord ++ tailWord_2844193) baseStart_2844193 baseEnd_2844193 := by
    simpa [prefixWord, tailWord_2844193, baseEnd_2844193] using wordTrace_append hprefix tailTrace_2844193
  have hstable : (prefixWord ++ tailWord_2844193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844193).length < 2 ^ (prefixWord ++ tailWord_2844193).sum := by decide
  have hdescent : baseEnd_2844193 < baseStart_2844193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844223 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 2, 3]
def baseStart_2844223 : Nat := 118140960795 + 2844223 * 2 ^ 59
def prefixEnd_2844223 : Nat := 4983230072969 + 3 ^ 40 * 2844223 * 2
def baseEnd_2844223 : Nat := 973635658381953798754775

theorem tailTrace_2844223 : CollatzResearch.WordTrace tailWord_2844223 prefixEnd_2844223 973635658381953798754775 := by
  unfold tailWord_2844223
  simp only [CollatzResearch.WordTrace]
  refine ⟨103737335174873300460609323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69158223449915533640406215 103737335174873300460609323)
  ·
    refine ⟨155606002762309950690913985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103737335174873300460609323 155606002762309950690913985)
    ·
      refine ⟨116704502071732463018185489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155606002762309950690913985 116704502071732463018185489)
      ·
        refine ⟨87528376553799347263639117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116704502071732463018185489 87528376553799347263639117)
        ·
          refine ⟨32823141207674755223864669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87528376553799347263639117 32823141207674755223864669)
          ·
            refine ⟨12308677952878033208949251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32823141207674755223864669 12308677952878033208949251)
            ·
              refine ⟨18463016929317049813423877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12308677952878033208949251 18463016929317049813423877)
              ·
                refine ⟨3461815674246946840016977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18463016929317049813423877 3461815674246946840016977)
                ·
                  refine ⟨2596361755685210130012733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3461815674246946840016977 2596361755685210130012733)
                  ·
                    refine ⟨973635658381953798754775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596361755685210130012733 973635658381953798754775)
                    ·
                      rfl

theorem cell22_2844223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_2844223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844223 prefixEnd_2844223 := by exact prefixLift 2844223
  have htrace : WordTrace (prefixWord ++ tailWord_2844223) baseStart_2844223 baseEnd_2844223 := by
    simpa [prefixWord, tailWord_2844223, baseEnd_2844223] using wordTrace_append hprefix tailTrace_2844223
  have hstable : (prefixWord ++ tailWord_2844223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844223).length < 2 ^ (prefixWord ++ tailWord_2844223).sum := by decide
  have hdescent : baseEnd_2844223 < baseStart_2844223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844236 : List Nat := [2, 2, 1, 3, 1, 3, 3, 7]
def baseStart_2844236 : Nat := 118140960795 + 2844236 * 2 ^ 59
def prefixEnd_2844236 : Nat := 4983230072969 + 3 ^ 40 * 2844236 * 2
def baseEnd_2844236 : Nat := 108182234283069566464415

theorem tailTrace_2844236 : CollatzResearch.WordTrace tailWord_2844236 prefixEnd_2844236 108182234283069566464415 := by
  unfold tailWord_2844236
  simp only [CollatzResearch.WordTrace]
  refine ⟨51868904661913101840416281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69158539549217469120555041 51868904661913101840416281)
  ·
    refine ⟨38901678496434826380312211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51868904661913101840416281 38901678496434826380312211)
    ·
      refine ⟨58352517744652239570468317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38901678496434826380312211 58352517744652239570468317)
      ·
        refine ⟨21882194154244589838925619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58352517744652239570468317 21882194154244589838925619)
        ·
          refine ⟨32823291231366884758388429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21882194154244589838925619 32823291231366884758388429)
          ·
            refine ⟨12308734211762581784395661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32823291231366884758388429 12308734211762581784395661)
            ·
              refine ⟨4615775329410968169148373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12308734211762581784395661 4615775329410968169148373)
              ·
                refine ⟨108182234283069566464415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4615775329410968169148373 108182234283069566464415)
                ·
                  rfl

theorem cell22_2844236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 7].length) (baseStart_2844236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844236 prefixEnd_2844236 := by exact prefixLift 2844236
  have htrace : WordTrace (prefixWord ++ tailWord_2844236) baseStart_2844236 baseEnd_2844236 := by
    simpa [prefixWord, tailWord_2844236, baseEnd_2844236] using wordTrace_append hprefix tailTrace_2844236
  have hstable : (prefixWord ++ tailWord_2844236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844236).length < 2 ^ (prefixWord ++ tailWord_2844236).sum := by decide
  have hdescent : baseEnd_2844236 < baseStart_2844236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844281 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 7]
def baseStart_2844281 : Nat := 118140960795 + 2844281 * 2 ^ 59
def prefixEnd_2844281 : Nat := 4983230072969 + 3 ^ 40 * 2844281 * 2
def baseEnd_2844281 : Nat := 324551837655753660268199

theorem tailTrace_2844281 : CollatzResearch.WordTrace tailWord_2844281 prefixEnd_2844281 324551837655753660268199 := by
  unfold tailWord_2844281
  simp only [CollatzResearch.WordTrace]
  refine ⟨103739450608663176366220697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69159633739108784244147131 103739450608663176366220697)
  ·
    refine ⟨77804587956497382274665523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103739450608663176366220697 77804587956497382274665523)
    ·
      refine ⟨116706881934746073411998285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77804587956497382274665523 116706881934746073411998285)
      ·
        refine ⟨43765080725529777529499357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116706881934746073411998285 43765080725529777529499357)
        ·
          refine ⟨16411905272073666573562259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43765080725529777529499357 16411905272073666573562259)
          ·
            refine ⟨24617857908110499860343389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16411905272073666573562259 24617857908110499860343389)
            ·
              refine ⟨9231696715541437447628771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24617857908110499860343389 9231696715541437447628771)
              ·
                refine ⟨13847545073312156171443157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9231696715541437447628771 13847545073312156171443157)
                ·
                  refine ⟨324551837655753660268199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13847545073312156171443157 324551837655753660268199)
                  ·
                    rfl

theorem cell22_2844281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_2844281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844281 prefixEnd_2844281 := by exact prefixLift 2844281
  have htrace : WordTrace (prefixWord ++ tailWord_2844281) baseStart_2844281 baseEnd_2844281 := by
    simpa [prefixWord, tailWord_2844281, baseEnd_2844281] using wordTrace_append hprefix tailTrace_2844281
  have hstable : (prefixWord ++ tailWord_2844281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844281).length < 2 ^ (prefixWord ++ tailWord_2844281).sum := by decide
  have hdescent : baseEnd_2844281 < baseStart_2844281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844285 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_2844285 : Nat := 118140960795 + 2844285 * 2 ^ 59
def prefixEnd_2844285 : Nat := 4983230072969 + 3 ^ 40 * 2844285 * 2
def baseEnd_2844285 : Nat := 973656882249006303704585

theorem tailTrace_2844285 : CollatzResearch.WordTrace tailWord_2844285 prefixEnd_2844285 973656882249006303704585 := by
  unfold tailWord_2844285
  simp only [CollatzResearch.WordTrace]
  refine ⟨103739596500648685049366309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69159731000432456699577539 103739596500648685049366309)
  ·
    refine ⟨19451174343871628446756183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103739596500648685049366309 19451174343871628446756183)
    ·
      refine ⟨29176761515807442670134275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19451174343871628446756183 29176761515807442670134275)
      ·
        refine ⟨43765142273711164005201413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29176761515807442670134275 43765142273711164005201413)
        ·
          refine ⟨8205964176320843250975265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43765142273711164005201413 8205964176320843250975265)
          ·
            refine ⟨6154473132240632438231449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8205964176320843250975265 6154473132240632438231449)
            ·
              refine ⟨4615854849180474328673587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6154473132240632438231449 4615854849180474328673587)
              ·
                refine ⟨6923782273770711493010381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615854849180474328673587 6923782273770711493010381)
                ·
                  refine ⟨2596418352664016809878893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6923782273770711493010381 2596418352664016809878893)
                  ·
                    refine ⟨973656882249006303704585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596418352664016809878893 973656882249006303704585)
                    ·
                      rfl

theorem cell22_2844285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_2844285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844285 prefixEnd_2844285 := by exact prefixLift 2844285
  have htrace : WordTrace (prefixWord ++ tailWord_2844285) baseStart_2844285 baseEnd_2844285 := by
    simpa [prefixWord, tailWord_2844285, baseEnd_2844285] using wordTrace_append hprefix tailTrace_2844285
  have hstable : (prefixWord ++ tailWord_2844285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844285).length < 2 ^ (prefixWord ++ tailWord_2844285).sum := by decide
  have hdescent : baseEnd_2844285 < baseStart_2844285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844343 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 6]
def baseStart_2844343 : Nat := 118140960795 + 2844343 * 2 ^ 59
def prefixEnd_2844343 : Nat := 4983230072969 + 3 ^ 40 * 2844343 * 2
def baseEnd_2844343 : Nat := 324558912278104495251469

theorem tailTrace_2844343 : CollatzResearch.WordTrace tailWord_2844343 prefixEnd_2844343 324558912278104495251469 := by
  unfold tailWord_2844343
  simp only [CollatzResearch.WordTrace]
  refine ⟨103741711934438560954977683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69161141289625707303318455 103741711934438560954977683)
  ·
    refine ⟨155612567901657841432466525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103741711934438560954977683 155612567901657841432466525)
    ·
      refine ⟨58354712963121690537174947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155612567901657841432466525 58354712963121690537174947)
      ·
        refine ⟨87532069444682535805762421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58354712963121690537174947 87532069444682535805762421)
        ·
          refine ⟨8206131510438987731790227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87532069444682535805762421 8206131510438987731790227)
          ·
            refine ⟨12309197265658481597685341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8206131510438987731790227 12309197265658481597685341)
            ·
              refine ⟨4615948974621930599132003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12309197265658481597685341 4615948974621930599132003)
              ·
                refine ⟨6923923461932895898698005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615948974621930599132003 6923923461932895898698005)
                ·
                  refine ⟨324558912278104495251469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6923923461932895898698005 324558912278104495251469)
                  ·
                    rfl

theorem cell22_2844343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 6].length) (baseStart_2844343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844343 prefixEnd_2844343 := by exact prefixLift 2844343
  have htrace : WordTrace (prefixWord ++ tailWord_2844343) baseStart_2844343 baseEnd_2844343 := by
    simpa [prefixWord, tailWord_2844343, baseEnd_2844343] using wordTrace_append hprefix tailTrace_2844343
  have hstable : (prefixWord ++ tailWord_2844343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844343).length < 2 ^ (prefixWord ++ tailWord_2844343).sum := by decide
  have hdescent : baseEnd_2844343 < baseStart_2844343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844362 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_2844362 : Nat := 118140960795 + 2844362 * 2 ^ 59
def prefixEnd_2844362 : Nat := 4983230072969 + 3 ^ 40 * 2844362 * 2
def baseEnd_2844362 : Nat := 973683240922603769529349

theorem tailTrace_2844362 : CollatzResearch.WordTrace tailWord_2844362 prefixEnd_2844362 973683240922603769529349 := by
  unfold tailWord_2844362
  simp only [CollatzResearch.WordTrace]
  refine ⟨25935601230342431799979835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69161603280913151466612893 25935601230342431799979835)
  ·
    refine ⟨38903401845513647699969753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25935601230342431799979835 38903401845513647699969753)
    ·
      refine ⟨29177551384135235774977315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38903401845513647699969753 29177551384135235774977315)
      ·
        refine ⟨43766327076202853662465973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29177551384135235774977315 43766327076202853662465973)
        ·
          refine ⟨4103093163394017530856185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43766327076202853662465973 4103093163394017530856185)
          ·
            refine ⟨3077319872545513148142139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4103093163394017530856185 3077319872545513148142139)
            ·
              refine ⟨4615979808818269722213209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3077319872545513148142139 4615979808818269722213209)
              ·
                refine ⟨3461984856613702291659907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4615979808818269722213209 3461984856613702291659907)
                ·
                  refine ⟨5192977284920553437489861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461984856613702291659907 5192977284920553437489861)
                  ·
                    refine ⟨973683240922603769529349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5192977284920553437489861 973683240922603769529349)
                    ·
                      rfl

theorem cell22_2844362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_2844362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844362 prefixEnd_2844362 := by exact prefixLift 2844362
  have htrace : WordTrace (prefixWord ++ tailWord_2844362) baseStart_2844362 baseEnd_2844362 := by
    simpa [prefixWord, tailWord_2844362, baseEnd_2844362] using wordTrace_append hprefix tailTrace_2844362
  have hstable : (prefixWord ++ tailWord_2844362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844362).length < 2 ^ (prefixWord ++ tailWord_2844362).sum := by decide
  have hdescent : baseEnd_2844362 < baseStart_2844362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844392 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 2, 3]
def baseStart_2844392 : Nat := 118140960795 + 2844392 * 2 ^ 59
def prefixEnd_2844392 : Nat := 4983230072969 + 3 ^ 40 * 2844392 * 2
def baseEnd_2844392 : Nat := 973693510535693691279257

theorem tailTrace_2844392 : CollatzResearch.WordTrace tailWord_2844392 prefixEnd_2844392 973693510535693691279257 := by
  unfold tailWord_2844392
  simp only [CollatzResearch.WordTrace]
  refine ⟨51871749555630521161755715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69162332740840694882340953 51871749555630521161755715)
  ·
    refine ⟨77807624333445781742633573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51871749555630521161755715 77807624333445781742633573)
    ·
      refine ⟨14588929562521084076743795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77807624333445781742633573 14588929562521084076743795)
      ·
        refine ⟨21883394343781626115115693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14588929562521084076743795 21883394343781626115115693)
        ·
          refine ⟨8206272878918109793168385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21883394343781626115115693 8206272878918109793168385)
          ·
            refine ⟨6154704659188582344876289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8206272878918109793168385 6154704659188582344876289)
            ·
              refine ⟨4616028494391436758657217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6154704659188582344876289 4616028494391436758657217)
              ·
                refine ⟨3462021370793577568992913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4616028494391436758657217 3462021370793577568992913)
                ·
                  refine ⟨2596516028095183176744685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3462021370793577568992913 2596516028095183176744685)
                  ·
                    refine ⟨973693510535693691279257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596516028095183176744685 973693510535693691279257)
                    ·
                      rfl

theorem cell22_2844392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_2844392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844392 prefixEnd_2844392 := by exact prefixLift 2844392
  have htrace : WordTrace (prefixWord ++ tailWord_2844392) baseStart_2844392 baseEnd_2844392 := by
    simpa [prefixWord, tailWord_2844392, baseEnd_2844392] using wordTrace_append hprefix tailTrace_2844392
  have hstable : (prefixWord ++ tailWord_2844392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844392).length < 2 ^ (prefixWord ++ tailWord_2844392).sum := by decide
  have hdescent : baseEnd_2844392 < baseStart_2844392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844420 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_2844420 : Nat := 118140960795 + 2844420 * 2 ^ 59
def prefixEnd_2844420 : Nat := 4983230072969 + 3 ^ 40 * 2844420 * 2
def baseEnd_2844420 : Nat := 973703095507910951579171

theorem tailTrace_2844420 : CollatzResearch.WordTrace tailWord_2844420 prefixEnd_2844420 973703095507910951579171 := by
  unfold tailWord_2844420
  simp only [CollatzResearch.WordTrace]
  refine ⟨51872260177579801552765357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69163013570106402070353809 51872260177579801552765357)
  ·
    refine ⟨19452097566592425582287009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51872260177579801552765357 19452097566592425582287009)
    ·
      refine ⟨14589073174944319186715257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19452097566592425582287009 14589073174944319186715257)
      ·
        refine ⟨10941804881208239390036443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14589073174944319186715257 10941804881208239390036443)
        ·
          refine ⟨16412707321812359085054665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10941804881208239390036443 16412707321812359085054665)
          ·
            refine ⟨12309530491359269313790999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16412707321812359085054665 12309530491359269313790999)
            ·
              refine ⟨18464295737038903970686499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12309530491359269313790999 18464295737038903970686499)
              ·
                refine ⟨27696443605558355956029749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18464295737038903970686499 27696443605558355956029749)
                ·
                  refine ⟨2596541588021095870877789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27696443605558355956029749 2596541588021095870877789)
                  ·
                    refine ⟨973703095507910951579171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596541588021095870877789 973703095507910951579171)
                    ·
                      rfl

theorem cell22_2844420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_2844420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844420 prefixEnd_2844420 := by exact prefixLift 2844420
  have htrace : WordTrace (prefixWord ++ tailWord_2844420) baseStart_2844420 baseEnd_2844420 := by
    simpa [prefixWord, tailWord_2844420, baseEnd_2844420] using wordTrace_append hprefix tailTrace_2844420
  have hstable : (prefixWord ++ tailWord_2844420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844420).length < 2 ^ (prefixWord ++ tailWord_2844420).sum := by decide
  have hdescent : baseEnd_2844420 < baseStart_2844420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844437 : List Nat := [1, 3, 2, 1, 2, 3, 1, 5, 1, 3]
def baseStart_2844437 : Nat := 118140960795 + 2844437 * 2 ^ 59
def prefixEnd_2844437 : Nat := 4983230072969 + 3 ^ 40 * 2844437 * 2
def baseEnd_2844437 : Nat := 973708914955328573904119

theorem tailTrace_2844437 : CollatzResearch.WordTrace tailWord_2844437 prefixEnd_2844437 973708914955328573904119 := by
  unfold tailWord_2844437
  simp only [CollatzResearch.WordTrace]
  refine ⟨103745140396098015008899565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69163426930732010005933043 103745140396098015008899565)
  ·
    refine ⟨38904427648536755628337337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103745140396098015008899565 38904427648536755628337337)
    ·
      refine ⟨29178320736402566721253003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38904427648536755628337337 29178320736402566721253003)
      ·
        refine ⟨43767481104603850081879505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29178320736402566721253003 43767481104603850081879505)
        ·
          refine ⟨32825610828452887561409629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43767481104603850081879505 32825610828452887561409629)
          ·
            refine ⟨12309604060669832835528611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32825610828452887561409629 12309604060669832835528611)
            ·
              refine ⟨18464406091004749253292917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12309604060669832835528611 18464406091004749253292917)
              ·
                refine ⟨1731038071031695242496211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18464406091004749253292917 1731038071031695242496211)
                ·
                  refine ⟨2596557106547542863744317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731038071031695242496211 2596557106547542863744317)
                  ·
                    refine ⟨973708914955328573904119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596557106547542863744317 973708914955328573904119)
                    ·
                      rfl

theorem cell22_2844437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_2844437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844437 prefixEnd_2844437 := by exact prefixLift 2844437
  have htrace : WordTrace (prefixWord ++ tailWord_2844437) baseStart_2844437 baseEnd_2844437 := by
    simpa [prefixWord, tailWord_2844437, baseEnd_2844437] using wordTrace_append hprefix tailTrace_2844437
  have hstable : (prefixWord ++ tailWord_2844437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844437).length < 2 ^ (prefixWord ++ tailWord_2844437).sum := by decide
  have hdescent : baseEnd_2844437 < baseStart_2844437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844448 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_2844448 : Nat := 118140960795 + 2844448 * 2 ^ 59
def prefixEnd_2844448 : Nat := 4983230072969 + 3 ^ 40 * 2844448 * 2
def baseEnd_2844448 : Nat := 973712680480128211879085

theorem tailTrace_2844448 : CollatzResearch.WordTrace tailWord_2844448 prefixEnd_2844448 973712680480128211879085 := by
  unfold tailWord_2844448
  simp only [CollatzResearch.WordTrace]
  refine ⟨51872770799529081943774999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69163694399372109258366665 51872770799529081943774999)
  ·
    refine ⟨77809156199293622915662499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51872770799529081943774999 77809156199293622915662499)
    ·
      refine ⟨116713734298940434373493749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77809156199293622915662499 116713734298940434373493749)
      ·
        refine ⟨10941912590525665722515039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116713734298940434373493749 10941912590525665722515039)
        ·
          refine ⟨16412868885788498583772559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10941912590525665722515039 16412868885788498583772559)
          ·
            refine ⟨24619303328682747875658839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16412868885788498583772559 24619303328682747875658839)
            ·
              refine ⟨36928954993024121813488259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24619303328682747875658839 36928954993024121813488259)
              ·
                refine ⟨55393432489536182720232389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36928954993024121813488259 55393432489536182720232389)
                ·
                  refine ⟨10386268591788034260043573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55393432489536182720232389 10386268591788034260043573)
                  ·
                    refine ⟨973712680480128211879085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10386268591788034260043573 973712680480128211879085)
                    ·
                      rfl

theorem cell22_2844448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_2844448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844448 prefixEnd_2844448 := by exact prefixLift 2844448
  have htrace : WordTrace (prefixWord ++ tailWord_2844448) baseStart_2844448 baseEnd_2844448 := by
    simpa [prefixWord, tailWord_2844448, baseEnd_2844448] using wordTrace_append hprefix tailTrace_2844448
  have hstable : (prefixWord ++ tailWord_2844448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844448).length < 2 ^ (prefixWord ++ tailWord_2844448).sum := by decide
  have hdescent : baseEnd_2844448 < baseStart_2844448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844467 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 5]
def baseStart_2844467 : Nat := 118140960795 + 2844467 * 2 ^ 59
def prefixEnd_2844467 : Nat := 4983230072969 + 3 ^ 40 * 2844467 * 2
def baseEnd_2844467 : Nat := 324573061522806165218009

theorem tailTrace_2844467 : CollatzResearch.WordTrace tailWord_2844467 prefixEnd_2844467 324573061522806165218009 := by
  unfold tailWord_2844467
  simp only [CollatzResearch.WordTrace]
  refine ⟨103746234585989330132491655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69164156390659553421661103 103746234585989330132491655)
  ·
    refine ⟨155619351878983995198737483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103746234585989330132491655 155619351878983995198737483)
    ·
      refine ⟨233429027818475992798106225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155619351878983995198737483 233429027818475992798106225)
      ·
        refine ⟨175071770863856994598579669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233429027818475992798106225 175071770863856994598579669)
        ·
          refine ⟨4103244629621648310904211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 175071770863856994598579669 4103244629621648310904211)
          ·
            refine ⟨6154866944432472466356317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103244629621648310904211 6154866944432472466356317)
            ·
              refine ⟨2308075104162177174883619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6154866944432472466356317 2308075104162177174883619)
              ·
                refine ⟨3462112656243265762325429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308075104162177174883619 3462112656243265762325429)
                ·
                  refine ⟨324573061522806165218009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3462112656243265762325429 324573061522806165218009)
                  ·
                    rfl

theorem cell22_2844467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 5].length) (baseStart_2844467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844467 prefixEnd_2844467 := by exact prefixLift 2844467
  have htrace : WordTrace (prefixWord ++ tailWord_2844467) baseStart_2844467 baseEnd_2844467 := by
    simpa [prefixWord, tailWord_2844467, baseEnd_2844467] using wordTrace_append hprefix tailTrace_2844467
  have hstable : (prefixWord ++ tailWord_2844467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844467).length < 2 ^ (prefixWord ++ tailWord_2844467).sum := by decide
  have hdescent : baseEnd_2844467 < baseStart_2844467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844538 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_2844538 : Nat := 118140960795 + 2844538 * 2 ^ 59
def prefixEnd_2844538 : Nat := 4983230072969 + 3 ^ 40 * 2844538 * 2
def baseEnd_2844538 : Nat := 973743489319397977128809

theorem tailTrace_2844538 : CollatzResearch.WordTrace tailWord_2844538 prefixEnd_2844538 973743489319397977128809 := by
  unfold tailWord_2844538
  simp only [CollatzResearch.WordTrace]
  refine ⟨25937206042183027314581567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69165882779154739505550845 25937206042183027314581567)
  ·
    refine ⟨38905809063274540971872351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25937206042183027314581567 38905809063274540971872351)
    ·
      refine ⟨58358713594911811457808527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38905809063274540971872351 58358713594911811457808527)
      ·
        refine ⟨87538070392367717186712791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58358713594911811457808527 87538070392367717186712791)
        ·
          refine ⟨131307105588551575780069187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87538070392367717186712791 131307105588551575780069187)
          ·
            refine ⟨196960658382827363670103781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131307105588551575780069187 196960658382827363670103781)
            ·
              refine ⟨36930123446780130688144459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196960658382827363670103781 36930123446780130688144459)
              ·
                refine ⟨55395185170170196032216689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36930123446780130688144459 55395185170170196032216689)
                ·
                  refine ⟨41546388877627647024162517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55395185170170196032216689 41546388877627647024162517)
                  ·
                    refine ⟨973743489319397977128809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41546388877627647024162517 973743489319397977128809)
                    ·
                      rfl

theorem cell22_2844538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_2844538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844538 prefixEnd_2844538 := by exact prefixLift 2844538
  have htrace : WordTrace (prefixWord ++ tailWord_2844538) baseStart_2844538 baseEnd_2844538 := by
    simpa [prefixWord, tailWord_2844538, baseEnd_2844538] using wordTrace_append hprefix tailTrace_2844538
  have hstable : (prefixWord ++ tailWord_2844538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844538).length < 2 ^ (prefixWord ++ tailWord_2844538).sum := by decide
  have hdescent : baseEnd_2844538 < baseStart_2844538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844570 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_2844570 : Nat := 118140960795 + 2844570 * 2 ^ 59
def prefixEnd_2844570 : Nat := 4983230072969 + 3 ^ 40 * 2844570 * 2
def baseEnd_2844570 : Nat := 973754443573360560328711

theorem tailTrace_2844570 : CollatzResearch.WordTrace tailWord_2844570 prefixEnd_2844570 973754443573360560328711 := by
  unfold tailWord_2844570
  simp only [CollatzResearch.WordTrace]
  refine ⟨25937497826154044680872791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69166660869744119148994109 25937497826154044680872791)
  ·
    refine ⟨38906246739231067021309187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25937497826154044680872791 38906246739231067021309187)
    ·
      refine ⟨58359370108846600531963781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38906246739231067021309187 58359370108846600531963781)
      ·
        refine ⟨10942381895408737599743209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58359370108846600531963781 10942381895408737599743209)
        ·
          refine ⟨8206786421556553199807407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10942381895408737599743209 8206786421556553199807407)
          ·
            refine ⟨12310179632334829799711111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8206786421556553199807407 12310179632334829799711111)
            ·
              refine ⟨18465269448502244699566667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12310179632334829799711111 18465269448502244699566667)
              ·
                refine ⟨27697904172753367049350001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18465269448502244699566667 27697904172753367049350001)
                ·
                  refine ⟨20773428129565025287012501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27697904172753367049350001 20773428129565025287012501)
                  ·
                    refine ⟨973754443573360560328711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20773428129565025287012501 973754443573360560328711)
                    ·
                      rfl

theorem cell22_2844570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_2844570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844570 prefixEnd_2844570 := by exact prefixLift 2844570
  have htrace : WordTrace (prefixWord ++ tailWord_2844570) baseStart_2844570 baseEnd_2844570 := by
    simpa [prefixWord, tailWord_2844570, baseEnd_2844570] using wordTrace_append hprefix tailTrace_2844570
  have hstable : (prefixWord ++ tailWord_2844570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844570).length < 2 ^ (prefixWord ++ tailWord_2844570).sum := by decide
  have hdescent : baseEnd_2844570 < baseStart_2844570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844606 : List Nat := [4, 2, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_2844606 : Nat := 118140960795 + 2844606 * 2 ^ 59
def prefixEnd_2844606 : Nat := 4983230072969 + 3 ^ 40 * 2844606 * 2
def baseEnd_2844606 : Nat := 973766767109068466428601

theorem tailTrace_2844606 : CollatzResearch.WordTrace tailWord_2844606 prefixEnd_2844606 973766767109068466428601 := by
  unfold tailWord_2844606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12968913041560719608975209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69167536221657171247867781 12968913041560719608975209)
  ·
    refine ⟨9726684781170539706731407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12968913041560719608975209 9726684781170539706731407)
    ·
      refine ⟨14590027171755809560097111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9726684781170539706731407 14590027171755809560097111)
      ·
        refine ⟨21885040757633714340145667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14590027171755809560097111 21885040757633714340145667)
        ·
          refine ⟨32827561136450571510218501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21885040757633714340145667 32827561136450571510218501)
          ·
            refine ⟨6155167713084482158165969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32827561136450571510218501 6155167713084482158165969)
            ·
              refine ⟨4616375784813361618624477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6155167713084482158165969 4616375784813361618624477)
              ·
                refine ⟨1731140919305010606984179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4616375784813361618624477 1731140919305010606984179)
                ·
                  refine ⟨2596711378957515910476269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731140919305010606984179 2596711378957515910476269)
                  ·
                    refine ⟨973766767109068466428601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596711378957515910476269 973766767109068466428601)
                    ·
                      rfl

theorem cell22_2844606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_2844606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844606 prefixEnd_2844606 := by exact prefixLift 2844606
  have htrace : WordTrace (prefixWord ++ tailWord_2844606) baseStart_2844606 baseEnd_2844606 := by
    simpa [prefixWord, tailWord_2844606, baseEnd_2844606] using wordTrace_append hprefix tailTrace_2844606
  have hstable : (prefixWord ++ tailWord_2844606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844606).length < 2 ^ (prefixWord ++ tailWord_2844606).sum := by decide
  have hdescent : baseEnd_2844606 < baseStart_2844606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844677 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_2844677 : Nat := 118140960795 + 2844677 * 2 ^ 59
def prefixEnd_2844677 : Nat := 4983230072969 + 3 ^ 40 * 2844677 * 2
def baseEnd_2844677 : Nat := 973791071860047947903383

theorem tailTrace_2844677 : CollatzResearch.WordTrace tailWord_2844677 prefixEnd_2844677 973791071860047947903383 := by
  unfold tailWord_2844677
  simp only [CollatzResearch.WordTrace]
  refine ⟨103753893915228535997636285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69169262610152357331757523 103753893915228535997636285)
  ·
    refine ⟨38907710218210700999113607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103753893915228535997636285 38907710218210700999113607)
    ·
      refine ⟨58361565327316051498670411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38907710218210700999113607 58361565327316051498670411)
      ·
        refine ⟨87542347990974077248005617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58361565327316051498670411 87542347990974077248005617)
        ·
          refine ⟨65656760993230557936004213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87542347990974077248005617 65656760993230557936004213)
          ·
            refine ⟨6155321343115364806500395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65656760993230557936004213 6155321343115364806500395)
            ·
              refine ⟨9232982014673047209750593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155321343115364806500395 9232982014673047209750593)
              ·
                refine ⟨6924736511004785407312945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9232982014673047209750593 6924736511004785407312945)
                ·
                  refine ⟨5193552383253589055484709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6924736511004785407312945 5193552383253589055484709)
                  ·
                    refine ⟨973791071860047947903383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5193552383253589055484709 973791071860047947903383)
                    ·
                      rfl

theorem cell22_2844677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_2844677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844677 prefixEnd_2844677 := by exact prefixLift 2844677
  have htrace : WordTrace (prefixWord ++ tailWord_2844677) baseStart_2844677 baseEnd_2844677 := by
    simpa [prefixWord, tailWord_2844677, baseEnd_2844677] using wordTrace_append hprefix tailTrace_2844677
  have hstable : (prefixWord ++ tailWord_2844677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844677).length < 2 ^ (prefixWord ++ tailWord_2844677).sum := by decide
  have hdescent : baseEnd_2844677 < baseStart_2844677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844707 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 5, 3]
def baseStart_2844707 : Nat := 118140960795 + 2844707 * 2 ^ 59
def prefixEnd_2844707 : Nat := 4983230072969 + 3 ^ 40 * 2844707 * 2
def baseEnd_2844707 : Nat := 973801341473137869653291

theorem tailTrace_2844707 : CollatzResearch.WordTrace tailWord_2844707 prefixEnd_2844707 973801341473137869653291 := by
  unfold tailWord_2844707
  simp only [CollatzResearch.WordTrace]
  refine ⟨103754988105119851121228375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69169992070079900747485583 103754988105119851121228375)
  ·
    refine ⟨155632482157679776681842563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103754988105119851121228375 155632482157679776681842563)
    ·
      refine ⟨233448723236519665022763845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155632482157679776681842563 233448723236519665022763845)
      ·
        refine ⟨43771635606847437191768221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233448723236519665022763845 43771635606847437191768221)
        ·
          refine ⟨16414363352567788946913083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43771635606847437191768221 16414363352567788946913083)
          ·
            refine ⟨24621545028851683420369625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16414363352567788946913083 24621545028851683420369625)
            ·
              refine ⟨18466158771638762565277219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24621545028851683420369625 18466158771638762565277219)
              ·
                refine ⟨27699238157458143847915829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18466158771638762565277219 27699238157458143847915829)
                ·
                  refine ⟨2596803577261700985742109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27699238157458143847915829 2596803577261700985742109)
                  ·
                    refine ⟨973801341473137869653291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596803577261700985742109 973801341473137869653291)
                    ·
                      rfl

theorem cell22_2844707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 3].length) (baseStart_2844707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844707 prefixEnd_2844707 := by exact prefixLift 2844707
  have htrace : WordTrace (prefixWord ++ tailWord_2844707) baseStart_2844707 baseEnd_2844707 := by
    simpa [prefixWord, tailWord_2844707, baseEnd_2844707] using wordTrace_append hprefix tailTrace_2844707
  have hstable : (prefixWord ++ tailWord_2844707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844707).length < 2 ^ (prefixWord ++ tailWord_2844707).sum := by decide
  have hdescent : baseEnd_2844707 < baseStart_2844707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844711 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2844711 : Nat := 118140960795 + 2844711 * 2 ^ 59
def prefixEnd_2844711 : Nat := 4983230072969 + 3 ^ 40 * 2844711 * 2
def baseEnd_2844711 : Nat := 973802710754883192553279

theorem tailTrace_2844711 : CollatzResearch.WordTrace tailWord_2844711 prefixEnd_2844711 973802710754883192553279 := by
  unfold tailWord_2844711
  simp only [CollatzResearch.WordTrace]
  refine ⟨103755133997105359804373987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69170089331403573202915991 103755133997105359804373987)
  ·
    refine ⟨155632700995658039706560981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103755133997105359804373987 155632700995658039706560981)
    ·
      refine ⟨3647641429585735305622523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 155632700995658039706560981 3647641429585735305622523)
      ·
        refine ⟨5471462144378602958433785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647641429585735305622523 5471462144378602958433785)
        ·
          refine ⟨4103596608283952218825339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5471462144378602958433785 4103596608283952218825339)
          ·
            refine ⟨6155394912425928328238009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103596608283952218825339 6155394912425928328238009)
            ·
              refine ⟨4616546184319446246178507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6155394912425928328238009 4616546184319446246178507)
              ·
                refine ⟨6924819276479169369267761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4616546184319446246178507 6924819276479169369267761)
                ·
                  refine ⟨5193614457359377026950821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6924819276479169369267761 5193614457359377026950821)
                  ·
                    refine ⟨973802710754883192553279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5193614457359377026950821 973802710754883192553279)
                    ·
                      rfl

theorem cell22_2844711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2844711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844711 prefixEnd_2844711 := by exact prefixLift 2844711
  have htrace : WordTrace (prefixWord ++ tailWord_2844711) baseStart_2844711 baseEnd_2844711 := by
    simpa [prefixWord, tailWord_2844711, baseEnd_2844711] using wordTrace_append hprefix tailTrace_2844711
  have hstable : (prefixWord ++ tailWord_2844711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844711).length < 2 ^ (prefixWord ++ tailWord_2844711).sum := by decide
  have hdescent : baseEnd_2844711 < baseStart_2844711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844758 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2844758 : Nat := 118140960795 + 2844758 * 2 ^ 59
def prefixEnd_2844758 : Nat := 4983230072969 + 3 ^ 40 * 2844758 * 2
def baseEnd_2844758 : Nat := 973818799815390736628135

theorem tailTrace_2844758 : CollatzResearch.WordTrace tailWord_2844758 prefixEnd_2844758 973818799815390736628135 := by
  unfold tailWord_2844758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6484803014245942926958433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69171232151956724554223285 6484803014245942926958433)
  ·
    refine ⟨4863602260684457195218825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6484803014245942926958433 4863602260684457195218825)
    ·
      refine ⟨3647701695513342896414119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4863602260684457195218825 3647701695513342896414119)
      ·
        refine ⟨5471552543270014344621179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647701695513342896414119 5471552543270014344621179)
        ·
          refine ⟨8207328814905021516931769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5471552543270014344621179 8207328814905021516931769)
          ·
            refine ⟨6155496611178766137698827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8207328814905021516931769 6155496611178766137698827)
            ·
              refine ⟨9233244916768149206548241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155496611178766137698827 9233244916768149206548241)
              ·
                refine ⟨6924933687576111904911181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9233244916768149206548241 6924933687576111904911181)
                ·
                  refine ⟨2596850132841041964341693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6924933687576111904911181 2596850132841041964341693)
                  ·
                    refine ⟨973818799815390736628135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2596850132841041964341693 973818799815390736628135)
                    ·
                      rfl

theorem cell22_2844758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2844758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844758 prefixEnd_2844758 := by exact prefixLift 2844758
  have htrace : WordTrace (prefixWord ++ tailWord_2844758) baseStart_2844758 baseEnd_2844758 := by
    simpa [prefixWord, tailWord_2844758, baseEnd_2844758] using wordTrace_append hprefix tailTrace_2844758
  have hstable : (prefixWord ++ tailWord_2844758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844758).length < 2 ^ (prefixWord ++ tailWord_2844758).sum := by decide
  have hdescent : baseEnd_2844758 < baseStart_2844758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844782 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_2844782 : Nat := 118140960795 + 2844782 * 2 ^ 59
def prefixEnd_2844782 : Nat := 4983230072969 + 3 ^ 40 * 2844782 * 2
def baseEnd_2844782 : Nat := 324609005168620891342687

theorem tailTrace_2844782 : CollatzResearch.WordTrace tailWord_2844782 prefixEnd_2844782 324609005168620891342687 := by
  unfold tailWord_2844782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12969715447481017366276075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69171815719898759286805733 12969715447481017366276075)
  ·
    refine ⟨19454573171221526049414113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12969715447481017366276075 19454573171221526049414113)
    ·
      refine ⟨14590929878416144537060585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19454573171221526049414113 14590929878416144537060585)
      ·
        refine ⟨10943197408812108402795439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14590929878416144537060585 10943197408812108402795439)
        ·
          refine ⟨16414796113218162604193159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10943197408812108402795439 16414796113218162604193159)
          ·
            refine ⟨24622194169827243906289739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16414796113218162604193159 24622194169827243906289739)
            ·
              refine ⟨36933291254740865859434609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24622194169827243906289739 36933291254740865859434609)
              ·
                refine ⟨27699968441055649394575957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36933291254740865859434609 27699968441055649394575957)
                ·
                  refine ⟨324609005168620891342687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27699968441055649394575957 324609005168620891342687)
                  ·
                    rfl

theorem cell22_2844782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_2844782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844782 prefixEnd_2844782 := by exact prefixLift 2844782
  have htrace : WordTrace (prefixWord ++ tailWord_2844782) baseStart_2844782 baseEnd_2844782 := by
    simpa [prefixWord, tailWord_2844782, baseEnd_2844782] using wordTrace_append hprefix tailTrace_2844782
  have hstable : (prefixWord ++ tailWord_2844782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844782).length < 2 ^ (prefixWord ++ tailWord_2844782).sum := by decide
  have hdescent : baseEnd_2844782 < baseStart_2844782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844784 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_2844784 : Nat := 118140960795 + 2844784 * 2 ^ 59
def prefixEnd_2844784 : Nat := 4983230072969 + 3 ^ 40 * 2844784 * 2
def baseEnd_2844784 : Nat := 973827700146735335478055

theorem tailTrace_2844784 : CollatzResearch.WordTrace tailWord_2844784 prefixEnd_2844784 973827700146735335478055 := by
  unfold tailWord_2844784
  simp only [CollatzResearch.WordTrace]
  refine ⟨51878898262920446635890703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69171864350560595514520937 51878898262920446635890703)
  ·
    refine ⟨77818347394380669953836055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51878898262920446635890703 77818347394380669953836055)
    ·
      refine ⟨116727521091571004930754083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77818347394380669953836055 116727521091571004930754083)
      ·
        refine ⟨175091281637356507396131125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116727521091571004930754083 175091281637356507396131125)
        ·
          refine ⟨16414807653502172568387293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175091281637356507396131125 16414807653502172568387293)
          ·
            refine ⟨6155552870063314713145235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16414807653502172568387293 6155552870063314713145235)
            ·
              refine ⟨9233329305094972069717853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155552870063314713145235 9233329305094972069717853)
              ·
                refine ⟨3462498489410614526144195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9233329305094972069717853 3462498489410614526144195)
                ·
                  refine ⟨5193747734115921789216293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3462498489410614526144195 5193747734115921789216293)
                  ·
                    refine ⟨973827700146735335478055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5193747734115921789216293 973827700146735335478055)
                    ·
                      rfl

theorem cell22_2844784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_2844784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844784 prefixEnd_2844784 := by exact prefixLift 2844784
  have htrace : WordTrace (prefixWord ++ tailWord_2844784) baseStart_2844784 baseEnd_2844784 := by
    simpa [prefixWord, tailWord_2844784, baseEnd_2844784] using wordTrace_append hprefix tailTrace_2844784
  have hstable : (prefixWord ++ tailWord_2844784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844784).length < 2 ^ (prefixWord ++ tailWord_2844784).sum := by decide
  have hdescent : baseEnd_2844784 < baseStart_2844784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844857 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_2844857 : Nat := 118140960795 + 2844857 * 2 ^ 59
def prefixEnd_2844857 : Nat := 4983230072969 + 3 ^ 40 * 2844857 * 2
def baseEnd_2844857 : Nat := 973852689538587478402831

theorem tailTrace_2844857 : CollatzResearch.WordTrace tailWord_2844857 prefixEnd_2844857 973852689538587478402831 := by
  unfold tailWord_2844857
  simp only [CollatzResearch.WordTrace]
  refine ⟨103760459054576426739188825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69173639369717617826125883 103760459054576426739188825)
  ·
    refine ⟨77820344290932320054391619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103760459054576426739188825 77820344290932320054391619)
    ·
      refine ⟨116730516436398480081587429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77820344290932320054391619 116730516436398480081587429)
      ·
        refine ⟨21886971831824715015297643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116730516436398480081587429 21886971831824715015297643)
        ·
          refine ⟨32830457747737072522946465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21886971831824715015297643 32830457747737072522946465)
          ·
            refine ⟨24622843310802804392209849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32830457747737072522946465 24622843310802804392209849)
            ·
              refine ⟨18467132483102103294157387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24622843310802804392209849 18467132483102103294157387)
              ·
                refine ⟨27700698724653154941236081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18467132483102103294157387 27700698724653154941236081)
                ·
                  refine ⟨20775524043489866205927061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27700698724653154941236081 20775524043489866205927061)
                  ·
                    refine ⟨973852689538587478402831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20775524043489866205927061 973852689538587478402831)
                    ·
                      rfl

theorem cell22_2844857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_2844857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844857 prefixEnd_2844857 := by exact prefixLift 2844857
  have htrace : WordTrace (prefixWord ++ tailWord_2844857) baseStart_2844857 baseEnd_2844857 := by
    simpa [prefixWord, tailWord_2844857, baseEnd_2844857] using wordTrace_append hprefix tailTrace_2844857
  have hstable : (prefixWord ++ tailWord_2844857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844857).length < 2 ^ (prefixWord ++ tailWord_2844857).sum := by decide
  have hdescent : baseEnd_2844857 < baseStart_2844857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844887 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 4, 5]
def baseStart_2844887 : Nat := 118140960795 + 2844887 * 2 ^ 59
def prefixEnd_2844887 : Nat := 4983230072969 + 3 ^ 40 * 2844887 * 2
def baseEnd_2844887 : Nat := 973862959151677400152739

theorem tailTrace_2844887 : CollatzResearch.WordTrace tailWord_2844887 prefixEnd_2844887 973862959151677400152739 := by
  unfold tailWord_2844887
  simp only [CollatzResearch.WordTrace]
  refine ⟨103761553244467741862780915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69174368829645161241853943 103761553244467741862780915)
  ·
    refine ⟨155642329866701612794171373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103761553244467741862780915 155642329866701612794171373)
    ·
      refine ⟨58365873700013104797814265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155642329866701612794171373 58365873700013104797814265)
      ·
        refine ⟨43774405275009828598360699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58365873700013104797814265 43774405275009828598360699)
        ·
          refine ⟨65661607912514742897541049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43774405275009828598360699 65661607912514742897541049)
          ·
            refine ⟨49246205934386057173155787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65661607912514742897541049 49246205934386057173155787)
            ·
              refine ⟨73869308901579085759733681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49246205934386057173155787 73869308901579085759733681)
              ·
                refine ⟨55401981676184314319800261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73869308901579085759733681 55401981676184314319800261)
                ·
                  refine ⟨10387871564284558934962549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55401981676184314319800261 10387871564284558934962549)
                  ·
                    refine ⟨973862959151677400152739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10387871564284558934962549 973862959151677400152739)
                    ·
                      rfl

theorem cell22_2844887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_2844887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844887 prefixEnd_2844887 := by exact prefixLift 2844887
  have htrace : WordTrace (prefixWord ++ tailWord_2844887) baseStart_2844887 baseEnd_2844887 := by
    simpa [prefixWord, tailWord_2844887, baseEnd_2844887] using wordTrace_append hprefix tailTrace_2844887
  have hstable : (prefixWord ++ tailWord_2844887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844887).length < 2 ^ (prefixWord ++ tailWord_2844887).sum := by decide
  have hdescent : baseEnd_2844887 < baseStart_2844887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844949 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2844949 : Nat := 118140960795 + 2844949 * 2 ^ 59
def prefixEnd_2844949 : Nat := 4983230072969 + 3 ^ 40 * 2844949 * 2
def baseEnd_2844949 : Nat := 973884183018729905102549

theorem tailTrace_2844949 : CollatzResearch.WordTrace tailWord_2844949 prefixEnd_2844949 973884183018729905102549 := by
  unfold tailWord_2844949
  simp only [CollatzResearch.WordTrace]
  refine ⟨103763814570243126451537901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69175876380162084301025267 103763814570243126451537901)
  ·
    refine ⟨38911430463841172419326713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103763814570243126451537901 38911430463841172419326713)
    ·
      refine ⟨29183572847880879314495035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38911430463841172419326713 29183572847880879314495035)
      ·
        refine ⟨43775359271821318971742553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29183572847880879314495035 43775359271821318971742553)
        ·
          refine ⟨32831519453865989228806915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43775359271821318971742553 32831519453865989228806915)
          ·
            refine ⟨49247279180798983843210373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32831519453865989228806915 49247279180798983843210373)
            ·
              refine ⟨9233864846399809470601945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49247279180798983843210373 9233864846399809470601945)
              ·
                refine ⟨6925398634799857102951459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9233864846399809470601945 6925398634799857102951459)
                ·
                  refine ⟨10388097952199785654427189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6925398634799857102951459 10388097952199785654427189)
                  ·
                    refine ⟨973884183018729905102549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10388097952199785654427189 973884183018729905102549)
                    ·
                      rfl

theorem cell22_2844949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2844949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844949 prefixEnd_2844949 := by exact prefixLift 2844949
  have htrace : WordTrace (prefixWord ++ tailWord_2844949) baseStart_2844949 baseEnd_2844949 := by
    simpa [prefixWord, tailWord_2844949, baseEnd_2844949] using wordTrace_append hprefix tailTrace_2844949
  have hstable : (prefixWord ++ tailWord_2844949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844949).length < 2 ^ (prefixWord ++ tailWord_2844949).sum := by decide
  have hdescent : baseEnd_2844949 < baseStart_2844949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844951 : List Nat := [1, 1, 3, 4, 1, 2, 1, 5, 4]
def baseStart_2844951 : Nat := 118140960795 + 2844951 * 2 ^ 59
def prefixEnd_2844951 : Nat := 4983230072969 + 3 ^ 40 * 2844951 * 2
def baseEnd_2844951 : Nat := 324628289219867522184181

theorem tailTrace_2844951 : CollatzResearch.WordTrace tailWord_2844951 prefixEnd_2844951 324628289219867522184181 := by
  unfold tailWord_2844951
  simp only [CollatzResearch.WordTrace]
  refine ⟨103763887516235880793110707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69175925010823920528740471 103763887516235880793110707)
  ·
    refine ⟨155645831274353821189666061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103763887516235880793110707 155645831274353821189666061)
    ·
      refine ⟨58367186727882682946124773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155645831274353821189666061 58367186727882682946124773)
      ·
        refine ⟨10943847511478003052398395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58367186727882682946124773 10943847511478003052398395)
        ·
          refine ⟨16415771267217004578597593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10943847511478003052398395 16415771267217004578597593)
          ·
            refine ⟨12311828450412753433948195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16415771267217004578597593 12311828450412753433948195)
            ·
              refine ⟨18467742675619130150922293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12311828450412753433948195 18467742675619130150922293)
              ·
                refine ⟨1731350875839293451648965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18467742675619130150922293 1731350875839293451648965)
                ·
                  refine ⟨324628289219867522184181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1731350875839293451648965 324628289219867522184181)
                  ·
                    rfl

theorem cell22_2844951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 4].length) (baseStart_2844951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2844951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2844951 prefixEnd_2844951 := by exact prefixLift 2844951
  have htrace : WordTrace (prefixWord ++ tailWord_2844951) baseStart_2844951 baseEnd_2844951 := by
    simpa [prefixWord, tailWord_2844951, baseEnd_2844951] using wordTrace_append hprefix tailTrace_2844951
  have hstable : (prefixWord ++ tailWord_2844951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844951).length < 2 ^ (prefixWord ++ tailWord_2844951).sum := by decide
  have hdescent : baseEnd_2844951 < baseStart_2844951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845114 : List Nat := [3, 1, 1, 1, 2, 1, 1, 12]
def baseStart_2845114 : Nat := 118140960795 + 2845114 * 2 ^ 59
def prefixEnd_2845114 : Nat := 4983230072969 + 3 ^ 40 * 2845114 * 2
def baseEnd_2845114 : Nat := 108215629543413830525227

theorem tailTrace_2845114 : CollatzResearch.WordTrace tailWord_2845114 prefixEnd_2845114 108215629543413830525227 := by
  unfold tailWord_2845114
  simp only [CollatzResearch.WordTrace]
  refine ⟨25942458153661339907823599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69179888409763573087529597 25942458153661339907823599)
  ·
    refine ⟨38913687230492009861735399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25942458153661339907823599 38913687230492009861735399)
    ·
      refine ⟨58370530845738014792603099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38913687230492009861735399 58370530845738014792603099)
      ·
        refine ⟨87555796268607022188904649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58370530845738014792603099 87555796268607022188904649)
        ·
          refine ⟨65666847201455266641678487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87555796268607022188904649 65666847201455266641678487)
          ·
            refine ⟨98500270802182899962517731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65666847201455266641678487 98500270802182899962517731)
            ·
              refine ⟨147750406203274349943776597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98500270802182899962517731 147750406203274349943776597)
              ·
                refine ⟨108215629543413830525227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 147750406203274349943776597 108215629543413830525227)
                ·
                  rfl

theorem cell22_2845114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_2845114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845114 prefixEnd_2845114 := by exact prefixLift 2845114
  have htrace : WordTrace (prefixWord ++ tailWord_2845114) baseStart_2845114 baseEnd_2845114 := by
    simpa [prefixWord, tailWord_2845114, baseEnd_2845114] using wordTrace_append hprefix tailTrace_2845114
  have hstable : (prefixWord ++ tailWord_2845114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845114).length < 2 ^ (prefixWord ++ tailWord_2845114).sum := by decide
  have hdescent : baseEnd_2845114 < baseStart_2845114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845165 : List Nat := [1, 5, 1, 3, 1, 3, 2, 6]
def baseStart_2845165 : Nat := 118140960795 + 2845165 * 2 ^ 59
def prefixEnd_2845165 : Nat := 4983230072969 + 3 ^ 40 * 2845165 * 2
def baseEnd_2845165 : Nat := 108217569359219704633543

theorem tailTrace_2845165 : CollatzResearch.WordTrace tailWord_2845165 prefixEnd_2845165 108217569359219704633543 := by
  unfold tailWord_2845165
  simp only [CollatzResearch.WordTrace]
  refine ⟨103771692737460595341400949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69181128491640396894267299 103771692737460595341400949)
  ·
    refine ⟨9728596194136930813256339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103771692737460595341400949 9728596194136930813256339)
    ·
      refine ⟨14592894291205396219884509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9728596194136930813256339 14592894291205396219884509)
      ·
        refine ⟨5472335359202023582456691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14592894291205396219884509 5472335359202023582456691)
        ·
          refine ⟨8208503038803035373685037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472335359202023582456691 8208503038803035373685037)
          ·
            refine ⟨3078188639551138265131889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8208503038803035373685037 3078188639551138265131889)
            ·
              refine ⟨2308641479663353698848917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3078188639551138265131889 2308641479663353698848917)
              ·
                refine ⟨108217569359219704633543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2308641479663353698848917 108217569359219704633543)
                ·
                  rfl

theorem cell22_2845165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 6].length) (baseStart_2845165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845165 prefixEnd_2845165 := by exact prefixLift 2845165
  have htrace : WordTrace (prefixWord ++ tailWord_2845165) baseStart_2845165 baseEnd_2845165 := by
    simpa [prefixWord, tailWord_2845165, baseEnd_2845165] using wordTrace_append hprefix tailTrace_2845165
  have hstable : (prefixWord ++ tailWord_2845165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845165).length < 2 ^ (prefixWord ++ tailWord_2845165).sum := by decide
  have hdescent : baseEnd_2845165 < baseStart_2845165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845221 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 6]
def baseStart_2845221 : Nat := 118140960795 + 2845221 * 2 ^ 59
def prefixEnd_2845221 : Nat := 4983230072969 + 3 ^ 40 * 2845221 * 2
def baseEnd_2845221 : Nat := 324659098059137287433905

theorem tailTrace_2845221 : CollatzResearch.WordTrace tailWord_2845221 prefixEnd_2845221 324659098059137287433905 := by
  unfold tailWord_2845221
  simp only [CollatzResearch.WordTrace]
  refine ⟨103773735225257716905439517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69182490150171811270293011 103773735225257716905439517)
  ·
    refine ⟨38915150709471643839539819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103773735225257716905439517 38915150709471643839539819)
    ·
      refine ⟨58372726064207465759309729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38915150709471643839539819 58372726064207465759309729)
      ·
        refine ⟨43779544548155599319482297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58372726064207465759309729 43779544548155599319482297)
        ·
          refine ⟨32834658411116699489611723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43779544548155599319482297 32834658411116699489611723)
          ·
            refine ⟨49251987616675049234417585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32834658411116699489611723 49251987616675049234417585)
            ·
              refine ⟨36938990712506286925813189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49251987616675049234417585 36938990712506286925813189)
              ·
                refine ⟨6926060758594928798589973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36938990712506286925813189 6926060758594928798589973)
                ·
                  refine ⟨324659098059137287433905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6926060758594928798589973 324659098059137287433905)
                  ·
                    rfl

theorem cell22_2845221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_2845221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845221 prefixEnd_2845221 := by exact prefixLift 2845221
  have htrace : WordTrace (prefixWord ++ tailWord_2845221) baseStart_2845221 baseEnd_2845221 := by
    simpa [prefixWord, tailWord_2845221, baseEnd_2845221] using wordTrace_append hprefix tailTrace_2845221
  have hstable : (prefixWord ++ tailWord_2845221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845221).length < 2 ^ (prefixWord ++ tailWord_2845221).sum := by decide
  have hdescent : baseEnd_2845221 < baseStart_2845221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845240 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 1, 4]
def baseStart_2845240 : Nat := 118140960795 + 2845240 * 2 ^ 59
def prefixEnd_2845240 : Nat := 4983230072969 + 3 ^ 40 * 2845240 * 2
def baseEnd_2845240 : Nat := 973983798265702146076657

theorem tailTrace_2845240 : CollatzResearch.WordTrace tailWord_2845240 prefixEnd_2845240 973983798265702146076657 := by
  unfold tailWord_2845240
  simp only [CollatzResearch.WordTrace]
  refine ⟨51887214106094441575190587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69182952141459255433587449 51887214106094441575190587)
  ·
    refine ⟨77830821159141662362785881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51887214106094441575190587 77830821159141662362785881)
    ·
      refine ⟨58373115869356246772089411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77830821159141662362785881 58373115869356246772089411)
      ·
        refine ⟨87559673804034370158134117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58373115869356246772089411 87559673804034370158134117)
        ·
          refine ⟨16417438838256444404650147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87559673804034370158134117 16417438838256444404650147)
          ·
            refine ⟨24626158257384666606975221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16417438838256444404650147 24626158257384666606975221)
            ·
              refine ⟨2308702336629812494403927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24626158257384666606975221 2308702336629812494403927)
              ·
                refine ⟨3463053504944718741605891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308702336629812494403927 3463053504944718741605891)
                ·
                  refine ⟨5194580257417078112408837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463053504944718741605891 5194580257417078112408837)
                  ·
                    refine ⟨973983798265702146076657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5194580257417078112408837 973983798265702146076657)
                    ·
                      rfl

theorem cell22_2845240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_2845240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845240 prefixEnd_2845240 := by exact prefixLift 2845240
  have htrace : WordTrace (prefixWord ++ tailWord_2845240) baseStart_2845240 baseEnd_2845240 := by
    simpa [prefixWord, tailWord_2845240, baseEnd_2845240] using wordTrace_append hprefix tailTrace_2845240
  have hstable : (prefixWord ++ tailWord_2845240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845240).length < 2 ^ (prefixWord ++ tailWord_2845240).sum := by decide
  have hdescent : baseEnd_2845240 < baseStart_2845240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845255 : List Nat := [1, 1, 4, 1, 4, 2, 1, 4, 4]
def baseStart_2845255 : Nat := 118140960795 + 2845255 * 2 ^ 59
def prefixEnd_2845255 : Nat := 4983230072969 + 3 ^ 40 * 2845255 * 2
def baseEnd_2845255 : Nat := 324662977690749035650537

theorem tailTrace_2845255 : CollatzResearch.WordTrace tailWord_2845255 prefixEnd_2845255 324662977690749035650537 := by
  unfold tailWord_2845255
  simp only [CollatzResearch.WordTrace]
  refine ⟨103774975307134540712177219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69183316871423027141451479 103774975307134540712177219)
  ·
    refine ⟨155662462960701811068265829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103774975307134540712177219 155662462960701811068265829)
    ·
      refine ⟨29186711805131589575299843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155662462960701811068265829 29186711805131589575299843)
      ·
        refine ⟨43780067707697384362949765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29186711805131589575299843 43780067707697384362949765)
        ·
          refine ⟨8208762695193259568053081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43780067707697384362949765 8208762695193259568053081)
          ·
            refine ⟨6156572021394944676039811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8208762695193259568053081 6156572021394944676039811)
            ·
              refine ⟨9234858032092417014059717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6156572021394944676039811 9234858032092417014059717)
              ·
                refine ⟨1731535881017328190136197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9234858032092417014059717 1731535881017328190136197)
                ·
                  refine ⟨324662977690749035650537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1731535881017328190136197 324662977690749035650537)
                  ·
                    rfl

theorem cell22_2845255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 4].length) (baseStart_2845255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845255 prefixEnd_2845255 := by exact prefixLift 2845255
  have htrace : WordTrace (prefixWord ++ tailWord_2845255) baseStart_2845255 baseEnd_2845255 := by
    simpa [prefixWord, tailWord_2845255, baseEnd_2845255] using wordTrace_append hprefix tailTrace_2845255
  have hstable : (prefixWord ++ tailWord_2845255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845255).length < 2 ^ (prefixWord ++ tailWord_2845255).sum := by decide
  have hdescent : baseEnd_2845255 < baseStart_2845255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845283 : List Nat := [1, 1, 1, 5, 1, 2, 5, 6]
def baseStart_2845283 : Nat := 118140960795 + 2845283 * 2 ^ 59
def prefixEnd_2845283 : Nat := 4983230072969 + 3 ^ 40 * 2845283 * 2
def baseEnd_2845283 : Nat := 108222057560496040805725

theorem tailTrace_2845283 : CollatzResearch.WordTrace tailWord_2845283 prefixEnd_2845283 108222057560496040805725 := by
  unfold tailWord_2845283
  simp only [CollatzResearch.WordTrace]
  refine ⟨103775996551033101494196503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69183997700688734329464335 103775996551033101494196503)
  ·
    refine ⟨155663994826549652241294755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103775996551033101494196503 155663994826549652241294755)
    ·
      refine ⟨233495992239824478361942133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155663994826549652241294755 233495992239824478361942133)
      ·
        refine ⟨21890249272483544846432075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233495992239824478361942133 21890249272483544846432075)
        ·
          refine ⟨32835373908725317269648113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21890249272483544846432075 32835373908725317269648113)
          ·
            refine ⟨24626530431543987952236085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32835373908725317269648113 24626530431543987952236085)
            ·
              refine ⟨2308737227957248870522133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24626530431543987952236085 2308737227957248870522133)
              ·
                refine ⟨108222057560496040805725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2308737227957248870522133 108222057560496040805725)
                ·
                  rfl

theorem cell22_2845283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 6].length) (baseStart_2845283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845283 prefixEnd_2845283 := by exact prefixLift 2845283
  have htrace : WordTrace (prefixWord ++ tailWord_2845283) baseStart_2845283 baseEnd_2845283 := by
    simpa [prefixWord, tailWord_2845283, baseEnd_2845283] using wordTrace_append hprefix tailTrace_2845283
  have hstable : (prefixWord ++ tailWord_2845283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845283).length < 2 ^ (prefixWord ++ tailWord_2845283).sum := by decide
  have hdescent : baseEnd_2845283 < baseStart_2845283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845332 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2845332 : Nat := 118140960795 + 2845332 * 2 ^ 59
def prefixEnd_2845332 : Nat := 4983230072969 + 3 ^ 40 * 2845332 * 2
def baseEnd_2845332 : Nat := 974015291745844572776375

theorem tailTrace_2845332 : CollatzResearch.WordTrace tailWord_2845332 prefixEnd_2845332 974015291745844572776375 := by
  unfold tailWord_2845332
  simp only [CollatzResearch.WordTrace]
  refine ⟨51888891863927791431365125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69185189151903721908486833 51888891863927791431365125)
  ·
    refine ⟨9729167224486460893380961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51888891863927791431365125 9729167224486460893380961)
    ·
      refine ⟨7296875418364845670035721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9729167224486460893380961 7296875418364845670035721)
      ·
        refine ⟨5472656563773634252526791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7296875418364845670035721 5472656563773634252526791)
        ·
          refine ⟨8208984845660451378790187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472656563773634252526791 8208984845660451378790187)
          ·
            refine ⟨12313477268490677068185281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8208984845660451378790187 12313477268490677068185281)
            ·
              refine ⟨9235107951368007801138961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12313477268490677068185281 9235107951368007801138961)
              ·
                refine ⟨6926330963526005850854221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9235107951368007801138961 6926330963526005850854221)
                ·
                  refine ⟨2597374111322252194070333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6926330963526005850854221 2597374111322252194070333)
                  ·
                    refine ⟨974015291745844572776375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2597374111322252194070333 974015291745844572776375)
                    ·
                      rfl

theorem cell22_2845332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2845332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845332 prefixEnd_2845332 := by exact prefixLift 2845332
  have htrace : WordTrace (prefixWord ++ tailWord_2845332) baseStart_2845332 baseEnd_2845332 := by
    simpa [prefixWord, tailWord_2845332, baseEnd_2845332] using wordTrace_append hprefix tailTrace_2845332
  have hstable : (prefixWord ++ tailWord_2845332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845332).length < 2 ^ (prefixWord ++ tailWord_2845332).sum := by decide
  have hdescent : baseEnd_2845332 < baseStart_2845332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845366 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2845366 : Nat := 118140960795 + 2845366 * 2 ^ 59
def prefixEnd_2845366 : Nat := 4983230072969 + 3 ^ 40 * 2845366 * 2
def baseEnd_2845366 : Nat := 974026930640679817426271

theorem tailTrace_2845366 : CollatzResearch.WordTrace tailWord_2845366 prefixEnd_2845366 974026930640679817426271 := by
  unfold tailWord_2845366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486188988108275416841747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69186015873154937779645301 6486188988108275416841747)
  ·
    refine ⟨9729283482162413125262621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6486188988108275416841747 9729283482162413125262621)
    ·
      refine ⟨3648481305810904921973483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9729283482162413125262621 3648481305810904921973483)
      ·
        refine ⟨5472721958716357382960225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3648481305810904921973483 5472721958716357382960225)
        ·
          refine ⟨4104541469037268037220169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5472721958716357382960225 4104541469037268037220169)
          ·
            refine ⟨3078406101777951027915127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4104541469037268037220169 3078406101777951027915127)
            ·
              refine ⟨4617609152666926541872691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078406101777951027915127 4617609152666926541872691)
              ·
                refine ⟨6926413729000389812809037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617609152666926541872691 6926413729000389812809037)
                ·
                  refine ⟨2597405148375146179803389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6926413729000389812809037 2597405148375146179803389)
                  ·
                    refine ⟨974026930640679817426271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2597405148375146179803389 974026930640679817426271)
                    ·
                      rfl

theorem cell22_2845366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2845366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845366 prefixEnd_2845366 := by exact prefixLift 2845366
  have htrace : WordTrace (prefixWord ++ tailWord_2845366) baseStart_2845366 baseEnd_2845366 := by
    simpa [prefixWord, tailWord_2845366, baseEnd_2845366] using wordTrace_append hprefix tailTrace_2845366
  have hstable : (prefixWord ++ tailWord_2845366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845366).length < 2 ^ (prefixWord ++ tailWord_2845366).sum := by decide
  have hdescent : baseEnd_2845366 < baseStart_2845366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845422 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_2845422 : Nat := 118140960795 + 2845422 * 2 ^ 59
def prefixEnd_2845422 : Nat := 4983230072969 + 3 ^ 40 * 2845422 * 2
def baseEnd_2845422 : Nat := 974046100585114338026099

theorem tailTrace_2845422 : CollatzResearch.WordTrace tailWord_2845422 prefixEnd_2845422 974046100585114338026099 := by
  unfold tailWord_2845422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12972633287191191029188315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69187377531686352155671013 12972633287191191029188315)
  ·
    refine ⟨19458949930786786543782473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12972633287191191029188315 19458949930786786543782473)
    ·
      refine ⟨14594212448090089907836855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19458949930786786543782473 14594212448090089907836855)
      ·
        refine ⟨21891318672135134861755283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14594212448090089907836855 21891318672135134861755283)
        ·
          refine ⟨32836978008202702292632925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21891318672135134861755283 32836978008202702292632925)
          ·
            refine ⟨12313866753076013359737347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32836978008202702292632925 12313866753076013359737347)
            ·
              refine ⟨18470800129614020039606021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12313866753076013359737347 18470800129614020039606021)
              ·
                refine ⟨3463275024302628757426129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18470800129614020039606021 3463275024302628757426129)
                ·
                  refine ⟨2597456268226971568069597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3463275024302628757426129 2597456268226971568069597)
                  ·
                    refine ⟨974046100585114338026099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2597456268226971568069597 974046100585114338026099)
                    ·
                      rfl

theorem cell22_2845422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_2845422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845422 prefixEnd_2845422 := by exact prefixLift 2845422
  have htrace : WordTrace (prefixWord ++ tailWord_2845422) baseStart_2845422 baseEnd_2845422 := by
    simpa [prefixWord, tailWord_2845422, baseEnd_2845422] using wordTrace_append hprefix tailTrace_2845422
  have hstable : (prefixWord ++ tailWord_2845422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845422).length < 2 ^ (prefixWord ++ tailWord_2845422).sum := by decide
  have hdescent : baseEnd_2845422 < baseStart_2845422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845480 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 7]
def baseStart_2845480 : Nat := 118140960795 + 2845480 * 2 ^ 59
def prefixEnd_2845480 : Nat := 4983230072969 + 3 ^ 40 * 2845480 * 2
def baseEnd_2845480 : Nat := 324688651723473840025307

theorem tailTrace_2845480 : CollatzResearch.WordTrace tailWord_2845480 prefixEnd_2845480 324688651723473840025307 := by
  unfold tailWord_2845480
  simp only [CollatzResearch.WordTrace]
  refine ⟨51891590865659702069558947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69188787820879602759411929 51891590865659702069558947)
  ·
    refine ⟨77837386298489553104338421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51891590865659702069558947 77837386298489553104338421)
    ·
      refine ⟨7297254965483395603531727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77837386298489553104338421 7297254965483395603531727)
      ·
        refine ⟨10945882448225093405297591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297254965483395603531727 10945882448225093405297591)
        ·
          refine ⟨16418823672337640107946387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10945882448225093405297591 16418823672337640107946387)
          ·
            refine ⟨24628235508506460161919581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16418823672337640107946387 24628235508506460161919581)
            ·
              refine ⟨9235588315689922560719843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24628235508506460161919581 9235588315689922560719843)
              ·
                refine ⟨13853382473534883841079765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9235588315689922560719843 13853382473534883841079765)
                ·
                  refine ⟨324688651723473840025307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13853382473534883841079765 324688651723473840025307)
                  ·
                    rfl

theorem cell22_2845480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_2845480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845480 prefixEnd_2845480 := by exact prefixLift 2845480
  have htrace : WordTrace (prefixWord ++ tailWord_2845480) baseStart_2845480 baseEnd_2845480 := by
    simpa [prefixWord, tailWord_2845480, baseEnd_2845480] using wordTrace_append hprefix tailTrace_2845480
  have hstable : (prefixWord ++ tailWord_2845480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845480).length < 2 ^ (prefixWord ++ tailWord_2845480).sum := by decide
  have hdescent : baseEnd_2845480 < baseStart_2845480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845527 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 1, 4]
def baseStart_2845527 : Nat := 118140960795 + 2845527 * 2 ^ 59
def prefixEnd_2845527 : Nat := 4983230072969 + 3 ^ 40 * 2845527 * 2
def baseEnd_2845527 : Nat := 974082044230929064150777

theorem tailTrace_2845527 : CollatzResearch.WordTrace tailWord_2845527 prefixEnd_2845527 974082044230929064150777 := by
  unfold tailWord_2845527
  simp only [CollatzResearch.WordTrace]
  refine ⟨103784895962149131166078835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69189930641432754110719223 103784895962149131166078835)
  ·
    refine ⟨155677343943223696749118253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103784895962149131166078835 155677343943223696749118253)
    ·
      refine ⟨58379003978708886280919345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155677343943223696749118253 58379003978708886280919345)
      ·
        refine ⟨43784252984031664710689509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58379003978708886280919345 43784252984031664710689509)
        ·
          refine ⟨8209547434505937133254283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43784252984031664710689509 8209547434505937133254283)
          ·
            refine ⟨12314321151758905699881425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8209547434505937133254283 12314321151758905699881425)
            ·
              refine ⟨9235740863819179274911069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12314321151758905699881425 9235740863819179274911069)
              ·
                refine ⟨3463402823932192228091651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9235740863819179274911069 3463402823932192228091651)
                ·
                  refine ⟨5195104235898288342137477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463402823932192228091651 5195104235898288342137477)
                  ·
                    refine ⟨974082044230929064150777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5195104235898288342137477 974082044230929064150777)
                    ·
                      rfl

theorem cell22_2845527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_2845527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845527 prefixEnd_2845527 := by exact prefixLift 2845527
  have htrace : WordTrace (prefixWord ++ tailWord_2845527) baseStart_2845527 baseEnd_2845527 := by
    simpa [prefixWord, tailWord_2845527, baseEnd_2845527] using wordTrace_append hprefix tailTrace_2845527
  have hstable : (prefixWord ++ tailWord_2845527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845527).length < 2 ^ (prefixWord ++ tailWord_2845527).sum := by decide
  have hdescent : baseEnd_2845527 < baseStart_2845527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845600 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_2845600 : Nat := 118140960795 + 2845600 * 2 ^ 59
def prefixEnd_2845600 : Nat := 4983230072969 + 3 ^ 40 * 2845600 * 2
def baseEnd_2845600 : Nat := 974107033622781207075553

theorem tailTrace_2845600 : CollatzResearch.WordTrace tailWord_2845600 prefixEnd_2845600 974107033622781207075553 := by
  unfold tailWord_2845600
  simp only [CollatzResearch.WordTrace]
  refine ⟨51893779245442332316743127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69191705660589776422324169 51893779245442332316743127)
  ·
    refine ⟨77840668868163498475114691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51893779245442332316743127 77840668868163498475114691)
    ·
      refine ⟨116761003302245247712672037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77840668868163498475114691 116761003302245247712672037)
      ·
        refine ⟨21892688119170983946126007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116761003302245247712672037 21892688119170983946126007)
        ·
          refine ⟨32839032178756475919189011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21892688119170983946126007 32839032178756475919189011)
          ·
            refine ⟨49258548268134713878783517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32839032178756475919189011 49258548268134713878783517)
            ·
              refine ⟨18471955600550517704543819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49258548268134713878783517 18471955600550517704543819)
              ·
                refine ⟨27707933400825776556815729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18471955600550517704543819 27707933400825776556815729)
                ·
                  refine ⟨20780950050619332417611797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27707933400825776556815729 20780950050619332417611797)
                  ·
                    refine ⟨974107033622781207075553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20780950050619332417611797 974107033622781207075553)
                    ·
                      rfl

theorem cell22_2845600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_2845600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845600 prefixEnd_2845600 := by exact prefixLift 2845600
  have htrace : WordTrace (prefixWord ++ tailWord_2845600) baseStart_2845600 baseEnd_2845600 := by
    simpa [prefixWord, tailWord_2845600, baseEnd_2845600] using wordTrace_append hprefix tailTrace_2845600
  have hstable : (prefixWord ++ tailWord_2845600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845600).length < 2 ^ (prefixWord ++ tailWord_2845600).sum := by decide
  have hdescent : baseEnd_2845600 < baseStart_2845600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845638 : List Nat := [6, 1, 3, 1, 1, 1, 9]
def baseStart_2845638 : Nat := 118140960795 + 2845638 * 2 ^ 59
def prefixEnd_2845638 : Nat := 4983230072969 + 3 ^ 40 * 2845638 * 2
def baseEnd_2845638 : Nat := 36078520066643028689831

theorem tailTrace_2845638 : CollatzResearch.WordTrace tailWord_2845638 prefixEnd_2845638 36078520066643028689831 := by
  unfold tailWord_2845638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3243404514523343660105299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69192629643164664748913045 3243404514523343660105299)
  ·
    refine ⟨4865106771785015490157949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3243404514523343660105299 4865106771785015490157949)
    ·
      refine ⟨1824415039419380808809231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4865106771785015490157949 1824415039419380808809231)
      ·
        refine ⟨2736622559129071213213847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824415039419380808809231 2736622559129071213213847)
        ·
          refine ⟨4104933838693606819820771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736622559129071213213847 4104933838693606819820771)
          ·
            refine ⟨6157400758040410229731157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104933838693606819820771 6157400758040410229731157)
            ·
              refine ⟨36078520066643028689831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6157400758040410229731157 36078520066643028689831)
              ·
                rfl

theorem cell22_2845638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 9].length) (baseStart_2845638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845638 prefixEnd_2845638 := by exact prefixLift 2845638
  have htrace : WordTrace (prefixWord ++ tailWord_2845638) baseStart_2845638 baseEnd_2845638 := by
    simpa [prefixWord, tailWord_2845638, baseEnd_2845638] using wordTrace_append hprefix tailTrace_2845638
  have hstable : (prefixWord ++ tailWord_2845638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845638).length < 2 ^ (prefixWord ++ tailWord_2845638).sum := by decide
  have hdescent : baseEnd_2845638 < baseStart_2845638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845679 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 1, 4]
def baseStart_2845679 : Nat := 118140960795 + 2845679 * 2 ^ 59
def prefixEnd_2845679 : Nat := 4983230072969 + 3 ^ 40 * 2845679 * 2
def baseEnd_2845679 : Nat := 974134076937251334350311

theorem tailTrace_2845679 : CollatzResearch.WordTrace tailWord_2845679 prefixEnd_2845679 974134076937251334350311 := by
  unfold tailWord_2845679
  simp only [CollatzResearch.WordTrace]
  refine ⟨103790439857598461125612091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69193626571732307417074727 103790439857598461125612091)
  ·
    refine ⟨155685659786397691688418137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103790439857598461125612091 155685659786397691688418137)
    ·
      refine ⟨116764244839798268766313603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155685659786397691688418137 116764244839798268766313603)
      ·
        refine ⟨175146367259697403149470405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116764244839798268766313603 175146367259697403149470405)
        ·
          refine ⟨32839943861193263090525701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175146367259697403149470405 32839943861193263090525701)
          ·
            refine ⟨6157489473973736829473569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32839943861193263090525701 6157489473973736829473569)
            ·
              refine ⟨4618117105480302622105177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6157489473973736829473569 4618117105480302622105177)
              ·
                refine ⟨3463587829110226966578883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4618117105480302622105177 3463587829110226966578883)
                ·
                  refine ⟨5195381743665340449868325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463587829110226966578883 5195381743665340449868325)
                  ·
                    refine ⟨974134076937251334350311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5195381743665340449868325 974134076937251334350311)
                    ·
                      rfl

theorem cell22_2845679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_2845679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845679 prefixEnd_2845679 := by exact prefixLift 2845679
  have htrace : WordTrace (prefixWord ++ tailWord_2845679) baseStart_2845679 baseEnd_2845679 := by
    simpa [prefixWord, tailWord_2845679, baseEnd_2845679] using wordTrace_append hprefix tailTrace_2845679
  have hstable : (prefixWord ++ tailWord_2845679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845679).length < 2 ^ (prefixWord ++ tailWord_2845679).sum := by decide
  have hdescent : baseEnd_2845679 < baseStart_2845679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845707 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 4, 4]
def baseStart_2845707 : Nat := 118140960795 + 2845707 * 2 ^ 59
def prefixEnd_2845707 : Nat := 4983230072969 + 3 ^ 40 * 2845707 * 2
def baseEnd_2845707 : Nat := 974143661909468594650225

theorem tailTrace_2845707 : CollatzResearch.WordTrace tailWord_2845707 prefixEnd_2845707 974143661909468594650225 := by
  unfold tailWord_2845707
  simp only [CollatzResearch.WordTrace]
  refine ⟨103791461101497021907631375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69194307400998014605087583 103791461101497021907631375)
  ·
    refine ⟨155687191652245532861447063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103791461101497021907631375 155687191652245532861447063)
    ·
      refine ⟨233530787478368299292170595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155687191652245532861447063 233530787478368299292170595)
      ·
        refine ⟨350296181217552448938255893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233530787478368299292170595 350296181217552448938255893)
        ·
          refine ⟨16420133494572771043980745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 350296181217552448938255893 16420133494572771043980745)
          ·
            refine ⟨12315100120929578282985559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16420133494572771043980745 12315100120929578282985559)
            ·
              refine ⟨18472650181394367424478339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12315100120929578282985559 18472650181394367424478339)
              ·
                refine ⟨27708975272091551136717509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18472650181394367424478339 27708975272091551136717509)
                ·
                  refine ⟨5195432863517165838134533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27708975272091551136717509 5195432863517165838134533)
                  ·
                    refine ⟨974143661909468594650225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5195432863517165838134533 974143661909468594650225)
                    ·
                      rfl

theorem cell22_2845707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 4].length) (baseStart_2845707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845707 prefixEnd_2845707 := by exact prefixLift 2845707
  have htrace : WordTrace (prefixWord ++ tailWord_2845707) baseStart_2845707 baseEnd_2845707 := by
    simpa [prefixWord, tailWord_2845707, baseEnd_2845707] using wordTrace_append hprefix tailTrace_2845707
  have hstable : (prefixWord ++ tailWord_2845707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845707).length < 2 ^ (prefixWord ++ tailWord_2845707).sum := by decide
  have hdescent : baseEnd_2845707 < baseStart_2845707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845722 : List Nat := [3, 1, 1, 3, 1, 2, 4, 7]
def baseStart_2845722 : Nat := 118140960795 + 2845722 * 2 ^ 59
def prefixEnd_2845722 : Nat := 4983230072969 + 3 ^ 40 * 2845722 * 2
def baseEnd_2845722 : Nat := 108238755190668172836131

theorem tailTrace_2845722 : CollatzResearch.WordTrace tailWord_2845722 prefixEnd_2845722 108238755190668172836131 := by
  unfold tailWord_2845722
  simp only [CollatzResearch.WordTrace]
  refine ⟨25948002049110669867356855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69194672130961786312951613 25948002049110669867356855)
  ·
    refine ⟨38922003073666004801035283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25948002049110669867356855 38922003073666004801035283)
    ·
      refine ⟨58383004610499007201552925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38922003073666004801035283 58383004610499007201552925)
      ·
        refine ⟨21893626728937127700582347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58383004610499007201552925 21893626728937127700582347)
        ·
          refine ⟨32840440093405691550873521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21893626728937127700582347 32840440093405691550873521)
          ·
            refine ⟨24630330070054268663155141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32840440093405691550873521 24630330070054268663155141)
            ·
              refine ⟨4618186888135175374341589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24630330070054268663155141 4618186888135175374341589)
              ·
                refine ⟨108238755190668172836131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4618186888135175374341589 108238755190668172836131)
                ·
                  rfl

theorem cell22_2845722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_2845722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845722 prefixEnd_2845722 := by exact prefixLift 2845722
  have htrace : WordTrace (prefixWord ++ tailWord_2845722) baseStart_2845722 baseEnd_2845722 := by
    simpa [prefixWord, tailWord_2845722, baseEnd_2845722] using wordTrace_append hprefix tailTrace_2845722
  have hstable : (prefixWord ++ tailWord_2845722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845722).length < 2 ^ (prefixWord ++ tailWord_2845722).sum := by decide
  have hdescent : baseEnd_2845722 < baseStart_2845722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845822 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2845822 : Nat := 118140960795 + 2845822 * 2 ^ 59
def prefixEnd_2845822 : Nat := 4983230072969 + 3 ^ 40 * 2845822 * 2
def baseEnd_2845822 : Nat := 974183028759646628024873

theorem tailTrace_2845822 : CollatzResearch.WordTrace tailWord_2845822 prefixEnd_2845822 974183028759646628024873 := by
  unfold tailWord_2845822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12974456937010049568508465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69197103664053597698711813 12974456937010049568508465)
  ·
    refine ⟨9730842702757537176381349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12974456937010049568508465 9730842702757537176381349)
    ·
      refine ⟨1824533006767038220571503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9730842702757537176381349 1824533006767038220571503)
      ·
        refine ⟨2736799510150557330857255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824533006767038220571503 2736799510150557330857255)
        ·
          refine ⟨4105199265225835996285883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736799510150557330857255 4105199265225835996285883)
          ·
            refine ⟨6157798897838753994428825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105199265225835996285883 6157798897838753994428825)
            ·
              refine ⟨4618349173379065495821619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6157798897838753994428825 4618349173379065495821619)
              ·
                refine ⟨6927523760068598243732429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618349173379065495821619 6927523760068598243732429)
                ·
                  refine ⟨2597821410025724341399661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6927523760068598243732429 2597821410025724341399661)
                  ·
                    refine ⟨974183028759646628024873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2597821410025724341399661 974183028759646628024873)
                    ·
                      rfl

theorem cell22_2845822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2845822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845822 prefixEnd_2845822 := by exact prefixLift 2845822
  have htrace : WordTrace (prefixWord ++ tailWord_2845822) baseStart_2845822 baseEnd_2845822 := by
    simpa [prefixWord, tailWord_2845822, baseEnd_2845822] using wordTrace_append hprefix tailTrace_2845822
  have hstable : (prefixWord ++ tailWord_2845822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845822).length < 2 ^ (prefixWord ++ tailWord_2845822).sum := by decide
  have hdescent : baseEnd_2845822 < baseStart_2845822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845863 : List Nat := [1, 1, 6, 2, 1, 1, 3, 3, 4]
def baseStart_2845863 : Nat := 118140960795 + 2845863 * 2 ^ 59
def prefixEnd_2845863 : Nat := 4983230072969 + 3 ^ 40 * 2845863 * 2
def baseEnd_2845863 : Nat := 324732354632512062583249

theorem tailTrace_2845863 : CollatzResearch.WordTrace tailWord_2845863 prefixEnd_2845863 324732354632512062583249 := by
  unfold tailWord_2845863
  simp only [CollatzResearch.WordTrace]
  refine ⟨103797150888931860550310243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69198100592621240366873495 103797150888931860550310243)
  ·
    refine ⟨155695726333397790825465365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103797150888931860550310243 155695726333397790825465365)
    ·
      refine ⟨7298237171878021444943689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155695726333397790825465365 7298237171878021444943689)
      ·
        refine ⟨5473677878908516083707767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7298237171878021444943689 5473677878908516083707767)
        ·
          refine ⟨8210516818362774125561651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5473677878908516083707767 8210516818362774125561651)
          ·
            refine ⟨12315775227544161188342477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8210516818362774125561651 12315775227544161188342477)
            ·
              refine ⟨4618415710329060445628429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12315775227544161188342477 4618415710329060445628429)
              ·
                refine ⟨1731905891373397667110661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4618415710329060445628429 1731905891373397667110661)
                ·
                  refine ⟨324732354632512062583249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1731905891373397667110661 324732354632512062583249)
                  ·
                    rfl

theorem cell22_2845863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 4].length) (baseStart_2845863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845863 prefixEnd_2845863 := by exact prefixLift 2845863
  have htrace : WordTrace (prefixWord ++ tailWord_2845863) baseStart_2845863 baseEnd_2845863 := by
    simpa [prefixWord, tailWord_2845863, baseEnd_2845863] using wordTrace_append hprefix tailTrace_2845863
  have hstable : (prefixWord ++ tailWord_2845863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845863).length < 2 ^ (prefixWord ++ tailWord_2845863).sum := by decide
  have hdescent : baseEnd_2845863 < baseStart_2845863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845872 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_2845872 : Nat := 118140960795 + 2845872 * 2 ^ 59
def prefixEnd_2845872 : Nat := 4983230072969 + 3 ^ 40 * 2845872 * 2
def baseEnd_2845872 : Nat := 974200144781463164274719

theorem tailTrace_2845872 : CollatzResearch.WordTrace tailWord_2845872 prefixEnd_2845872 974200144781463164274719 := by
  unfold tailWord_2845872
  simp only [CollatzResearch.WordTrace]
  refine ⟨51898739572949627543693935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69198319430599503391591913 51898739572949627543693935)
  ·
    refine ⟨77848109359424441315540903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51898739572949627543693935 77848109359424441315540903)
    ·
      refine ⟨116772164039136661973311355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77848109359424441315540903 116772164039136661973311355)
      ·
        refine ⟨175158246058704992959967033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116772164039136661973311355 175158246058704992959967033)
        ·
          refine ⟨131368684544028744719975275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175158246058704992959967033 131368684544028744719975275)
          ·
            refine ⟨197053026816043117079962913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131368684544028744719975275 197053026816043117079962913)
            ·
              refine ⟨147789770112032337809972185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197053026816043117079962913 147789770112032337809972185)
              ·
                refine ⟨110842327584024253357479139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147789770112032337809972185 110842327584024253357479139)
                ·
                  refine ⟨166263491376036380036218709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110842327584024253357479139 166263491376036380036218709)
                  ·
                    refine ⟨974200144781463164274719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 166263491376036380036218709 974200144781463164274719)
                    ·
                      rfl

theorem cell22_2845872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_2845872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845872 prefixEnd_2845872 := by exact prefixLift 2845872
  have htrace : WordTrace (prefixWord ++ tailWord_2845872) baseStart_2845872 baseEnd_2845872 := by
    simpa [prefixWord, tailWord_2845872, baseEnd_2845872] using wordTrace_append hprefix tailTrace_2845872
  have hstable : (prefixWord ++ tailWord_2845872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845872).length < 2 ^ (prefixWord ++ tailWord_2845872).sum := by decide
  have hdescent : baseEnd_2845872 < baseStart_2845872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845874 : List Nat := [3, 2, 1, 1, 1, 6, 8]
def baseStart_2845874 : Nat := 118140960795 + 2845874 * 2 ^ 59
def prefixEnd_2845874 : Nat := 4983230072969 + 3 ^ 40 * 2845874 * 2
def baseEnd_2845874 : Nat := 36081512200827252804619

theorem tailTrace_2845874 : CollatzResearch.WordTrace tailWord_2845874 prefixEnd_2845874 36081512200827252804619 := by
  unfold tailWord_2845874
  simp only [CollatzResearch.WordTrace]
  refine ⟨25949388022973002357240169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69198368061261339619307117 25949388022973002357240169)
  ·
    refine ⟨19462041017229751767930127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25949388022973002357240169 19462041017229751767930127)
    ·
      refine ⟨29193061525844627651895191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19462041017229751767930127 29193061525844627651895191)
      ·
        refine ⟨43789592288766941477842787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29193061525844627651895191 43789592288766941477842787)
        ·
          refine ⟨65684388433150412216764181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43789592288766941477842787 65684388433150412216764181)
          ·
            refine ⟨3078955707803925572660821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65684388433150412216764181 3078955707803925572660821)
            ·
              refine ⟨36081512200827252804619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3078955707803925572660821 36081512200827252804619)
              ·
                rfl

theorem cell22_2845874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 8].length) (baseStart_2845874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845874 prefixEnd_2845874 := by exact prefixLift 2845874
  have htrace : WordTrace (prefixWord ++ tailWord_2845874) baseStart_2845874 baseEnd_2845874 := by
    simpa [prefixWord, tailWord_2845874, baseEnd_2845874] using wordTrace_append hprefix tailTrace_2845874
  have hstable : (prefixWord ++ tailWord_2845874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845874).length < 2 ^ (prefixWord ++ tailWord_2845874).sum := by decide
  have hdescent : baseEnd_2845874 < baseStart_2845874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845906 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_2845906 : Nat := 118140960795 + 2845906 * 2 ^ 59
def prefixEnd_2845906 : Nat := 4983230072969 + 3 ^ 40 * 2845906 * 2
def baseEnd_2845906 : Nat := 974211783676298408924615

theorem tailTrace_2845906 : CollatzResearch.WordTrace tailWord_2845906 prefixEnd_2845906 974211783676298408924615 := by
  unfold tailWord_2845906
  simp only [CollatzResearch.WordTrace]
  refine ⟨25949679806944019723531393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69199146151850719262750381 25949679806944019723531393)
  ·
    refine ⟨19462259855208014792648545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25949679806944019723531393 19462259855208014792648545)
    ·
      refine ⟨14596694891406011094486409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19462259855208014792648545 14596694891406011094486409)
      ·
        refine ⟨10947521168554508320864807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14596694891406011094486409 10947521168554508320864807)
        ·
          refine ⟨16421281752831762481297211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10947521168554508320864807 16421281752831762481297211)
          ·
            refine ⟨24631922629247643721945817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16421281752831762481297211 24631922629247643721945817)
            ·
              refine ⟨18473941971935732791459363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24631922629247643721945817 18473941971935732791459363)
              ·
                refine ⟨27710912957903599187189045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18473941971935732791459363 27710912957903599187189045)
                ·
                  refine ⟨2597898089803462423798973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27710912957903599187189045 2597898089803462423798973)
                  ·
                    refine ⟨974211783676298408924615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2597898089803462423798973 974211783676298408924615)
                    ·
                      rfl

theorem cell22_2845906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_2845906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845906 prefixEnd_2845906 := by exact prefixLift 2845906
  have htrace : WordTrace (prefixWord ++ tailWord_2845906) baseStart_2845906 baseEnd_2845906 := by
    simpa [prefixWord, tailWord_2845906, baseEnd_2845906] using wordTrace_append hprefix tailTrace_2845906
  have hstable : (prefixWord ++ tailWord_2845906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845906).length < 2 ^ (prefixWord ++ tailWord_2845906).sum := by decide
  have hdescent : baseEnd_2845906 < baseStart_2845906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845910 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2845910 : Nat := 118140960795 + 2845910 * 2 ^ 59
def prefixEnd_2845910 : Nat := 4983230072969 + 3 ^ 40 * 2845910 * 2
def baseEnd_2845910 : Nat := 974213152958043731824603

theorem tailTrace_2845910 : CollatzResearch.WordTrace tailWord_2845910 prefixEnd_2845910 974213152958043731824603 := by
  unfold tailWord_2845910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6487429069985099223579449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69199243413174391718180789 6487429069985099223579449)
  ·
    refine ⟨4865571802488824417684587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6487429069985099223579449 4865571802488824417684587)
    ·
      refine ⟨7298357703733236626526881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865571802488824417684587 7298357703733236626526881)
      ·
        refine ⟨5473768277799927469895161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7298357703733236626526881 5473768277799927469895161)
        ·
          refine ⟨4105326208349945602421371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5473768277799927469895161 4105326208349945602421371)
          ·
            refine ⟨6157989312524918403632057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105326208349945602421371 6157989312524918403632057)
            ·
              refine ⟨4618491984393688802724043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6157989312524918403632057 4618491984393688802724043)
              ·
                refine ⟨6927737976590533204086065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618491984393688802724043 6927737976590533204086065)
                ·
                  refine ⟨5195803482442899903064549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6927737976590533204086065 5195803482442899903064549)
                  ·
                    refine ⟨974213152958043731824603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5195803482442899903064549 974213152958043731824603)
                    ·
                      rfl

theorem cell22_2845910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2845910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845910 prefixEnd_2845910 := by exact prefixLift 2845910
  have htrace : WordTrace (prefixWord ++ tailWord_2845910) baseStart_2845910 baseEnd_2845910 := by
    simpa [prefixWord, tailWord_2845910, baseEnd_2845910] using wordTrace_append hprefix tailTrace_2845910
  have hstable : (prefixWord ++ tailWord_2845910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845910).length < 2 ^ (prefixWord ++ tailWord_2845910).sum := by decide
  have hdescent : baseEnd_2845910 < baseStart_2845910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845964 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 8]
def baseStart_2845964 : Nat := 118140960795 + 2845964 * 2 ^ 59
def prefixEnd_2845964 : Nat := 4983230072969 + 3 ^ 40 * 2845964 * 2
def baseEnd_2845964 : Nat := 324743879420535196991479

theorem tailTrace_2845964 : CollatzResearch.WordTrace tailWord_2845964 prefixEnd_2845964 324743879420535196991479 := by
  unfold tailWord_2845964
  simp only [CollatzResearch.WordTrace]
  refine ⟨51900417330782977399868473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69200556441043969866491297 51900417330782977399868473)
  ·
    refine ⟨38925312998087233049901355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51900417330782977399868473 38925312998087233049901355)
    ·
      refine ⟨58387969497130849574852033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38925312998087233049901355 58387969497130849574852033)
      ·
        refine ⟨43790977122848137181139025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58387969497130849574852033 43790977122848137181139025)
        ·
          refine ⟨32843232842136102885854269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43790977122848137181139025 32843232842136102885854269)
          ·
            refine ⟨12316212315801038582195351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32843232842136102885854269 12316212315801038582195351)
            ·
              refine ⟨18474318473701557873293027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12316212315801038582195351 18474318473701557873293027)
              ·
                refine ⟨27711477710552336809939541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18474318473701557873293027 27711477710552336809939541)
                ·
                  refine ⟨324743879420535196991479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27711477710552336809939541 324743879420535196991479)
                  ·
                    rfl

theorem cell22_2845964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_2845964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845964 prefixEnd_2845964 := by exact prefixLift 2845964
  have htrace : WordTrace (prefixWord ++ tailWord_2845964) baseStart_2845964 baseEnd_2845964 := by
    simpa [prefixWord, tailWord_2845964, baseEnd_2845964] using wordTrace_append hprefix tailTrace_2845964
  have hstable : (prefixWord ++ tailWord_2845964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845964).length < 2 ^ (prefixWord ++ tailWord_2845964).sum := by decide
  have hdescent : baseEnd_2845964 < baseStart_2845964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845966 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_2845966 : Nat := 118140960795 + 2845966 * 2 ^ 59
def prefixEnd_2845966 : Nat := 4983230072969 + 3 ^ 40 * 2845966 * 2
def baseEnd_2845966 : Nat := 974232322902478252424431

theorem tailTrace_2845966 : CollatzResearch.WordTrace tailWord_2845966 prefixEnd_2845966 974232322902478252424431 := by
  unfold tailWord_2845966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975113450944838642663719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69200605071705806094206501 12975113450944838642663719)
  ·
    refine ⟨19462670176417257963995579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12975113450944838642663719 19462670176417257963995579)
    ·
      refine ⟨29194005264625886945993369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19462670176417257963995579 29194005264625886945993369)
      ·
        refine ⟨21895503948469415209495027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29194005264625886945993369 21895503948469415209495027)
        ·
          refine ⟨32843255922704122814242541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21895503948469415209495027 32843255922704122814242541)
          ·
            refine ⟨12316220971014046055340953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32843255922704122814242541 12316220971014046055340953)
            ·
              refine ⟨9237165728260534541505715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12316220971014046055340953 9237165728260534541505715)
              ·
                refine ⟨13855748592390801812258573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9237165728260534541505715 13855748592390801812258573)
                ·
                  refine ⟨5195905722146550679596965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13855748592390801812258573 5195905722146550679596965)
                  ·
                    refine ⟨974232322902478252424431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5195905722146550679596965 974232322902478252424431)
                    ·
                      rfl

theorem cell22_2845966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_2845966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845966 prefixEnd_2845966 := by exact prefixLift 2845966
  have htrace : WordTrace (prefixWord ++ tailWord_2845966) baseStart_2845966 baseEnd_2845966 := by
    simpa [prefixWord, tailWord_2845966, baseEnd_2845966] using wordTrace_append hprefix tailTrace_2845966
  have hstable : (prefixWord ++ tailWord_2845966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845966).length < 2 ^ (prefixWord ++ tailWord_2845966).sum := by decide
  have hdescent : baseEnd_2845966 < baseStart_2845966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845983 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 1, 4]
def baseStart_2845983 : Nat := 118140960795 + 2845983 * 2 ^ 59
def prefixEnd_2845983 : Nat := 4983230072969 + 3 ^ 40 * 2845983 * 2
def baseEnd_2845983 : Nat := 974238142349895874749379

theorem tailTrace_2845983 : CollatzResearch.WordTrace tailWord_2845983 prefixEnd_2845983 974238142349895874749379 := by
  unfold tailWord_2845983
  simp only [CollatzResearch.WordTrace]
  refine ⟨103801527648497121044678603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69201018432331414029785735 103801527648497121044678603)
  ·
    refine ⟨155702291472745681567017905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103801527648497121044678603 155702291472745681567017905)
    ·
      refine ⟨116776718604559261175263429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155702291472745681567017905 116776718604559261175263429)
      ·
        refine ⟨21895634738354861470361893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116776718604559261175263429 21895634738354861470361893)
        ·
          refine ⟨4105431513441536525692855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21895634738354861470361893 4105431513441536525692855)
          ·
            refine ⟨6158147270162304788539283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105431513441536525692855 6158147270162304788539283)
            ·
              refine ⟨9237220905243457182808925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6158147270162304788539283 9237220905243457182808925)
              ·
                refine ⟨3463957839466296443553347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9237220905243457182808925 3463957839466296443553347)
                ·
                  refine ⟨5195936759199444665330021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463957839466296443553347 5195936759199444665330021)
                  ·
                    refine ⟨974238142349895874749379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5195936759199444665330021 974238142349895874749379)
                    ·
                      rfl

theorem cell22_2845983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_2845983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2845983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2845983 prefixEnd_2845983 := by exact prefixLift 2845983
  have htrace : WordTrace (prefixWord ++ tailWord_2845983) baseStart_2845983 baseEnd_2845983 := by
    simpa [prefixWord, tailWord_2845983, baseEnd_2845983] using wordTrace_append hprefix tailTrace_2845983
  have hstable : (prefixWord ++ tailWord_2845983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845983).length < 2 ^ (prefixWord ++ tailWord_2845983).sum := by decide
  have hdescent : baseEnd_2845983 < baseStart_2845983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846024 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_2846024 : Nat := 118140960795 + 2846024 * 2 ^ 59
def prefixEnd_2846024 : Nat := 4983230072969 + 3 ^ 40 * 2846024 * 2
def baseEnd_2846024 : Nat := 974252177487785434474253

theorem tailTrace_2846024 : CollatzResearch.WordTrace tailWord_2846024 prefixEnd_2846024 974252177487785434474253 := by
  unfold tailWord_2846024
  simp only [CollatzResearch.WordTrace]
  refine ⟨51901511520674292523460563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69202015360899056697947417 51901511520674292523460563)
  ·
    refine ⟨77852267281011438785190845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51901511520674292523460563 77852267281011438785190845)
    ·
      refine ⟨29194600230379289544446567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77852267281011438785190845 29194600230379289544446567)
      ·
        refine ⟨43791900345568934316669851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29194600230379289544446567 43791900345568934316669851)
        ·
          refine ⟨65687850518353401475004777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43791900345568934316669851 65687850518353401475004777)
          ·
            refine ⟨49265887888765051106253583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65687850518353401475004777 49265887888765051106253583)
            ·
              refine ⟨73898831833147576659380375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49265887888765051106253583 73898831833147576659380375)
              ·
                refine ⟨110848247749721364989070563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73898831833147576659380375 110848247749721364989070563)
                ·
                  refine ⟨166272371624582047483605845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110848247749721364989070563 166272371624582047483605845)
                  ·
                    refine ⟨974252177487785434474253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 166272371624582047483605845 974252177487785434474253)
                    ·
                      rfl

theorem cell22_2846024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_2846024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846024 prefixEnd_2846024 := by exact prefixLift 2846024
  have htrace : WordTrace (prefixWord ++ tailWord_2846024) baseStart_2846024 baseEnd_2846024 := by
    simpa [prefixWord, tailWord_2846024, baseEnd_2846024] using wordTrace_append hprefix tailTrace_2846024
  have hstable : (prefixWord ++ tailWord_2846024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846024).length < 2 ^ (prefixWord ++ tailWord_2846024).sum := by decide
  have hdescent : baseEnd_2846024 < baseStart_2846024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846041 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 5, 3]
def baseStart_2846041 : Nat := 118140960795 + 2846041 * 2 ^ 59
def prefixEnd_2846041 : Nat := 4983230072969 + 3 ^ 40 * 2846041 * 2
def baseEnd_2846041 : Nat := 974257996935203056799201

theorem tailTrace_2846041 : CollatzResearch.WordTrace tailWord_2846041 prefixEnd_2846041 974257996935203056799201 := by
  unfold tailWord_2846041
  simp only [CollatzResearch.WordTrace]
  refine ⟨103803643082286996950289977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69202428721524664633526651 103803643082286996950289977)
  ·
    refine ⟨77852732311715247712717483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103803643082286996950289977 77852732311715247712717483)
    ·
      refine ⟨116779098467572871569076225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77852732311715247712717483 116779098467572871569076225)
      ·
        refine ⟨87584323850679653676807169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116779098467572871569076225 87584323850679653676807169)
        ·
          refine ⟨65688242888009740257605377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87584323850679653676807169 65688242888009740257605377)
          ·
            refine ⟨49266182166007305193204033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65688242888009740257605377 49266182166007305193204033)
            ·
              refine ⟨36949636624505478894903025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49266182166007305193204033 36949636624505478894903025)
              ·
                refine ⟨27712227468379109171177269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36949636624505478894903025 27712227468379109171177269)
                ·
                  refine ⟨2598021325160541484797869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27712227468379109171177269 2598021325160541484797869)
                  ·
                    refine ⟨974257996935203056799201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598021325160541484797869 974257996935203056799201)
                    ·
                      rfl

theorem cell22_2846041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_2846041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846041 prefixEnd_2846041 := by exact prefixLift 2846041
  have htrace : WordTrace (prefixWord ++ tailWord_2846041) baseStart_2846041 baseEnd_2846041 := by
    simpa [prefixWord, tailWord_2846041, baseEnd_2846041] using wordTrace_append hprefix tailTrace_2846041
  have hstable : (prefixWord ++ tailWord_2846041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846041).length < 2 ^ (prefixWord ++ tailWord_2846041).sum := by decide
  have hdescent : baseEnd_2846041 < baseStart_2846041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846071 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 5]
def baseStart_2846071 : Nat := 118140960795 + 2846071 * 2 ^ 59
def prefixEnd_2846071 : Nat := 4983230072969 + 3 ^ 40 * 2846071 * 2
def baseEnd_2846071 : Nat := 324756088849430992849703

theorem tailTrace_2846071 : CollatzResearch.WordTrace tailWord_2846071 prefixEnd_2846071 324756088849430992849703 := by
  unfold tailWord_2846071
  simp only [CollatzResearch.WordTrace]
  refine ⟨103804737272178312073882067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69203158181452208049254711 103804737272178312073882067)
  ·
    refine ⟨155707105908267468110823101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103804737272178312073882067 155707105908267468110823101)
    ·
      refine ⟨58390164715600300541558663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155707105908267468110823101 58390164715600300541558663)
      ·
        refine ⟨87585247073400450812337995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58390164715600300541558663 87585247073400450812337995)
        ·
          refine ⟨131377870610100676218506993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87585247073400450812337995 131377870610100676218506993)
          ·
            refine ⟨98533402957575507163880245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131377870610100676218506993 98533402957575507163880245)
            ·
              refine ⟨9237506527272703796613773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98533402957575507163880245 9237506527272703796613773)
              ·
                refine ⟨3464064947727263923730165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9237506527272703796613773 3464064947727263923730165)
                ·
                  refine ⟨324756088849430992849703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3464064947727263923730165 324756088849430992849703)
                  ·
                    rfl

theorem cell22_2846071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 5].length) (baseStart_2846071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846071 prefixEnd_2846071 := by exact prefixLift 2846071
  have htrace : WordTrace (prefixWord ++ tailWord_2846071) baseStart_2846071 baseEnd_2846071 := by
    simpa [prefixWord, tailWord_2846071, baseEnd_2846071] using wordTrace_append hprefix tailTrace_2846071
  have hstable : (prefixWord ++ tailWord_2846071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846071).length < 2 ^ (prefixWord ++ tailWord_2846071).sum := by decide
  have hdescent : baseEnd_2846071 < baseStart_2846071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846109 : List Nat := [1, 4, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2846109 : Nat := 118140960795 + 2846109 * 2 ^ 59
def prefixEnd_2846109 : Nat := 4983230072969 + 3 ^ 40 * 2846109 * 2
def baseEnd_2846109 : Nat := 974281274724873546098993

theorem tailTrace_2846109 : CollatzResearch.WordTrace tailWord_2846109 prefixEnd_2846109 974281274724873546098993 := by
  unfold tailWord_2846109
  simp only [CollatzResearch.WordTrace]
  refine ⟨103806123246040644563765381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69204082164027096375843587 103806123246040644563765381)
  ·
    refine ⟨19463648108632620855706009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103806123246040644563765381 19463648108632620855706009)
    ·
      refine ⟨14597736081474465641779507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19463648108632620855706009 14597736081474465641779507)
      ·
        refine ⟨21896604122211698462669261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14597736081474465641779507 21896604122211698462669261)
        ·
          refine ⟨8211226545829386923500973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21896604122211698462669261 8211226545829386923500973)
          ·
            refine ⟨3079209954686020096312865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8211226545829386923500973 3079209954686020096312865)
            ·
              refine ⟨2309407466014515072234649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3079209954686020096312865 2309407466014515072234649)
              ·
                refine ⟨1732055599510886304175987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2309407466014515072234649 1732055599510886304175987)
                ·
                  refine ⟨2598083399266329456263981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732055599510886304175987 2598083399266329456263981)
                  ·
                    refine ⟨974281274724873546098993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598083399266329456263981 974281274724873546098993)
                    ·
                      rfl

theorem cell22_2846109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2846109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846109 prefixEnd_2846109 := by exact prefixLift 2846109
  have htrace : WordTrace (prefixWord ++ tailWord_2846109) baseStart_2846109 baseEnd_2846109 := by
    simpa [prefixWord, tailWord_2846109, baseEnd_2846109] using wordTrace_append hprefix tailTrace_2846109
  have hstable : (prefixWord ++ tailWord_2846109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846109).length < 2 ^ (prefixWord ++ tailWord_2846109).sum := by decide
  have hdescent : baseEnd_2846109 < baseStart_2846109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846116 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 6]
def baseStart_2846116 : Nat := 118140960795 + 2846116 * 2 ^ 59
def prefixEnd_2846116 : Nat := 4983230072969 + 3 ^ 40 * 2846116 * 2
def baseEnd_2846116 : Nat := 324761223655975953724657

theorem tailTrace_2846116 : CollatzResearch.WordTrace tailWord_2846116 prefixEnd_2846116 324761223655975953724657 := by
  unfold tailWord_2846116
  simp only [CollatzResearch.WordTrace]
  refine ⟨51903189278507642379635101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69204252371343523172846801 51903189278507642379635101)
  ·
    refine ⟨19463695979440365892363163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51903189278507642379635101 19463695979440365892363163)
    ·
      refine ⟨29195543969160548838544745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19463695979440365892363163 29195543969160548838544745)
      ·
        refine ⟨21896657976870411628908559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29195543969160548838544745 21896657976870411628908559)
        ·
          refine ⟨32844986965305617443362839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21896657976870411628908559 32844986965305617443362839)
          ·
            refine ⟨49267480447958426165044259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32844986965305617443362839 49267480447958426165044259)
            ·
              refine ⟨73901220671937639247566389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49267480447958426165044259 73901220671937639247566389)
              ·
                refine ⟨6928239437994153679459349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73901220671937639247566389 6928239437994153679459349)
                ·
                  refine ⟨324761223655975953724657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6928239437994153679459349 324761223655975953724657)
                  ·
                    rfl

theorem cell22_2846116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_2846116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846116 prefixEnd_2846116 := by exact prefixLift 2846116
  have htrace : WordTrace (prefixWord ++ tailWord_2846116) baseStart_2846116 baseEnd_2846116 := by
    simpa [prefixWord, tailWord_2846116, baseEnd_2846116] using wordTrace_append hprefix tailTrace_2846116
  have hstable : (prefixWord ++ tailWord_2846116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846116).length < 2 ^ (prefixWord ++ tailWord_2846116).sum := by decide
  have hdescent : baseEnd_2846116 < baseStart_2846116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846120 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2846120 : Nat := 118140960795 + 2846120 * 2 ^ 59
def prefixEnd_2846120 : Nat := 4983230072969 + 3 ^ 40 * 2846120 * 2
def baseEnd_2846120 : Nat := 974285040249673184073959

theorem tailTrace_2846120 : CollatzResearch.WordTrace tailWord_2846120 prefixEnd_2846120 974285040249673184073959 := by
  unfold tailWord_2846120
  simp only [CollatzResearch.WordTrace]
  refine ⟨51903262224500396721207907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69204349632667195628277209 51903262224500396721207907)
  ·
    refine ⟨77854893336750595081811861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51903262224500396721207907 77854893336750595081811861)
    ·
      refine ⟨3649448125160184144459931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77854893336750595081811861 3649448125160184144459931)
      ·
        refine ⟨5474172187740276216689897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3649448125160184144459931 5474172187740276216689897)
        ·
          refine ⟨4105629140805207162517423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5474172187740276216689897 4105629140805207162517423)
          ·
            refine ⟨6158443711207810743776135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105629140805207162517423 6158443711207810743776135)
            ·
              refine ⟨9237665566811716115664203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6158443711207810743776135 9237665566811716115664203)
              ·
                refine ⟨13856498350217574173496305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9237665566811716115664203 13856498350217574173496305)
                ·
                  refine ⟨10392373762663180630122229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13856498350217574173496305 10392373762663180630122229)
                  ·
                    refine ⟨974285040249673184073959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10392373762663180630122229 974285040249673184073959)
                    ·
                      rfl

theorem cell22_2846120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2846120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846120 prefixEnd_2846120 := by exact prefixLift 2846120
  have htrace : WordTrace (prefixWord ++ tailWord_2846120) baseStart_2846120 baseEnd_2846120 := by
    simpa [prefixWord, tailWord_2846120, baseEnd_2846120] using wordTrace_append hprefix tailTrace_2846120
  have hstable : (prefixWord ++ tailWord_2846120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846120).length < 2 ^ (prefixWord ++ tailWord_2846120).sum := by decide
  have hdescent : baseEnd_2846120 < baseStart_2846120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846133 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 6]
def baseStart_2846133 : Nat := 118140960795 + 2846133 * 2 ^ 59
def prefixEnd_2846133 : Nat := 4983230072969 + 3 ^ 40 * 2846133 * 2
def baseEnd_2846133 : Nat := 324763163471781827832973

theorem tailTrace_2846133 : CollatzResearch.WordTrace tailWord_2846133 prefixEnd_2846133 324763163471781827832973 := by
  unfold tailWord_2846133
  simp only [CollatzResearch.WordTrace]
  refine ⟨103806998597953696662639053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69204665731969131108426035 103806998597953696662639053)
  ·
    refine ⟨38927624474232636248489645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103806998597953696662639053 38927624474232636248489645)
    ·
      refine ⟨14597859177837238593183617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38927624474232636248489645 14597859177837238593183617)
      ·
        refine ⟨10948394383377928944887713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14597859177837238593183617 10948394383377928944887713)
        ·
          refine ⟨8211295787533446708665785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10948394383377928944887713 8211295787533446708665785)
          ·
            refine ⟨6158471840650085031499339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8211295787533446708665785 6158471840650085031499339)
            ·
              refine ⟨9237707760975127547249009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6158471840650085031499339 9237707760975127547249009)
              ·
                refine ⟨6928280820731345660436757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9237707760975127547249009 6928280820731345660436757)
                ·
                  refine ⟨324763163471781827832973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6928280820731345660436757 324763163471781827832973)
                  ·
                    rfl

theorem cell22_2846133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_2846133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846133 prefixEnd_2846133 := by exact prefixLift 2846133
  have htrace : WordTrace (prefixWord ++ tailWord_2846133) baseStart_2846133 baseEnd_2846133 := by
    simpa [prefixWord, tailWord_2846133, baseEnd_2846133] using wordTrace_append hprefix tailTrace_2846133
  have hstable : (prefixWord ++ tailWord_2846133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846133).length < 2 ^ (prefixWord ++ tailWord_2846133).sum := by decide
  have hdescent : baseEnd_2846133 < baseStart_2846133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846191 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 2, 6]
def baseStart_2846191 : Nat := 118140960795 + 2846191 * 2 ^ 59
def prefixEnd_2846191 : Nat := 4983230072969 + 3 ^ 40 * 2846191 * 2
def baseEnd_2846191 : Nat := 974309345000652665548741

theorem tailTrace_2846191 : CollatzResearch.WordTrace tailWord_2846191 prefixEnd_2846191 974309345000652665548741 := by
  unfold tailWord_2846191
  simp only [CollatzResearch.WordTrace]
  refine ⟨103809114031743572568250427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69206076021162381712166951 103809114031743572568250427)
  ·
    refine ⟨155713671047615358852375641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103809114031743572568250427 155713671047615358852375641)
    ·
      refine ⟨116785253285711519139281731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155713671047615358852375641 116785253285711519139281731)
      ·
        refine ⟨175177879928567278708922597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116785253285711519139281731 175177879928567278708922597)
        ·
          refine ⟨32845852486606364757922987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175177879928567278708922597 32845852486606364757922987)
          ·
            refine ⟨49268778729909547136884481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32845852486606364757922987 49268778729909547136884481)
            ·
              refine ⟨36951584047432160352663361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49268778729909547136884481 36951584047432160352663361)
              ·
                refine ⟨27713688035574120264497521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36951584047432160352663361 27713688035574120264497521)
                ·
                  refine ⟨20785266026680590198373141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27713688035574120264497521 20785266026680590198373141)
                  ·
                    refine ⟨974309345000652665548741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20785266026680590198373141 974309345000652665548741)
                    ·
                      rfl

theorem cell22_2846191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_2846191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846191 prefixEnd_2846191 := by exact prefixLift 2846191
  have htrace : WordTrace (prefixWord ++ tailWord_2846191) baseStart_2846191 baseEnd_2846191 := by
    simpa [prefixWord, tailWord_2846191, baseEnd_2846191] using wordTrace_append hprefix tailTrace_2846191
  have hstable : (prefixWord ++ tailWord_2846191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846191).length < 2 ^ (prefixWord ++ tailWord_2846191).sum := by decide
  have hdescent : baseEnd_2846191 < baseStart_2846191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846240 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 5]
def baseStart_2846240 : Nat := 118140960795 + 2846240 * 2 ^ 59
def prefixEnd_2846240 : Nat := 4983230072969 + 3 ^ 40 * 2846240 * 2
def baseEnd_2846240 : Nat := 324775372900677623691197

theorem tailTrace_2846240 : CollatzResearch.WordTrace tailWord_2846240 prefixEnd_2846240 324775372900677623691197 := by
  unfold tailWord_2846240
  simp only [CollatzResearch.WordTrace]
  refine ⟨51905450604283026968392087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69207267472377369291189449 51905450604283026968392087)
  ·
    refine ⟨77858175906424540452588131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51905450604283026968392087 77858175906424540452588131)
    ·
      refine ⟨116787263859636810678882197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77858175906424540452588131 116787263859636810678882197)
      ·
        refine ⟨5474402993420475500572603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116787263859636810678882197 5474402993420475500572603)
        ·
          refine ⟨8211604490130713250858905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5474402993420475500572603 8211604490130713250858905)
          ·
            refine ⟨6158703367598034938144179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8211604490130713250858905 6158703367598034938144179)
            ·
              refine ⟨9238055051397052407216269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6158703367598034938144179 9238055051397052407216269)
              ·
                refine ⟨3464270644273894652706101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9238055051397052407216269 3464270644273894652706101)
                ·
                  refine ⟨324775372900677623691197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3464270644273894652706101 324775372900677623691197)
                  ·
                    rfl

theorem cell22_2846240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_2846240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846240 prefixEnd_2846240 := by exact prefixLift 2846240
  have htrace : WordTrace (prefixWord ++ tailWord_2846240) baseStart_2846240 baseEnd_2846240 := by
    simpa [prefixWord, tailWord_2846240, baseEnd_2846240] using wordTrace_append hprefix tailTrace_2846240
  have hstable : (prefixWord ++ tailWord_2846240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846240).length < 2 ^ (prefixWord ++ tailWord_2846240).sum := by decide
  have hdescent : baseEnd_2846240 < baseStart_2846240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846298 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_2846298 : Nat := 118140960795 + 2846298 * 2 ^ 59
def prefixEnd_2846298 : Nat := 4983230072969 + 3 ^ 40 * 2846298 * 2
def baseEnd_2846298 : Nat := 974345973287340053123413

theorem tailTrace_2846298 : CollatzResearch.WordTrace tailWord_2846298 prefixEnd_2846298 974345973287340053123413 := by
  unfold tailWord_2846298
  simp only [CollatzResearch.WordTrace]
  refine ⟨25953254160588982460598887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69208677761570619894930365 25953254160588982460598887)
  ·
    refine ⟨38929881240883473690898331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25953254160588982460598887 38929881240883473690898331)
    ·
      refine ⟨58394821861325210536347497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38929881240883473690898331 58394821861325210536347497)
      ·
        refine ⟨43796116395993907902260623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58394821861325210536347497 43796116395993907902260623)
        ·
          refine ⟨65694174593990861853390935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43796116395993907902260623 65694174593990861853390935)
          ·
            refine ⟨98541261890986292780086403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65694174593990861853390935 98541261890986292780086403)
            ·
              refine ⟨147811892836479439170129605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98541261890986292780086403 147811892836479439170129605)
              ·
                refine ⟨27714729906839894844399301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147811892836479439170129605 27714729906839894844399301)
                ·
                  refine ⟨5196511857532480283324869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27714729906839894844399301 5196511857532480283324869)
                  ·
                    refine ⟨974345973287340053123413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5196511857532480283324869 974345973287340053123413)
                    ·
                      rfl

theorem cell22_2846298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_2846298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846298 prefixEnd_2846298 := by exact prefixLift 2846298
  have htrace : WordTrace (prefixWord ++ tailWord_2846298) baseStart_2846298 baseEnd_2846298 := by
    simpa [prefixWord, tailWord_2846298, baseEnd_2846298] using wordTrace_append hprefix tailTrace_2846298
  have hstable : (prefixWord ++ tailWord_2846298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846298).length < 2 ^ (prefixWord ++ tailWord_2846298).sum := by decide
  have hdescent : baseEnd_2846298 < baseStart_2846298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846300 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2846300 : Nat := 118140960795 + 2846300 * 2 ^ 59
def prefixEnd_2846300 : Nat := 4983230072969 + 3 ^ 40 * 2846300 * 2
def baseEnd_2846300 : Nat := 974346657928212714573407

theorem tailTrace_2846300 : CollatzResearch.WordTrace tailWord_2846300 prefixEnd_2846300 974346657928212714573407 := by
  unfold tailWord_2846300
  simp only [CollatzResearch.WordTrace]
  refine ⟨51906544794174342091984177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69208726392232456122645569 51906544794174342091984177)
  ·
    refine ⟨38929908595630756568988133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51906544794174342091984177 38929908595630756568988133)
    ·
      refine ⟨7299357861680766856685275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38929908595630756568988133 7299357861680766856685275)
      ·
        refine ⟨10949036792521150285027913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7299357861680766856685275 10949036792521150285027913)
        ·
          refine ⟨8211777594390862713770935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10949036792521150285027913 8211777594390862713770935)
          ·
            refine ⟨12317666391586294070656403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8211777594390862713770935 12317666391586294070656403)
            ·
              refine ⟨18476499587379441105984605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12317666391586294070656403 18476499587379441105984605)
              ·
                refine ⟨6928687345267290414744227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18476499587379441105984605 6928687345267290414744227)
                ·
                  refine ⟨10393031017900935622116341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6928687345267290414744227 10393031017900935622116341)
                  ·
                    refine ⟨974346657928212714573407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10393031017900935622116341 974346657928212714573407)
                    ·
                      rfl

theorem cell22_2846300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2846300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846300 prefixEnd_2846300 := by exact prefixLift 2846300
  have htrace : WordTrace (prefixWord ++ tailWord_2846300) baseStart_2846300 baseEnd_2846300 := by
    simpa [prefixWord, tailWord_2846300, baseEnd_2846300] using wordTrace_append hprefix tailTrace_2846300
  have hstable : (prefixWord ++ tailWord_2846300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846300).length < 2 ^ (prefixWord ++ tailWord_2846300).sum := by decide
  have hdescent : baseEnd_2846300 < baseStart_2846300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846345 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 3, 3]
def baseStart_2846345 : Nat := 118140960795 + 2846345 * 2 ^ 59
def prefixEnd_2846345 : Nat := 4983230072969 + 3 ^ 40 * 2846345 * 2
def baseEnd_2846345 : Nat := 974362062347847597198269

theorem tailTrace_2846345 : CollatzResearch.WordTrace tailWord_2846345 prefixEnd_2846345 974362062347847597198269 := by
  unfold tailWord_2846345
  simp only [CollatzResearch.WordTrace]
  refine ⟨103814730873185656869356489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69209820582123771246237659 103814730873185656869356489)
  ·
    refine ⟨77861048154889242652017367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103814730873185656869356489 77861048154889242652017367)
    ·
      refine ⟨116791572232333863978026051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77861048154889242652017367 116791572232333863978026051)
      ·
        refine ⟨175187358348500795967039077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116791572232333863978026051 175187358348500795967039077)
        ·
          refine ⟨32847629690343899243819827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175187358348500795967039077 32847629690343899243819827)
          ·
            refine ⟨49271444535515848865729741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32847629690343899243819827 49271444535515848865729741)
            ·
              refine ⟨18476791700818443324648653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49271444535515848865729741 18476791700818443324648653)
              ·
                refine ⟨6928796887806916246743245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18476791700818443324648653 6928796887806916246743245)
                ·
                  refine ⟨2598298832927593592528717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6928796887806916246743245 2598298832927593592528717)
                  ·
                    refine ⟨974362062347847597198269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598298832927593592528717 974362062347847597198269)
                    ·
                      rfl

theorem cell22_2846345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_2846345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846345 prefixEnd_2846345 := by exact prefixLift 2846345
  have htrace : WordTrace (prefixWord ++ tailWord_2846345) baseStart_2846345 baseEnd_2846345 := by
    simpa [prefixWord, tailWord_2846345, baseEnd_2846345] using wordTrace_append hprefix tailTrace_2846345
  have hstable : (prefixWord ++ tailWord_2846345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846345).length < 2 ^ (prefixWord ++ tailWord_2846345).sum := by decide
  have hdescent : baseEnd_2846345 < baseStart_2846345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846364 : List Nat := [2, 2, 3, 2, 4, 1, 2, 6]
def baseStart_2846364 : Nat := 118140960795 + 2846364 * 2 ^ 59
def prefixEnd_2846364 : Nat := 4983230072969 + 3 ^ 40 * 2846364 * 2
def baseEnd_2846364 : Nat := 108263174048459764552579

theorem tailTrace_2846364 : CollatzResearch.WordTrace tailWord_2846364 prefixEnd_2846364 108263174048459764552579 := by
  unfold tailWord_2846364
  simp only [CollatzResearch.WordTrace]
  refine ⟨51907711930058411557149073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69210282573411215409532097 51907711930058411557149073)
  ·
    refine ⟨38930783947543808667861805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51907711930058411557149073 38930783947543808667861805)
    ·
      refine ⟨14599043980328928250448177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38930783947543808667861805 14599043980328928250448177)
      ·
        refine ⟨10949282985246696187836133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14599043980328928250448177 10949282985246696187836133)
        ·
          refine ⟨2052990559733755535219275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10949282985246696187836133 2052990559733755535219275)
          ·
            refine ⟨3079485839600633302828913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052990559733755535219275 3079485839600633302828913)
            ·
              refine ⟨2309614379700474977121685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3079485839600633302828913 2309614379700474977121685)
              ·
                refine ⟨108263174048459764552579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2309614379700474977121685 108263174048459764552579)
                ·
                  rfl

theorem cell22_2846364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 6].length) (baseStart_2846364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846364 prefixEnd_2846364 := by exact prefixLift 2846364
  have htrace : WordTrace (prefixWord ++ tailWord_2846364) baseStart_2846364 baseEnd_2846364 := by
    simpa [prefixWord, tailWord_2846364, baseEnd_2846364] using wordTrace_append hprefix tailTrace_2846364
  have hstable : (prefixWord ++ tailWord_2846364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846364).length < 2 ^ (prefixWord ++ tailWord_2846364).sum := by decide
  have hdescent : baseEnd_2846364 < baseStart_2846364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846373 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_2846373 : Nat := 118140960795 + 2846373 * 2 ^ 59
def prefixEnd_2846373 : Nat := 4983230072969 + 3 ^ 40 * 2846373 * 2
def baseEnd_2846373 : Nat := 974371647320064857498183

theorem tailTrace_2846373 : CollatzResearch.WordTrace tailWord_2846373 prefixEnd_2846373 974371647320064857498183 := by
  unfold tailWord_2846373
  simp only [CollatzResearch.WordTrace]
  refine ⟨103815752117084217651375773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69210501411389478434250515 103815752117084217651375773)
  ·
    refine ⟨38930907043906581619265915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103815752117084217651375773 38930907043906581619265915)
    ·
      refine ⟨58396360565859872428898873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38930907043906581619265915 58396360565859872428898873)
      ·
        refine ⟨43797270424394904321674155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58396360565859872428898873 43797270424394904321674155)
        ·
          refine ⟨65695905636592356482511233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43797270424394904321674155 65695905636592356482511233)
          ·
            refine ⟨49271929227444267361883425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65695905636592356482511233 49271929227444267361883425)
            ·
              refine ⟨36953946920583200521412569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49271929227444267361883425 36953946920583200521412569)
              ·
                refine ⟨27715460190437400391059427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36953946920583200521412569 27715460190437400391059427)
                ·
                  refine ⟨41573190285656100586589141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27715460190437400391059427 41573190285656100586589141)
                  ·
                    refine ⟨974371647320064857498183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41573190285656100586589141 974371647320064857498183)
                    ·
                      rfl

theorem cell22_2846373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_2846373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846373 prefixEnd_2846373 := by exact prefixLift 2846373
  have htrace : WordTrace (prefixWord ++ tailWord_2846373) baseStart_2846373 baseEnd_2846373 := by
    simpa [prefixWord, tailWord_2846373, baseEnd_2846373] using wordTrace_append hprefix tailTrace_2846373
  have hstable : (prefixWord ++ tailWord_2846373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846373).length < 2 ^ (prefixWord ++ tailWord_2846373).sum := by decide
  have hdescent : baseEnd_2846373 < baseStart_2846373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846396 : List Nat := [2, 2, 2, 3, 1, 3, 3, 2, 1, 3]
def baseStart_2846396 : Nat := 118140960795 + 2846396 * 2 ^ 59
def prefixEnd_2846396 : Nat := 4983230072969 + 3 ^ 40 * 2846396 * 2
def baseEnd_2846396 : Nat := 974379520690100464173113

theorem tailTrace_2846396 : CollatzResearch.WordTrace tailWord_2846396 prefixEnd_2846396 974379520690100464173113 := by
  unfold tailWord_2846396
  simp only [CollatzResearch.WordTrace]
  refine ⟨51908295498000446289731521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69211060664000595052975361 51908295498000446289731521)
  ·
    refine ⟨38931221623500334717298641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51908295498000446289731521 38931221623500334717298641)
    ·
      refine ⟨29198416217625251037973981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38931221623500334717298641 29198416217625251037973981)
      ·
        refine ⟨10949406081609469139240243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29198416217625251037973981 10949406081609469139240243)
        ·
          refine ⟨16424109122414203708860365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10949406081609469139240243 16424109122414203708860365)
          ·
            refine ⟨6159040920905326390822637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16424109122414203708860365 6159040920905326390822637)
            ·
              refine ⟨2309640345339497396558489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6159040920905326390822637 2309640345339497396558489)
              ·
                refine ⟨1732230259004623047418867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2309640345339497396558489 1732230259004623047418867)
                ·
                  refine ⟨2598345388506934571128301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732230259004623047418867 2598345388506934571128301)
                  ·
                    refine ⟨974379520690100464173113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598345388506934571128301 974379520690100464173113)
                    ·
                      rfl

theorem cell22_2846396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_2846396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846396 prefixEnd_2846396 := by exact prefixLift 2846396
  have htrace : WordTrace (prefixWord ++ tailWord_2846396) baseStart_2846396 baseEnd_2846396 := by
    simpa [prefixWord, tailWord_2846396, baseEnd_2846396] using wordTrace_append hprefix tailTrace_2846396
  have hstable : (prefixWord ++ tailWord_2846396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846396).length < 2 ^ (prefixWord ++ tailWord_2846396).sum := by decide
  have hdescent : baseEnd_2846396 < baseStart_2846396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846402 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2846402 : Nat := 118140960795 + 2846402 * 2 ^ 59
def prefixEnd_2846402 : Nat := 4983230072969 + 3 ^ 40 * 2846402 * 2
def baseEnd_2846402 : Nat := 974381574612718448523095

theorem tailTrace_2846402 : CollatzResearch.WordTrace tailWord_2846402 prefixEnd_2846402 974381574612718448523095 := by
  unfold tailWord_2846402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25954202458494788901045365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69211206555986103736120973 25954202458494788901045365)
  ·
    refine ⟨2433206480483886459473003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25954202458494788901045365 2433206480483886459473003)
    ·
      refine ⟨3649809720725829689209505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2433206480483886459473003 3649809720725829689209505)
      ·
        refine ⟨2737357290544372266907129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3649809720725829689209505 2737357290544372266907129)
        ·
          refine ⟨2053017967908279200180347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2737357290544372266907129 2053017967908279200180347)
          ·
            refine ⟨3079526951862418800270521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053017967908279200180347 3079526951862418800270521)
            ·
              refine ⟨2309645213896814100202891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3079526951862418800270521 2309645213896814100202891)
              ·
                refine ⟨3464467820845221150304337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2309645213896814100202891 3464467820845221150304337)
                ·
                  refine ⟨2598350865633915862728253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3464467820845221150304337 2598350865633915862728253)
                  ·
                    refine ⟨974381574612718448523095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598350865633915862728253 974381574612718448523095)
                    ·
                      rfl

theorem cell22_2846402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2846402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846402 prefixEnd_2846402 := by exact prefixLift 2846402
  have htrace : WordTrace (prefixWord ++ tailWord_2846402) baseStart_2846402 baseEnd_2846402 := by
    simpa [prefixWord, tailWord_2846402, baseEnd_2846402] using wordTrace_append hprefix tailTrace_2846402
  have hstable : (prefixWord ++ tailWord_2846402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846402).length < 2 ^ (prefixWord ++ tailWord_2846402).sum := by decide
  have hdescent : baseEnd_2846402 < baseStart_2846402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846437 : List Nat := [1, 3, 1, 4, 1, 1, 2, 5, 4]
def baseStart_2846437 : Nat := 118140960795 + 2846437 * 2 ^ 59
def prefixEnd_2846437 : Nat := 4983230072969 + 3 ^ 40 * 2846437 * 2
def baseEnd_2846437 : Nat := 324797851942663341299329

theorem tailTrace_2846437 : CollatzResearch.WordTrace tailWord_2846437 prefixEnd_2846437 324797851942663341299329 := by
  unfold tailWord_2846437
  simp only [CollatzResearch.WordTrace]
  refine ⟨103818086388852356581705565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69212057592568237721137043 103818086388852356581705565)
  ·
    refine ⟨38931782395819633718139587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103818086388852356581705565 38931782395819633718139587)
    ·
      refine ⟨58397673593729450577209381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38931782395819633718139587 58397673593729450577209381)
      ·
        refine ⟨10949563798824271983226759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58397673593729450577209381 10949563798824271983226759)
        ·
          refine ⟨16424345698236407974840139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10949563798824271983226759 16424345698236407974840139)
          ·
            refine ⟨24636518547354611962260209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16424345698236407974840139 24636518547354611962260209)
            ·
              refine ⟨18477388910515958971695157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24636518547354611962260209 18477388910515958971695157)
              ·
                refine ⟨1732255210360871153596421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18477388910515958971695157 1732255210360871153596421)
                ·
                  refine ⟨324797851942663341299329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732255210360871153596421 324797851942663341299329)
                  ·
                    rfl

theorem cell22_2846437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_2846437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846437 prefixEnd_2846437 := by exact prefixLift 2846437
  have htrace : WordTrace (prefixWord ++ tailWord_2846437) baseStart_2846437 baseEnd_2846437 := by
    simpa [prefixWord, tailWord_2846437, baseEnd_2846437] using wordTrace_append hprefix tailTrace_2846437
  have hstable : (prefixWord ++ tailWord_2846437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846437).length < 2 ^ (prefixWord ++ tailWord_2846437).sum := by decide
  have hdescent : baseEnd_2846437 < baseStart_2846437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846454 : List Nat := [5, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_2846454 : Nat := 118140960795 + 2846454 * 2 ^ 59
def prefixEnd_2846454 : Nat := 4983230072969 + 3 ^ 40 * 2846454 * 2
def baseEnd_2846454 : Nat := 324799791758469215407645

theorem tailTrace_2846454 : CollatzResearch.WordTrace tailWord_2846454 prefixEnd_2846454 324799791758469215407645 := by
  unfold tailWord_2846454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6488669151861923030317151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69212470953193845656716277 6488669151861923030317151)
  ·
    refine ⟨9733003727792884545475727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6488669151861923030317151 9733003727792884545475727)
    ·
      refine ⟨14599505591689326818213591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9733003727792884545475727 14599505591689326818213591)
      ·
        refine ⟨21899258387533990227320387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14599505591689326818213591 21899258387533990227320387)
        ·
          refine ⟨32848887581300985340980581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21899258387533990227320387 32848887581300985340980581)
          ·
            refine ⟨6159166421493934751433859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32848887581300985340980581 6159166421493934751433859)
            ·
              refine ⟨9238749632240902127150789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6159166421493934751433859 9238749632240902127150789)
              ·
                refine ⟨1732265556045169148840773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9238749632240902127150789 1732265556045169148840773)
                ·
                  refine ⟨324799791758469215407645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732265556045169148840773 324799791758469215407645)
                  ·
                    rfl

theorem cell22_2846454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_2846454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846454 prefixEnd_2846454 := by exact prefixLift 2846454
  have htrace : WordTrace (prefixWord ++ tailWord_2846454) baseStart_2846454 baseEnd_2846454 := by
    simpa [prefixWord, tailWord_2846454, baseEnd_2846454] using wordTrace_append hprefix tailTrace_2846454
  have hstable : (prefixWord ++ tailWord_2846454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846454).length < 2 ^ (prefixWord ++ tailWord_2846454).sum := by decide
  have hdescent : baseEnd_2846454 < baseStart_2846454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846465 : List Nat := [1, 2, 4, 1, 1, 1, 5, 7]
def baseStart_2846465 : Nat := 118140960795 + 2846465 * 2 ^ 59
def prefixEnd_2846465 : Nat := 4983230072969 + 3 ^ 40 * 2846465 * 2
def baseEnd_2846465 : Nat := 108267015644467476021989

theorem tailTrace_2846465 : CollatzResearch.WordTrace tailWord_2846465 prefixEnd_2846465 108267015644467476021989 := by
  unfold tailWord_2846465
  simp only [CollatzResearch.WordTrace]
  refine ⟨103819107632750917363724849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69212738421833944909149899 103819107632750917363724849)
  ·
    refine ⟨77864330724563188022793637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103819107632750917363724849 77864330724563188022793637)
    ·
      refine ⟨14599562010855597754273807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77864330724563188022793637 14599562010855597754273807)
      ·
        refine ⟨21899343016283396631410711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14599562010855597754273807 21899343016283396631410711)
        ·
          refine ⟨32849014524425094947116067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21899343016283396631410711 32849014524425094947116067)
          ·
            refine ⟨49273521786637642420674101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32849014524425094947116067 49273521786637642420674101)
            ·
              refine ⟨4619392667497278976938197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49273521786637642420674101 4619392667497278976938197)
              ·
                refine ⟨108267015644467476021989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4619392667497278976938197 108267015644467476021989)
                ·
                  rfl

theorem cell22_2846465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 7].length) (baseStart_2846465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846465 prefixEnd_2846465 := by exact prefixLift 2846465
  have htrace : WordTrace (prefixWord ++ tailWord_2846465) baseStart_2846465 baseEnd_2846465 := by
    simpa [prefixWord, tailWord_2846465, baseEnd_2846465] using wordTrace_append hprefix tailTrace_2846465
  have hstable : (prefixWord ++ tailWord_2846465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846465).length < 2 ^ (prefixWord ++ tailWord_2846465).sum := by decide
  have hdescent : baseEnd_2846465 < baseStart_2846465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846514 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_2846514 : Nat := 118140960795 + 2846514 * 2 ^ 59
def prefixEnd_2846514 : Nat := 4983230072969 + 3 ^ 40 * 2846514 * 2
def baseEnd_2846514 : Nat := 974419914501587489722751

theorem tailTrace_2846514 : CollatzResearch.WordTrace tailWord_2846514 prefixEnd_2846514 974419914501587489722751 := by
  unfold tailWord_2846514
  simp only [CollatzResearch.WordTrace]
  refine ⟨25955223702393349683064649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69213929873048932488172397 25955223702393349683064649)
  ·
    refine ⟨19466417776795012262298487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25955223702393349683064649 19466417776795012262298487)
    ·
      refine ⟨29199626665192518393447731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19466417776795012262298487 29199626665192518393447731)
      ·
        refine ⟨43799439997788777590171597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29199626665192518393447731 43799439997788777590171597)
        ·
          refine ⟨16424789999170791596314349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43799439997788777590171597 16424789999170791596314349)
          ·
            refine ⟨6159296249689046848617881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16424789999170791596314349 6159296249689046848617881)
            ·
              refine ⟨4619472187266785136463411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6159296249689046848617881 4619472187266785136463411)
              ·
                refine ⟨6929208280900177704695117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619472187266785136463411 6929208280900177704695117)
                ·
                  refine ⟨2598453105337566639260669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6929208280900177704695117 2598453105337566639260669)
                  ·
                    refine ⟨974419914501587489722751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598453105337566639260669 974419914501587489722751)
                    ·
                      rfl

theorem cell22_2846514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_2846514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846514 prefixEnd_2846514 := by exact prefixLift 2846514
  have htrace : WordTrace (prefixWord ++ tailWord_2846514) baseStart_2846514 baseEnd_2846514 := by
    simpa [prefixWord, tailWord_2846514, baseEnd_2846514] using wordTrace_append hprefix tailTrace_2846514
  have hstable : (prefixWord ++ tailWord_2846514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846514).length < 2 ^ (prefixWord ++ tailWord_2846514).sum := by decide
  have hdescent : baseEnd_2846514 < baseStart_2846514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846548 : List Nat := [2, 4, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_2846548 : Nat := 118140960795 + 2846548 * 2 ^ 59
def prefixEnd_2846548 : Nat := 4983230072969 + 3 ^ 40 * 2846548 * 2
def baseEnd_2846548 : Nat := 974431553396422734372647

theorem tailTrace_2846548 : CollatzResearch.WordTrace tailWord_2846548 prefixEnd_2846548 974431553396422734372647 := by
  unfold tailWord_2846548
  simp only [CollatzResearch.WordTrace]
  refine ⟨51911067445725111269498149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69214756594300148359330865 51911067445725111269498149)
  ·
    refine ⟨9733325146073458363030903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51911067445725111269498149 9733325146073458363030903)
    ·
      refine ⟨14599987719110187544546355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9733325146073458363030903 14599987719110187544546355)
      ·
        refine ⟨21899981578665281316819533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14599987719110187544546355 21899981578665281316819533)
        ·
          refine ⟨8212493091999480493807325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21899981578665281316819533 8212493091999480493807325)
          ·
            refine ⟨3079684909499805185177747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8212493091999480493807325 3079684909499805185177747)
            ·
              refine ⟨4619527364249707777766621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079684909499805185177747 4619527364249707777766621)
              ·
                refine ⟨1732322761593640416662483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4619527364249707777766621 1732322761593640416662483)
                ·
                  refine ⟨2598484142390460624993725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732322761593640416662483 2598484142390460624993725)
                  ·
                    refine ⟨974431553396422734372647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598484142390460624993725 974431553396422734372647)
                    ·
                      rfl

theorem cell22_2846548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_2846548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846548 prefixEnd_2846548 := by exact prefixLift 2846548
  have htrace : WordTrace (prefixWord ++ tailWord_2846548) baseStart_2846548 baseEnd_2846548 := by
    simpa [prefixWord, tailWord_2846548, baseEnd_2846548] using wordTrace_append hprefix tailTrace_2846548
  have hstable : (prefixWord ++ tailWord_2846548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846548).length < 2 ^ (prefixWord ++ tailWord_2846548).sum := by decide
  have hdescent : baseEnd_2846548 < baseStart_2846548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846572 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 6]
def baseStart_2846572 : Nat := 118140960795 + 2846572 * 2 ^ 59
def prefixEnd_2846572 : Nat := 4983230072969 + 3 ^ 40 * 2846572 * 2
def baseEnd_2846572 : Nat := 324813256362298223924191

theorem tailTrace_2846572 : CollatzResearch.WordTrace tailWord_2846572 prefixEnd_2846572 324813256362298223924191 := by
  unfold tailWord_2846572
  simp only [CollatzResearch.WordTrace]
  refine ⟨51911505121681637318934985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69215340162242183091913313 51911505121681637318934985)
  ·
    refine ⟨38933628841261227989201239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51911505121681637318934985 38933628841261227989201239)
    ·
      refine ⟨58400443261891841983801859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38933628841261227989201239 58400443261891841983801859)
      ·
        refine ⟨87600664892837762975702789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58400443261891841983801859 87600664892837762975702789)
        ·
          refine ⟨16425124667407080557944273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87600664892837762975702789 16425124667407080557944273)
          ·
            refine ⟨12318843500555310418458205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16425124667407080557944273 12318843500555310418458205)
            ·
              refine ⟨4619566312708241406921827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12318843500555310418458205 4619566312708241406921827)
              ·
                refine ⟨6929349469062362110382741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619566312708241406921827 6929349469062362110382741)
                ·
                  refine ⟨324813256362298223924191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6929349469062362110382741 324813256362298223924191)
                  ·
                    rfl

theorem cell22_2846572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_2846572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846572 prefixEnd_2846572 := by exact prefixLift 2846572
  have htrace : WordTrace (prefixWord ++ tailWord_2846572) baseStart_2846572 baseEnd_2846572 := by
    simpa [prefixWord, tailWord_2846572, baseEnd_2846572] using wordTrace_append hprefix tailTrace_2846572
  have hstable : (prefixWord ++ tailWord_2846572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846572).length < 2 ^ (prefixWord ++ tailWord_2846572).sum := by decide
  have hdescent : baseEnd_2846572 < baseStart_2846572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846621 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_2846621 : Nat := 118140960795 + 2846621 * 2 ^ 59
def prefixEnd_2846621 : Nat := 4983230072969 + 3 ^ 40 * 2846621 * 2
def baseEnd_2846621 : Nat := 974456542788274877297423

theorem tailTrace_2846621 : CollatzResearch.WordTrace tailWord_2846621 prefixEnd_2846621 974456542788274877297423 := by
  unfold tailWord_2846621
  simp only [CollatzResearch.WordTrace]
  refine ⟨103824797420185756006403717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69216531613457170670935811 103824797420185756006403717)
  ·
    refine ⟨19467149516284829251200697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103824797420185756006403717 19467149516284829251200697)
    ·
      refine ⟨14600362137213621938400523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19467149516284829251200697 14600362137213621938400523)
      ·
        refine ⟨21900543205820432907600785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14600362137213621938400523 21900543205820432907600785)
        ·
          refine ⟨16425407404365324680700589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21900543205820432907600785 16425407404365324680700589)
          ·
            refine ⟨6159527776636996755262721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16425407404365324680700589 6159527776636996755262721)
            ·
              refine ⟨4619645832477747566447041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6159527776636996755262721 4619645832477747566447041)
              ·
                refine ⟨3464734374358310674835281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4619645832477747566447041 3464734374358310674835281)
                ·
                  refine ⟨2598550780768733006126461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3464734374358310674835281 2598550780768733006126461)
                  ·
                    refine ⟨974456542788274877297423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598550780768733006126461 974456542788274877297423)
                    ·
                      rfl

theorem cell22_2846621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_2846621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846621 prefixEnd_2846621 := by exact prefixLift 2846621
  have htrace : WordTrace (prefixWord ++ tailWord_2846621) baseStart_2846621 baseEnd_2846621 := by
    simpa [prefixWord, tailWord_2846621, baseEnd_2846621] using wordTrace_append hprefix tailTrace_2846621
  have hstable : (prefixWord ++ tailWord_2846621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846621).length < 2 ^ (prefixWord ++ tailWord_2846621).sum := by decide
  have hdescent : baseEnd_2846621 < baseStart_2846621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846623 : List Nat := [1, 1, 2, 5, 3, 2, 2, 2, 4]
def baseStart_2846623 : Nat := 118140960795 + 2846623 * 2 ^ 59
def prefixEnd_2846623 : Nat := 4983230072969 + 3 ^ 40 * 2846623 * 2
def baseEnd_2846623 : Nat := 324819075809715846249139

theorem tailTrace_2846623 : CollatzResearch.WordTrace tailWord_2846623 prefixEnd_2846623 324819075809715846249139 := by
  unfold tailWord_2846623
  simp only [CollatzResearch.WordTrace]
  refine ⟨103824870366178510347976523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69216580244119006898651015 103824870366178510347976523)
  ·
    refine ⟨155737305549267765521964785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103824870366178510347976523 155737305549267765521964785)
    ·
      refine ⟨116802979161950824141473589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155737305549267765521964785 116802979161950824141473589)
      ·
        refine ⟨10950279296432889763263149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116802979161950824141473589 10950279296432889763263149)
        ·
          refine ⟨4106354736162333661223681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10950279296432889763263149 4106354736162333661223681)
          ·
            refine ⟨3079766052121750245917761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4106354736162333661223681 3079766052121750245917761)
            ·
              refine ⟨2309824539091312684438321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3079766052121750245917761 2309824539091312684438321)
              ·
                refine ⟨1732368404318484513328741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2309824539091312684438321 1732368404318484513328741)
                ·
                  refine ⟨324819075809715846249139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732368404318484513328741 324819075809715846249139)
                  ·
                    rfl

theorem cell22_2846623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 4].length) (baseStart_2846623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846623 prefixEnd_2846623 := by exact prefixLift 2846623
  have htrace : WordTrace (prefixWord ++ tailWord_2846623) baseStart_2846623 baseEnd_2846623 := by
    simpa [prefixWord, tailWord_2846623, baseEnd_2846623] using wordTrace_append hprefix tailTrace_2846623
  have hstable : (prefixWord ++ tailWord_2846623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846623).length < 2 ^ (prefixWord ++ tailWord_2846623).sum := by decide
  have hdescent : baseEnd_2846623 < baseStart_2846623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846649 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 3, 3]
def baseStart_2846649 : Nat := 118140960795 + 2846649 * 2 ^ 59
def prefixEnd_2846649 : Nat := 4983230072969 + 3 ^ 40 * 2846649 * 2
def baseEnd_2846649 : Nat := 974466127760492137597337

theorem tailTrace_2846649 : CollatzResearch.WordTrace tailWord_2846649 prefixEnd_2846649 974466127760492137597337 := by
  unfold tailWord_2846649
  simp only [CollatzResearch.WordTrace]
  refine ⟨103825818664084316788423001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69217212442722877858948667 103825818664084316788423001)
  ·
    refine ⟨77869363998063237591317251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103825818664084316788423001 77869363998063237591317251)
    ·
      refine ⟨116804045997094856386975877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77869363998063237591317251 116804045997094856386975877)
      ·
        refine ⟨21900758624455285572557977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116804045997094856386975877 21900758624455285572557977)
        ·
          refine ⟨16425568968341464179418483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21900758624455285572557977 16425568968341464179418483)
          ·
            refine ⟨24638353452512196269127725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16425568968341464179418483 24638353452512196269127725)
            ·
              refine ⟨9239382544692073600922897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24638353452512196269127725 9239382544692073600922897)
              ·
                refine ⟨6929536908519055200692173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9239382544692073600922897 6929536908519055200692173)
                ·
                  refine ⟨2598576340694645700259565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6929536908519055200692173 2598576340694645700259565)
                  ·
                    refine ⟨974466127760492137597337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598576340694645700259565 974466127760492137597337)
                    ·
                      rfl

theorem cell22_2846649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_2846649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846649 prefixEnd_2846649 := by exact prefixLift 2846649
  have htrace : WordTrace (prefixWord ++ tailWord_2846649) baseStart_2846649 baseEnd_2846649 := by
    simpa [prefixWord, tailWord_2846649, baseEnd_2846649] using wordTrace_append hprefix tailTrace_2846649
  have hstable : (prefixWord ++ tailWord_2846649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846649).length < 2 ^ (prefixWord ++ tailWord_2846649).sum := by decide
  have hdescent : baseEnd_2846649 < baseStart_2846649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846666 : List Nat := [3, 1, 2, 1, 2, 1, 3, 5, 1, 3]
def baseStart_2846666 : Nat := 118140960795 + 2846666 * 2 ^ 59
def prefixEnd_2846666 : Nat := 4983230072969 + 3 ^ 40 * 2846666 * 2
def baseEnd_2846666 : Nat := 974471947207909759922285

theorem tailTrace_2846666 : CollatzResearch.WordTrace tailWord_2846666 prefixEnd_2846666 974471947207909759922285 := by
  unfold tailWord_2846666
  simp only [CollatzResearch.WordTrace]
  refine ⟨25956609676255682172947963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69217625803348485794527901 25956609676255682172947963)
  ·
    refine ⟨38934914514383523259421945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25956609676255682172947963 38934914514383523259421945)
    ·
      refine ⟨29201185885787642444566459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38934914514383523259421945 29201185885787642444566459)
      ·
        refine ⟨43801778828681463666849689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29201185885787642444566459 43801778828681463666849689)
        ·
          refine ⟨32851334121511097750137267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43801778828681463666849689 32851334121511097750137267)
          ·
            refine ⟨49277001182266646625205901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32851334121511097750137267 49277001182266646625205901)
            ·
              refine ⟨18478875443349992484452213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49277001182266646625205901 18478875443349992484452213)
              ·
                refine ⟨1732394572814061795417395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18478875443349992484452213 1732394572814061795417395)
                ·
                  refine ⟨2598591859221092693126093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732394572814061795417395 2598591859221092693126093)
                  ·
                    refine ⟨974471947207909759922285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598591859221092693126093 974471947207909759922285)
                    ·
                      rfl

theorem cell22_2846666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_2846666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846666 prefixEnd_2846666 := by exact prefixLift 2846666
  have htrace : WordTrace (prefixWord ++ tailWord_2846666) baseStart_2846666 baseEnd_2846666 := by
    simpa [prefixWord, tailWord_2846666, baseEnd_2846666] using wordTrace_append hprefix tailTrace_2846666
  have hstable : (prefixWord ++ tailWord_2846666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846666).length < 2 ^ (prefixWord ++ tailWord_2846666).sum := by decide
  have hdescent : baseEnd_2846666 < baseStart_2846666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846739 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 4, 3]
def baseStart_2846739 : Nat := 118140960795 + 2846739 * 2 ^ 59
def prefixEnd_2846739 : Nat := 4983230072969 + 3 ^ 40 * 2846739 * 2
def baseEnd_2846739 : Nat := 974496936599761902847061

theorem tailTrace_2846739 : CollatzResearch.WordTrace tailWord_2846739 prefixEnd_2846739 974496936599761902847061 := by
  unfold tailWord_2846739
  simp only [CollatzResearch.WordTrace]
  refine ⟨103829101233758262159199271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69219400822505508106132847 103829101233758262159199271)
  ·
    refine ⟨155743651850637393238798907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103829101233758262159199271 155743651850637393238798907)
    ·
      refine ⟨233615477775956089858198361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155743651850637393238798907 233615477775956089858198361)
      ·
        refine ⟨175211608331967067393648771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233615477775956089858198361 175211608331967067393648771)
        ·
          refine ⟨262817412497950601090473157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175211608331967067393648771 262817412497950601090473157)
          ·
            refine ⟨49278264843365737704463717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262817412497950601090473157 49278264843365737704463717)
            ·
              refine ⟨9239674658131075819586947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49278264843365737704463717 9239674658131075819586947)
              ·
                refine ⟨13859511987196613729380421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9239674658131075819586947 13859511987196613729380421)
                ·
                  refine ⟨2598658497599365074258829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13859511987196613729380421 2598658497599365074258829)
                  ·
                    refine ⟨974496936599761902847061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598658497599365074258829 974496936599761902847061)
                    ·
                      rfl

theorem cell22_2846739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 3].length) (baseStart_2846739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846739 prefixEnd_2846739 := by exact prefixLift 2846739
  have htrace : WordTrace (prefixWord ++ tailWord_2846739) baseStart_2846739 baseEnd_2846739 := by
    simpa [prefixWord, tailWord_2846739, baseEnd_2846739] using wordTrace_append hprefix tailTrace_2846739
  have hstable : (prefixWord ++ tailWord_2846739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846739).length < 2 ^ (prefixWord ++ tailWord_2846739).sum := by decide
  have hdescent : baseEnd_2846739 < baseStart_2846739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846741 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 6]
def baseStart_2846741 : Nat := 118140960795 + 2846741 * 2 ^ 59
def prefixEnd_2846741 : Nat := 4983230072969 + 3 ^ 40 * 2846741 * 2
def baseEnd_2846741 : Nat := 324832540413544854765685

theorem tailTrace_2846741 : CollatzResearch.WordTrace tailWord_2846741 prefixEnd_2846741 324832540413544854765685 := by
  unfold tailWord_2846741
  simp only [CollatzResearch.WordTrace]
  refine ⟨103829174179751016500772077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69219449453167344333848051 103829174179751016500772077)
  ·
    refine ⟨38935940317406631187789529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103829174179751016500772077 38935940317406631187789529)
    ·
      refine ⟨29201955238054973390842147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38935940317406631187789529 29201955238054973390842147)
      ·
        refine ⟨43802932857082460086263221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29201955238054973390842147 43802932857082460086263221)
        ·
          refine ⟨4106524955351480633087177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43802932857082460086263221 4106524955351480633087177)
          ·
            refine ⟨3079893716513610474815383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4106524955351480633087177 3079893716513610474815383)
            ·
              refine ⟨4619840574770415712223075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079893716513610474815383 4619840574770415712223075)
              ·
                refine ⟨6929760862155623568334613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619840574770415712223075 6929760862155623568334613)
                ·
                  refine ⟨324832540413544854765685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6929760862155623568334613 324832540413544854765685)
                  ·
                    rfl

theorem cell22_2846741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_2846741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846741 prefixEnd_2846741 := by exact prefixLift 2846741
  have htrace : WordTrace (prefixWord ++ tailWord_2846741) baseStart_2846741 baseEnd_2846741 := by
    simpa [prefixWord, tailWord_2846741, baseEnd_2846741] using wordTrace_append hprefix tailTrace_2846741
  have hstable : (prefixWord ++ tailWord_2846741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846741).length < 2 ^ (prefixWord ++ tailWord_2846741).sum := by decide
  have hdescent : baseEnd_2846741 < baseStart_2846741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846754 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2846754 : Nat := 118140960795 + 2846754 * 2 ^ 59
def prefixEnd_2846754 : Nat := 4983230072969 + 3 ^ 40 * 2846754 * 2
def baseEnd_2846754 : Nat := 974502071406306863722015

theorem tailTrace_2846754 : CollatzResearch.WordTrace tailWord_2846754 prefixEnd_2846754 974502071406306863722015 := by
  unfold tailWord_2846754
  simp only [CollatzResearch.WordTrace]
  refine ⟨25957412082175979930248829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69219765552469279813996877 25957412082175979930248829)
  ·
    refine ⟨9734029530815992473843311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25957412082175979930248829 9734029530815992473843311)
    ·
      refine ⟨14601044296223988710764967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9734029530815992473843311 14601044296223988710764967)
      ·
        refine ⟨21901566444335983066147451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14601044296223988710764967 21901566444335983066147451)
        ·
          refine ⟨32852349666503974599221177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21901566444335983066147451 32852349666503974599221177)
          ·
            refine ⟨24639262249877980949415883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32852349666503974599221177 24639262249877980949415883)
            ·
              refine ⟨36958893374816971424123825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24639262249877980949415883 36958893374816971424123825)
              ·
                refine ⟨27719170031112728568092869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36958893374816971424123825 27719170031112728568092869)
                ·
                  refine ⟨5197344380833636606517413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27719170031112728568092869 5197344380833636606517413)
                  ·
                    refine ⟨974502071406306863722015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5197344380833636606517413 974502071406306863722015)
                    ·
                      rfl

theorem cell22_2846754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2846754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846754 prefixEnd_2846754 := by exact prefixLift 2846754
  have htrace : WordTrace (prefixWord ++ tailWord_2846754) baseStart_2846754 baseEnd_2846754 := by
    simpa [prefixWord, tailWord_2846754, baseEnd_2846754] using wordTrace_append hprefix tailTrace_2846754
  have hstable : (prefixWord ++ tailWord_2846754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846754).length < 2 ^ (prefixWord ++ tailWord_2846754).sum := by decide
  have hdescent : baseEnd_2846754 < baseStart_2846754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846760 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2846760 : Nat := 118140960795 + 2846760 * 2 ^ 59
def prefixEnd_2846760 : Nat := 4983230072969 + 3 ^ 40 * 2846760 * 2
def baseEnd_2846760 : Nat := 974504125328924848071997

theorem tailTrace_2846760 : CollatzResearch.WordTrace tailWord_2846760 prefixEnd_2846760 974504125328924848071997 := by
  unfold tailWord_2846760
  simp only [CollatzResearch.WordTrace]
  refine ⟨51914933583341091372856867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69219911444454788497142489 51914933583341091372856867)
  ·
    refine ⟨77872400375011637059285301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51914933583341091372856867 77872400375011637059285301)
    ·
      refine ⟨7300537535157340974307997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77872400375011637059285301 7300537535157340974307997)
      ·
        refine ⟨2737701575684002865365499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7300537535157340974307997 2737701575684002865365499)
        ·
          refine ⟨4106552363526004298048249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737701575684002865365499 4106552363526004298048249)
          ·
            refine ⟨3079914272644503223536187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4106552363526004298048249 3079914272644503223536187)
            ·
              refine ⟨4619871408966754835304281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079914272644503223536187 4619871408966754835304281)
              ·
                refine ⟨3464903556725066126478211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4619871408966754835304281 3464903556725066126478211)
                ·
                  refine ⟨5197355335087599189717317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464903556725066126478211 5197355335087599189717317)
                  ·
                    refine ⟨974504125328924848071997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5197355335087599189717317 974504125328924848071997)
                    ·
                      rfl

theorem cell22_2846760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2846760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846760 prefixEnd_2846760 := by exact prefixLift 2846760
  have htrace : WordTrace (prefixWord ++ tailWord_2846760) baseStart_2846760 baseEnd_2846760 := by
    simpa [prefixWord, tailWord_2846760, baseEnd_2846760] using wordTrace_append hprefix tailTrace_2846760
  have hstable : (prefixWord ++ tailWord_2846760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846760).length < 2 ^ (prefixWord ++ tailWord_2846760).sum := by decide
  have hdescent : baseEnd_2846760 < baseStart_2846760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846790 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2846790 : Nat := 118140960795 + 2846790 * 2 ^ 59
def prefixEnd_2846790 : Nat := 4983230072969 + 3 ^ 40 * 2846790 * 2
def baseEnd_2846790 : Nat := 974514394942014769821905

theorem tailTrace_2846790 : CollatzResearch.WordTrace tailWord_2846790 prefixEnd_2846790 974514394942014769821905 := by
  unfold tailWord_2846790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244717542392921808415807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69220640904382331912870549 3244717542392921808415807)
  ·
    refine ⟨4867076313589382712623711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3244717542392921808415807 4867076313589382712623711)
    ·
      refine ⟨7300614470384074068935567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4867076313589382712623711 7300614470384074068935567)
      ·
        refine ⟨10950921705576111103403351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7300614470384074068935567 10950921705576111103403351)
        ·
          refine ⟨16426382558364166655105027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10950921705576111103403351 16426382558364166655105027)
          ·
            refine ⟨24639573837546249982657541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16426382558364166655105027 24639573837546249982657541)
            ·
              refine ⟨4619920094539921871748289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24639573837546249982657541 4619920094539921871748289)
              ·
                refine ⟨3464940070904941403811217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4619920094539921871748289 3464940070904941403811217)
                ·
                  refine ⟨2598705053178706052858413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3464940070904941403811217 2598705053178706052858413)
                  ·
                    refine ⟨974514394942014769821905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598705053178706052858413 974514394942014769821905)
                    ·
                      rfl

theorem cell22_2846790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2846790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846790 prefixEnd_2846790 := by exact prefixLift 2846790
  have htrace : WordTrace (prefixWord ++ tailWord_2846790) baseStart_2846790 baseEnd_2846790 := by
    simpa [prefixWord, tailWord_2846790, baseEnd_2846790] using wordTrace_append hprefix tailTrace_2846790
  have hstable : (prefixWord ++ tailWord_2846790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846790).length < 2 ^ (prefixWord ++ tailWord_2846790).sum := by decide
  have hdescent : baseEnd_2846790 < baseStart_2846790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846829 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2846829 : Nat := 118140960795 + 2846829 * 2 ^ 59
def prefixEnd_2846829 : Nat := 4983230072969 + 3 ^ 40 * 2846829 * 2
def baseEnd_2846829 : Nat := 974527745439031668096785

theorem tailTrace_2846829 : CollatzResearch.WordTrace tailWord_2846829 prefixEnd_2846829 974527745439031668096785 := by
  unfold tailWord_2846829
  simp only [CollatzResearch.WordTrace]
  refine ⟨103832383803432207529975541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69221589202288138353317027 103832383803432207529975541)
  ·
    refine ⟨9734285981571769455935207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103832383803432207529975541 9734285981571769455935207)
    ·
      refine ⟨14601428972357654183902811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9734285981571769455935207 14601428972357654183902811)
      ·
        refine ⟨21902143458536481275854217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14601428972357654183902811 21902143458536481275854217)
        ·
          refine ⟨16426607593902360956890663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21902143458536481275854217 16426607593902360956890663)
          ·
            refine ⟨24639911390853541435335995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16426607593902360956890663 24639911390853541435335995)
            ·
              refine ⟨36959867086280312153003993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24639911390853541435335995 36959867086280312153003993)
              ·
                refine ⟨27719900314710234114752995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36959867086280312153003993 27719900314710234114752995)
                ·
                  refine ⟨41579850472065351172129493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27719900314710234114752995 41579850472065351172129493)
                  ·
                    refine ⟨974527745439031668096785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41579850472065351172129493 974527745439031668096785)
                    ·
                      rfl

theorem cell22_2846829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2846829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846829 prefixEnd_2846829 := by exact prefixLift 2846829
  have htrace : WordTrace (prefixWord ++ tailWord_2846829) baseStart_2846829 baseEnd_2846829 := by
    simpa [prefixWord, tailWord_2846829, baseEnd_2846829] using wordTrace_append hprefix tailTrace_2846829
  have hstable : (prefixWord ++ tailWord_2846829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846829).length < 2 ^ (prefixWord ++ tailWord_2846829).sum := by decide
  have hdescent : baseEnd_2846829 < baseStart_2846829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846910 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_2846910 : Nat := 118140960795 + 2846910 * 2 ^ 59
def prefixEnd_2846910 : Nat := 4983230072969 + 3 ^ 40 * 2846910 * 2
def baseEnd_2846910 : Nat := 324851824464791485607179

theorem tailTrace_2846910 : CollatzResearch.WordTrace tailWord_2846910 prefixEnd_2846910 324851824464791485607179 := by
  unfold tailWord_2846910
  simp only [CollatzResearch.WordTrace]
  refine ⟨12979417264517344795459273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69223558744092505575782789 12979417264517344795459273)
  ·
    refine ⟨9734562948388008596594455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12979417264517344795459273 9734562948388008596594455)
    ·
      refine ⟨14601844422582012894891683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9734562948388008596594455 14601844422582012894891683)
      ·
        refine ⟨21902766633873019342337525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14601844422582012894891683 21902766633873019342337525)
        ·
          refine ⟨2053384371925595563344143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21902766633873019342337525 2053384371925595563344143)
          ·
            refine ⟨3080076557888393345016215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053384371925595563344143 3080076557888393345016215)
            ·
              refine ⟨4620114836832590017524323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080076557888393345016215 4620114836832590017524323)
              ·
                refine ⟨6930172255248885026286485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620114836832590017524323 6930172255248885026286485)
                ·
                  refine ⟨324851824464791485607179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6930172255248885026286485 324851824464791485607179)
                  ·
                    rfl

theorem cell22_2846910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_2846910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846910 prefixEnd_2846910 := by exact prefixLift 2846910
  have htrace : WordTrace (prefixWord ++ tailWord_2846910) baseStart_2846910 baseEnd_2846910 := by
    simpa [prefixWord, tailWord_2846910, baseEnd_2846910] using wordTrace_append hprefix tailTrace_2846910
  have hstable : (prefixWord ++ tailWord_2846910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846910).length < 2 ^ (prefixWord ++ tailWord_2846910).sum := by decide
  have hdescent : baseEnd_2846910 < baseStart_2846910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846966 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_2846966 : Nat := 118140960795 + 2846966 * 2 ^ 59
def prefixEnd_2846966 : Nat := 4983230072969 + 3 ^ 40 * 2846966 * 2
def baseEnd_2846966 : Nat := 324858214446269659140455

theorem tailTrace_2846966 : CollatzResearch.WordTrace tailWord_2846966 prefixEnd_2846966 324858214446269659140455 := by
  unfold tailWord_2846966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6489836287745992495482047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69224920402623919951808501 6489836287745992495482047)
  ·
    refine ⟨9734754431618988743223071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6489836287745992495482047 9734754431618988743223071)
    ·
      refine ⟨14602131647428483114834607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9734754431618988743223071 14602131647428483114834607)
      ·
        refine ⟨21903197471142724672251911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14602131647428483114834607 21903197471142724672251911)
        ·
          refine ⟨32854796206714087008377867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21903197471142724672251911 32854796206714087008377867)
          ·
            refine ⟨49282194310071130512566801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32854796206714087008377867 49282194310071130512566801)
            ·
              refine ⟨36961645732553347884425101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49282194310071130512566801 36961645732553347884425101)
              ·
                refine ⟨13860617149707505456659413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36961645732553347884425101 13860617149707505456659413)
                ·
                  refine ⟨324858214446269659140455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13860617149707505456659413 324858214446269659140455)
                  ·
                    rfl

theorem cell22_2846966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_2846966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846966 prefixEnd_2846966 := by exact prefixLift 2846966
  have htrace : WordTrace (prefixWord ++ tailWord_2846966) baseStart_2846966 baseEnd_2846966 := by
    simpa [prefixWord, tailWord_2846966, baseEnd_2846966] using wordTrace_append hprefix tailTrace_2846966
  have hstable : (prefixWord ++ tailWord_2846966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846966).length < 2 ^ (prefixWord ++ tailWord_2846966).sum := by decide
  have hdescent : baseEnd_2846966 < baseStart_2846966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846970 : List Nat := [3, 1, 1, 1, 1, 6, 1, 4, 1, 3]
def baseStart_2846970 : Nat := 118140960795 + 2846970 * 2 ^ 59
def prefixEnd_2846970 : Nat := 4983230072969 + 3 ^ 40 * 2846970 * 2
def baseEnd_2846970 : Nat := 974576012620554300321353

theorem tailTrace_2846970 : CollatzResearch.WordTrace tailWord_2846970 prefixEnd_2846970 974576012620554300321353 := by
  unfold tailWord_2846970
  simp only [CollatzResearch.WordTrace]
  refine ⟨25959381623980347152714591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69225017663947592407238909 25959381623980347152714591)
  ·
    refine ⟨38939072435970520729071887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25959381623980347152714591 38939072435970520729071887)
    ·
      refine ⟨58408608653955781093607831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38939072435970520729071887 58408608653955781093607831)
      ·
        refine ⟨87612912980933671640411747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58408608653955781093607831 87612912980933671640411747)
        ·
          refine ⟨131419369471400507460617621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87612912980933671640411747 131419369471400507460617621)
          ·
            refine ⟨6160282943971898787216451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131419369471400507460617621 6160282943971898787216451)
            ·
              refine ⟨9240424415957848180824677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6160282943971898787216451 9240424415957848180824677)
              ·
                refine ⟨1732579577992096533904627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9240424415957848180824677 1732579577992096533904627)
                ·
                  refine ⟨2598869366988144800856941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732579577992096533904627 2598869366988144800856941)
                  ·
                    refine ⟨974576012620554300321353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598869366988144800856941 974576012620554300321353)
                    ·
                      rfl

theorem cell22_2846970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_2846970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2846970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2846970 prefixEnd_2846970 := by exact prefixLift 2846970
  have htrace : WordTrace (prefixWord ++ tailWord_2846970) baseStart_2846970 baseEnd_2846970 := by
    simpa [prefixWord, tailWord_2846970, baseEnd_2846970] using wordTrace_append hprefix tailTrace_2846970
  have hstable : (prefixWord ++ tailWord_2846970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846970).length < 2 ^ (prefixWord ++ tailWord_2846970).sum := by decide
  have hdescent : baseEnd_2846970 < baseStart_2846970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847028 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 6]
def baseStart_2847028 : Nat := 118140960795 + 2847028 * 2 ^ 59
def prefixEnd_2847028 : Nat := 4983230072969 + 3 ^ 40 * 2847028 * 2
def baseEnd_2847028 : Nat := 324865289068620494123725

theorem tailTrace_2847028 : CollatzResearch.WordTrace tailWord_2847028 prefixEnd_2847028 324865289068620494123725 := by
  unfold tailWord_2847028
  simp only [CollatzResearch.WordTrace]
  refine ⟨51919820964855632258234869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69226427953140843010979825 51919820964855632258234869)
  ·
    refine ⟨4867483215455215524209519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51919820964855632258234869 4867483215455215524209519)
    ·
      refine ⟨7301224823182823286314279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4867483215455215524209519 7301224823182823286314279)
      ·
        refine ⟨10951837234774234929471419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7301224823182823286314279 10951837234774234929471419)
        ·
          refine ⟨16427755852161352394207129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10951837234774234929471419 16427755852161352394207129)
          ·
            refine ⟨12320816889121014295655347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16427755852161352394207129 12320816889121014295655347)
            ·
              refine ⟨18481225333681521443483021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12320816889121014295655347 18481225333681521443483021)
              ·
                refine ⟨6930459500130570541306133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18481225333681521443483021 6930459500130570541306133)
                ·
                  refine ⟨324865289068620494123725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6930459500130570541306133 324865289068620494123725)
                  ·
                    rfl

theorem cell22_2847028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_2847028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847028 prefixEnd_2847028 := by exact prefixLift 2847028
  have htrace : WordTrace (prefixWord ++ tailWord_2847028) baseStart_2847028 baseEnd_2847028 := by
    simpa [prefixWord, tailWord_2847028, baseEnd_2847028] using wordTrace_append hprefix tailTrace_2847028
  have hstable : (prefixWord ++ tailWord_2847028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847028).length < 2 ^ (prefixWord ++ tailWord_2847028).sum := by decide
  have hdescent : baseEnd_2847028 < baseStart_2847028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847043 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 2, 3]
def baseStart_2847043 : Nat := 118140960795 + 2847043 * 2 ^ 59
def prefixEnd_2847043 : Nat := 4983230072969 + 3 ^ 40 * 2847043 * 2
def baseEnd_2847043 : Nat := 974601002012406443246129

theorem tailTrace_2847043 : CollatzResearch.WordTrace tailWord_2847043 prefixEnd_2847043 974601002012406443246129 := by
  unfold tailWord_2847043
  simp only [CollatzResearch.WordTrace]
  refine ⟨103840189024656922078265783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69226792683104614718843855 103840189024656922078265783)
  ·
    refine ⟨155760283536985383117398675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103840189024656922078265783 155760283536985383117398675)
    ·
      refine ⟨233640425305478074676098013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155760283536985383117398675 233640425305478074676098013)
      ·
        refine ⟨87615159489554278003536755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233640425305478074676098013 87615159489554278003536755)
        ·
          refine ⟨131422739234331417005305133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87615159489554278003536755 131422739234331417005305133)
          ·
            refine ⟨49283527212874281376989425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131422739234331417005305133 49283527212874281376989425)
            ·
              refine ⟨36962645409655711032742069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49283527212874281376989425 36962645409655711032742069)
              ·
                refine ⟨3465248007155222909319569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36962645409655711032742069 3465248007155222909319569)
                ·
                  refine ⟨2598936005366417181989677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465248007155222909319569 2598936005366417181989677)
                  ·
                    refine ⟨974601002012406443246129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598936005366417181989677 974601002012406443246129)
                    ·
                      rfl

theorem cell22_2847043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 3].length) (baseStart_2847043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847043 prefixEnd_2847043 := by exact prefixLift 2847043
  have htrace : WordTrace (prefixWord ++ tailWord_2847043) baseStart_2847043 baseEnd_2847043 := by
    simpa [prefixWord, tailWord_2847043, baseEnd_2847043] using wordTrace_append hprefix tailTrace_2847043
  have hstable : (prefixWord ++ tailWord_2847043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847043).length < 2 ^ (prefixWord ++ tailWord_2847043).sum := by decide
  have hdescent : baseEnd_2847043 < baseStart_2847043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847056 : List Nat := [2, 1, 1, 1, 1, 7, 1, 8]
def baseStart_2847056 : Nat := 118140960795 + 2847056 * 2 ^ 59
def prefixEnd_2847056 : Nat := 4983230072969 + 3 ^ 40 * 2847056 * 2
def baseEnd_2847056 : Nat := 108289494686453193630121

theorem tailTrace_2847056 : CollatzResearch.WordTrace tailWord_2847056 prefixEnd_2847056 108289494686453193630121 := by
  unfold tailWord_2847056
  simp only [CollatzResearch.WordTrace]
  refine ⟨51920331586804912649244511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69227108782406550198992681 51920331586804912649244511)
  ·
    refine ⟨77880497380207368973866767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51920331586804912649244511 77880497380207368973866767)
    ·
      refine ⟨116820746070311053460800151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77880497380207368973866767 116820746070311053460800151)
      ·
        refine ⟨175231119105466580191200227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116820746070311053460800151 175231119105466580191200227)
        ·
          refine ⟨262846678658199870286800341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175231119105466580191200227 262846678658199870286800341)
          ·
            refine ⟨6160469031051559459846883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 262846678658199870286800341 6160469031051559459846883)
            ·
              refine ⟨9240703546577339189770325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6160469031051559459846883 9240703546577339189770325)
              ·
                refine ⟨108289494686453193630121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9240703546577339189770325 108289494686453193630121)
                ·
                  rfl

theorem cell22_2847056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 8].length) (baseStart_2847056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847056 prefixEnd_2847056 := by exact prefixLift 2847056
  have htrace : WordTrace (prefixWord ++ tailWord_2847056) baseStart_2847056 baseEnd_2847056 := by
    simpa [prefixWord, tailWord_2847056, baseEnd_2847056] using wordTrace_append hprefix tailTrace_2847056
  have hstable : (prefixWord ++ tailWord_2847056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847056).length < 2 ^ (prefixWord ++ tailWord_2847056).sum := by decide
  have hdescent : baseEnd_2847056 < baseStart_2847056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847094 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_2847094 : Nat := 118140960795 + 2847094 * 2 ^ 59
def prefixEnd_2847094 : Nat := 4983230072969 + 3 ^ 40 * 2847094 * 2
def baseEnd_2847094 : Nat := 974618460354659310220973

theorem tailTrace_2847094 : CollatzResearch.WordTrace tailWord_2847094 prefixEnd_2847094 974618460354659310220973 := by
  unfold tailWord_2847094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6490128071717009861773271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69228032764981438525581557 6490128071717009861773271)
  ·
    refine ⟨9735192107575514792659907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6490128071717009861773271 9735192107575514792659907)
    ·
      refine ⟨14602788161363272188989861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9735192107575514792659907 14602788161363272188989861)
      ·
        refine ⟨2738022780255613535435599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14602788161363272188989861 2738022780255613535435599)
        ·
          refine ⟨4107034170383420303153399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2738022780255613535435599 4107034170383420303153399)
          ·
            refine ⟨6160551255575130454730099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107034170383420303153399 6160551255575130454730099)
            ·
              refine ⟨9240826883362695682095149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6160551255575130454730099 9240826883362695682095149)
              ·
                refine ⟨3465310081261010880785681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9240826883362695682095149 3465310081261010880785681)
                ·
                  refine ⟨2598982560945758160589261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465310081261010880785681 2598982560945758160589261)
                  ·
                    refine ⟨974618460354659310220973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598982560945758160589261 974618460354659310220973)
                    ·
                      rfl

theorem cell22_2847094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_2847094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847094 prefixEnd_2847094 := by exact prefixLift 2847094
  have htrace : WordTrace (prefixWord ++ tailWord_2847094) baseStart_2847094 baseEnd_2847094 := by
    simpa [prefixWord, tailWord_2847094, baseEnd_2847094] using wordTrace_append hprefix tailTrace_2847094
  have hstable : (prefixWord ++ tailWord_2847094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847094).length < 2 ^ (prefixWord ++ tailWord_2847094).sum := by decide
  have hdescent : baseEnd_2847094 < baseStart_2847094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847139 : List Nat := [1, 1, 1, 4, 1, 6, 2, 2, 1, 3]
def baseStart_2847139 : Nat := 118140960795 + 2847139 * 2 ^ 59
def prefixEnd_2847139 : Nat := 4983230072969 + 3 ^ 40 * 2847139 * 2
def baseEnd_2847139 : Nat := 974633864774294192845835

theorem tailTrace_2847139 : CollatzResearch.WordTrace tailWord_2847139 prefixEnd_2847139 974633864774294192845835 := by
  unfold tailWord_2847139
  simp only [CollatzResearch.WordTrace]
  refine ⟨103843690432309130473760471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69229126954872753649173647 103843690432309130473760471)
  ·
    refine ⟨155765535648463695710640707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103843690432309130473760471 155765535648463695710640707)
    ·
      refine ⟨233648303472695543565961061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155765535648463695710640707 233648303472695543565961061)
      ·
        refine ⟨43809056901130414418617699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233648303472695543565961061 43809056901130414418617699)
        ·
          refine ⟨65713585351695621627926549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43809056901130414418617699 65713585351695621627926549)
          ·
            refine ⟨3080324313360732263809057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65713585351695621627926549 3080324313360732263809057)
            ·
              refine ⟨2310243235020549197856793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3080324313360732263809057 2310243235020549197856793)
              ·
                refine ⟨1732682426265411898392595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310243235020549197856793 1732682426265411898392595)
                ·
                  refine ⟨2599023639398117847588893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732682426265411898392595 2599023639398117847588893)
                  ·
                    refine ⟨974633864774294192845835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599023639398117847588893 974633864774294192845835)
                    ·
                      rfl

theorem cell22_2847139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 3].length) (baseStart_2847139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847139 prefixEnd_2847139 := by exact prefixLift 2847139
  have htrace : WordTrace (prefixWord ++ tailWord_2847139) baseStart_2847139 baseEnd_2847139 := by
    simpa [prefixWord, tailWord_2847139, baseEnd_2847139] using wordTrace_append hprefix tailTrace_2847139
  have hstable : (prefixWord ++ tailWord_2847139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847139).length < 2 ^ (prefixWord ++ tailWord_2847139).sum := by decide
  have hdescent : baseEnd_2847139 < baseStart_2847139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847178 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_2847178 : Nat := 118140960795 + 2847178 * 2 ^ 59
def prefixEnd_2847178 : Nat := 4983230072969 + 3 ^ 40 * 2847178 * 2
def baseEnd_2847178 : Nat := 974647215271311091120715

theorem tailTrace_2847178 : CollatzResearch.WordTrace tailWord_2847178 prefixEnd_2847178 974647215271311091120715 := by
  unfold tailWord_2847178
  simp only [CollatzResearch.WordTrace]
  refine ⟨25961278219791960033607547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69230075252778560089620125 25961278219791960033607547)
  ·
    refine ⟨38941917329687940050411321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25961278219791960033607547 38941917329687940050411321)
    ·
      refine ⟨29206437997265955037808491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38941917329687940050411321 29206437997265955037808491)
      ·
        refine ⟨43809656995898932556712737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29206437997265955037808491 43809656995898932556712737)
        ·
          refine ⟨32857242746924199417534553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43809656995898932556712737 32857242746924199417534553)
          ·
            refine ⟨24642932060193149563150915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32857242746924199417534553 24642932060193149563150915)
            ·
              refine ⟨36964398090289724344726373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24642932060193149563150915 36964398090289724344726373)
              ·
                refine ⟨6930824641929323314636195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36964398090289724344726373 6930824641929323314636195)
                ·
                  refine ⟨10396236962893984971954293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6930824641929323314636195 10396236962893984971954293)
                  ·
                    refine ⟨974647215271311091120715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10396236962893984971954293 974647215271311091120715)
                    ·
                      rfl

theorem cell22_2847178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_2847178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847178 prefixEnd_2847178 := by exact prefixLift 2847178
  have htrace : WordTrace (prefixWord ++ tailWord_2847178) baseStart_2847178 baseEnd_2847178 := by
    simpa [prefixWord, tailWord_2847178, baseEnd_2847178] using wordTrace_append hprefix tailTrace_2847178
  have hstable : (prefixWord ++ tailWord_2847178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847178).length < 2 ^ (prefixWord ++ tailWord_2847178).sum := by decide
  have hdescent : baseEnd_2847178 < baseStart_2847178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847193 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_2847193 : Nat := 118140960795 + 2847193 * 2 ^ 59
def prefixEnd_2847193 : Nat := 4983230072969 + 3 ^ 40 * 2847193 * 2
def baseEnd_2847193 : Nat := 974652350077856051995669

theorem tailTrace_2847193 : CollatzResearch.WordTrace tailWord_2847193 prefixEnd_2847193 974652350077856051995669 := by
  unfold tailWord_2847193
  simp only [CollatzResearch.WordTrace]
  refine ⟨103845659974113497696226233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69230439982742331797484155 103845659974113497696226233)
  ·
    refine ⟨77884244980585123272169675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103845659974113497696226233 77884244980585123272169675)
    ·
      refine ⟨116826367470877684908254513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77884244980585123272169675 116826367470877684908254513)
      ·
        refine ⟨87619775603158263681190885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116826367470877684908254513 87619775603158263681190885)
        ·
          refine ⟨16428707925592174440223291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87619775603158263681190885 16428707925592174440223291)
          ·
            refine ⟨24643061888388261660334937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16428707925592174440223291 24643061888388261660334937)
            ·
              refine ⟨18482296416291196245251203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24643061888388261660334937 18482296416291196245251203)
              ·
                refine ⟨27723444624436794367876805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18482296416291196245251203 27723444624436794367876805)
                ·
                  refine ⟨5198145867081898943976901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27723444624436794367876805 5198145867081898943976901)
                  ·
                    refine ⟨974652350077856051995669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5198145867081898943976901 974652350077856051995669)
                    ·
                      rfl

theorem cell22_2847193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_2847193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847193 prefixEnd_2847193 := by exact prefixLift 2847193
  have htrace : WordTrace (prefixWord ++ tailWord_2847193) baseStart_2847193 baseEnd_2847193 := by
    simpa [prefixWord, tailWord_2847193, baseEnd_2847193] using wordTrace_append hprefix tailTrace_2847193
  have hstable : (prefixWord ++ tailWord_2847193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847193).length < 2 ^ (prefixWord ++ tailWord_2847193).sum := by decide
  have hdescent : baseEnd_2847193 < baseStart_2847193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847212 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 2, 3]
def baseStart_2847212 : Nat := 118140960795 + 2847212 * 2 ^ 59
def prefixEnd_2847212 : Nat := 4983230072969 + 3 ^ 40 * 2847212 * 2
def baseEnd_2847212 : Nat := 974658854166146335770611

theorem tailTrace_2847212 : CollatzResearch.WordTrace tailWord_2847212 prefixEnd_2847212 974658854166146335770611 := by
  unfold tailWord_2847212
  simp only [CollatzResearch.WordTrace]
  refine ⟨51923176480522331970583945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69230901974029775960778593 51923176480522331970583945)
  ·
    refine ⟨38942382360391748977937959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51923176480522331970583945 38942382360391748977937959)
    ·
      refine ⟨58413573540587623466906939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38942382360391748977937959 58413573540587623466906939)
      ·
        refine ⟨87620360310881435200360409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58413573540587623466906939 87620360310881435200360409)
        ·
          refine ⟨65715270233161076400270307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87620360310881435200360409 65715270233161076400270307)
          ·
            refine ⟨98572905349741614600405461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65715270233161076400270307 98572905349741614600405461)
            ·
              refine ⟨2310302469134569092197003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98572905349741614600405461 2310302469134569092197003)
              ·
                refine ⟨3465453703701853638295505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310302469134569092197003 3465453703701853638295505)
                ·
                  refine ⟨2599090277776390228721629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465453703701853638295505 2599090277776390228721629)
                  ·
                    refine ⟨974658854166146335770611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599090277776390228721629 974658854166146335770611)
                    ·
                      rfl

theorem cell22_2847212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_2847212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847212 prefixEnd_2847212 := by exact prefixLift 2847212
  have htrace : WordTrace (prefixWord ++ tailWord_2847212) baseStart_2847212 baseEnd_2847212 := by
    simpa [prefixWord, tailWord_2847212, baseEnd_2847212] using wordTrace_append hprefix tailTrace_2847212
  have hstable : (prefixWord ++ tailWord_2847212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847212).length < 2 ^ (prefixWord ++ tailWord_2847212).sum := by decide
  have hdescent : baseEnd_2847212 < baseStart_2847212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847253 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 7]
def baseStart_2847253 : Nat := 118140960795 + 2847253 * 2 ^ 59
def prefixEnd_2847253 : Nat := 4983230072969 + 3 ^ 40 * 2847253 * 2
def baseEnd_2847253 : Nat := 324890963101345298498495

theorem tailTrace_2847253 : CollatzResearch.WordTrace tailWord_2847253 prefixEnd_2847253 324890963101345298498495 := by
  unfold tailWord_2847253
  simp only [CollatzResearch.WordTrace]
  refine ⟨103847848353896127943410413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69231898902597418628940275 103847848353896127943410413)
  ·
    refine ⟨38942943132711047978778905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103847848353896127943410413 38942943132711047978778905)
    ·
      refine ⟨29207207349533285984084179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38942943132711047978778905 29207207349533285984084179)
      ·
        refine ⟨43810811024299928976126269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29207207349533285984084179 43810811024299928976126269)
        ·
          refine ⟨16429054134112473366047351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43810811024299928976126269 16429054134112473366047351)
          ·
            refine ⟨24643581201168710049071027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16429054134112473366047351 24643581201168710049071027)
            ·
              refine ⟨36965371801753065073606541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24643581201168710049071027 36965371801753065073606541)
              ·
                refine ⟨13862014425657399402602453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36965371801753065073606541 13862014425657399402602453)
                ·
                  refine ⟨324890963101345298498495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13862014425657399402602453 324890963101345298498495)
                  ·
                    rfl

theorem cell22_2847253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_2847253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847253 prefixEnd_2847253 := by exact prefixLift 2847253
  have htrace : WordTrace (prefixWord ++ tailWord_2847253) baseStart_2847253 baseEnd_2847253 := by
    simpa [prefixWord, tailWord_2847253, baseEnd_2847253] using wordTrace_append hprefix tailTrace_2847253
  have hstable : (prefixWord ++ tailWord_2847253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847253).length < 2 ^ (prefixWord ++ tailWord_2847253).sum := by decide
  have hdescent : baseEnd_2847253 < baseStart_2847253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847343 : List Nat := [1, 1, 2, 1, 3, 2, 2, 10]
def baseStart_2847343 : Nat := 118140960795 + 2847343 * 2 ^ 59
def prefixEnd_2847343 : Nat := 4983230072969 + 3 ^ 40 * 2847343 * 2
def baseEnd_2847343 : Nat := 108300410904811740082801

theorem tailTrace_2847343 : CollatzResearch.WordTrace tailWord_2847343 prefixEnd_2847343 108300410904811740082801 := by
  unfold tailWord_2847343
  simp only [CollatzResearch.WordTrace]
  refine ⟨103851130923570073314186683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69234087282380048876124455 103851130923570073314186683)
  ·
    refine ⟨155776696385355109971280025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103851130923570073314186683 155776696385355109971280025)
    ·
      refine ⟨116832522289016332478460019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155776696385355109971280025 116832522289016332478460019)
      ·
        refine ⟨175248783433524498717690029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116832522289016332478460019 175248783433524498717690029)
        ·
          refine ⟨65718293787571687019133761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175248783433524498717690029 65718293787571687019133761)
          ·
            refine ⟨49288720340678765264350321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65718293787571687019133761 49288720340678765264350321)
            ·
              refine ⟨36966540255509073948262741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49288720340678765264350321 36966540255509073948262741)
              ·
                refine ⟨108300410904811740082801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36966540255509073948262741 108300410904811740082801)
                ·
                  rfl

theorem cell22_2847343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 10].length) (baseStart_2847343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847343 prefixEnd_2847343 := by exact prefixLift 2847343
  have htrace : WordTrace (prefixWord ++ tailWord_2847343) baseStart_2847343 baseEnd_2847343 := by
    simpa [prefixWord, tailWord_2847343, baseEnd_2847343] using wordTrace_append hprefix tailTrace_2847343
  have hstable : (prefixWord ++ tailWord_2847343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847343).length < 2 ^ (prefixWord ++ tailWord_2847343).sum := by decide
  have hdescent : baseEnd_2847343 < baseStart_2847343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847364 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_2847364 : Nat := 118140960795 + 2847364 * 2 ^ 59
def prefixEnd_2847364 : Nat := 4983230072969 + 3 ^ 40 * 2847364 * 2
def baseEnd_2847364 : Nat := 974710886872468605970145

theorem tailTrace_2847364 : CollatzResearch.WordTrace tailWord_2847364 prefixEnd_2847364 974710886872468605970145 := by
  unfold tailWord_2847364
  simp only [CollatzResearch.WordTrace]
  refine ⟨51925948428246996950350573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69234597904329329267134097 51925948428246996950350573)
  ·
    refine ⟨19472230660592623856381465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51925948428246996950350573 19472230660592623856381465)
    ·
      refine ⟨14604172995444467892286099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19472230660592623856381465 14604172995444467892286099)
      ·
        refine ⟨21906259493166701838429149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14604172995444467892286099 21906259493166701838429149)
        ·
          refine ⟨8214847309937513189410931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21906259493166701838429149 8214847309937513189410931)
          ·
            refine ⟨12322270964906269784116397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8214847309937513189410931 12322270964906269784116397)
            ·
              refine ⟨4620851611839851169043649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12322270964906269784116397 4620851611839851169043649)
              ·
                refine ⟨3465638708879888376782737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4620851611839851169043649 3465638708879888376782737)
                ·
                  refine ⟨2599229031659916282587053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465638708879888376782737 2599229031659916282587053)
                  ·
                    refine ⟨974710886872468605970145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599229031659916282587053 974710886872468605970145)
                    ·
                      rfl

theorem cell22_2847364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_2847364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847364 prefixEnd_2847364 := by exact prefixLift 2847364
  have htrace : WordTrace (prefixWord ++ tailWord_2847364) baseStart_2847364 baseEnd_2847364 := by
    simpa [prefixWord, tailWord_2847364, baseEnd_2847364] using wordTrace_append hprefix tailTrace_2847364
  have hstable : (prefixWord ++ tailWord_2847364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847364).length < 2 ^ (prefixWord ++ tailWord_2847364).sum := by decide
  have hdescent : baseEnd_2847364 < baseStart_2847364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847375 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 7, 3]
def baseStart_2847375 : Nat := 118140960795 + 2847375 * 2 ^ 59
def prefixEnd_2847375 : Nat := 4983230072969 + 3 ^ 40 * 2847375 * 2
def baseEnd_2847375 : Nat := 974714652397268243945111

theorem tailTrace_2847375 : CollatzResearch.WordTrace tailWord_2847375 prefixEnd_2847375 974714652397268243945111 := by
  unfold tailWord_2847375
  simp only [CollatzResearch.WordTrace]
  refine ⟨103852298059454142779351579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69234865372969428519567719 103852298059454142779351579)
  ·
    refine ⟨155778447089181214169027369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103852298059454142779351579 155778447089181214169027369)
    ·
      refine ⟨116833835316885910626770527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155778447089181214169027369 116833835316885910626770527)
      ·
        refine ⟨175250752975328865940155791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116833835316885910626770527 175250752975328865940155791)
        ·
          refine ⟨262876129462993298910233687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175250752975328865940155791 262876129462993298910233687)
          ·
            refine ⟨394314194194489948365350531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262876129462993298910233687 394314194194489948365350531)
            ·
              refine ⟨591471291291734922548025797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394314194194489948365350531 591471291291734922548025797)
              ·
                refine ⟨110900867117200297977754837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591471291291734922548025797 110900867117200297977754837)
                ·
                  refine ⟨2599239073059381983853629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 110900867117200297977754837 2599239073059381983853629)
                  ·
                    refine ⟨974714652397268243945111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599239073059381983853629 974714652397268243945111)
                    ·
                      rfl

theorem cell22_2847375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_2847375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847375 prefixEnd_2847375 := by exact prefixLift 2847375
  have htrace : WordTrace (prefixWord ++ tailWord_2847375) baseStart_2847375 baseEnd_2847375 := by
    simpa [prefixWord, tailWord_2847375, baseEnd_2847375] using wordTrace_append hprefix tailTrace_2847375
  have hstable : (prefixWord ++ tailWord_2847375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847375).length < 2 ^ (prefixWord ++ tailWord_2847375).sum := by decide
  have hdescent : baseEnd_2847375 < baseStart_2847375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847422 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2847422 : Nat := 118140960795 + 2847422 * 2 ^ 59
def prefixEnd_2847422 : Nat := 4983230072969 + 3 ^ 40 * 2847422 * 2
def baseEnd_2847422 : Nat := 324910247152591929339989

theorem tailTrace_2847422 : CollatzResearch.WordTrace tailWord_2847422 prefixEnd_2847422 324910247152591929339989 := by
  unfold tailWord_2847422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12981751536285483725789065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69236008193522579870875013 12981751536285483725789065)
  ·
    refine ⟨9736313652214112794341799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12981751536285483725789065 9736313652214112794341799)
    ·
      refine ⟨14604470478321169191512699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9736313652214112794341799 14604470478321169191512699)
      ·
        refine ⟨21906705717481753787269049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14604470478321169191512699 21906705717481753787269049)
        ·
          refine ⟨16430029288111315340451787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21906705717481753787269049 16430029288111315340451787)
          ·
            refine ⟨24645043932166973010677681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16430029288111315340451787 24645043932166973010677681)
            ·
              refine ⟨18483782949125229758008261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24645043932166973010677681 18483782949125229758008261)
              ·
                refine ⟨3465709302960980579626549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18483782949125229758008261 3465709302960980579626549)
                ·
                  refine ⟨324910247152591929339989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3465709302960980579626549 324910247152591929339989)
                  ·
                    rfl

theorem cell22_2847422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2847422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847422 prefixEnd_2847422 := by exact prefixLift 2847422
  have htrace : WordTrace (prefixWord ++ tailWord_2847422) baseStart_2847422 baseEnd_2847422 := by
    simpa [prefixWord, tailWord_2847422, baseEnd_2847422] using wordTrace_append hprefix tailTrace_2847422
  have hstable : (prefixWord ++ tailWord_2847422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847422).length < 2 ^ (prefixWord ++ tailWord_2847422).sum := by decide
  have hdescent : baseEnd_2847422 < baseStart_2847422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847450 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_2847450 : Nat := 118140960795 + 2847450 * 2 ^ 59
def prefixEnd_2847450 : Nat := 4983230072969 + 3 ^ 40 * 2847450 * 2
def baseEnd_2847450 : Nat := 324913442143331016106627

theorem tailTrace_2847450 : CollatzResearch.WordTrace tailWord_2847450 prefixEnd_2847450 324913442143331016106627 := by
  unfold tailWord_2847450
  simp only [CollatzResearch.WordTrace]
  refine ⟨25963758383545607647082951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69236689022788287058887869 25963758383545607647082951)
  ·
    refine ⟨38945637575318411470624427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25963758383545607647082951 38945637575318411470624427)
    ·
      refine ⟨58418456362977617205936641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38945637575318411470624427 58418456362977617205936641)
      ·
        refine ⟨43813842272233212904452481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58418456362977617205936641 43813842272233212904452481)
        ·
          refine ⟨32860381704174909678339361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43813842272233212904452481 32860381704174909678339361)
          ·
            refine ⟨24645286278131182258754521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32860381704174909678339361 24645286278131182258754521)
            ·
              refine ⟨18483964708598386694065891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24645286278131182258754521 18483964708598386694065891)
              ·
                refine ⟨27725947062897580041098837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18483964708598386694065891 27725947062897580041098837)
                ·
                  refine ⟨324913442143331016106627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27725947062897580041098837 324913442143331016106627)
                  ·
                    rfl

theorem cell22_2847450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_2847450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847450 prefixEnd_2847450 := by exact prefixLift 2847450
  have htrace : WordTrace (prefixWord ++ tailWord_2847450) baseStart_2847450 baseEnd_2847450 := by
    simpa [prefixWord, tailWord_2847450, baseEnd_2847450] using wordTrace_append hprefix tailTrace_2847450
  have hstable : (prefixWord ++ tailWord_2847450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847450).length < 2 ^ (prefixWord ++ tailWord_2847450).sum := by decide
  have hdescent : baseEnd_2847450 < baseStart_2847450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847465 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_2847465 : Nat := 118140960795 + 2847465 * 2 ^ 59
def prefixEnd_2847465 : Nat := 4983230072969 + 3 ^ 40 * 2847465 * 2
def baseEnd_2847465 : Nat := 974745461236538009194835

theorem tailTrace_2847465 : CollatzResearch.WordTrace tailWord_2847465 prefixEnd_2847465 974745461236538009194835 := by
  unfold tailWord_2847465
  simp only [CollatzResearch.WordTrace]
  refine ⟨103855580629128088150127849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69237053752752058766751899 103855580629128088150127849)
  ·
    refine ⟨77891685471846066112595887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103855580629128088150127849 77891685471846066112595887)
    ·
      refine ⟨116837528207769099168893831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77891685471846066112595887 116837528207769099168893831)
      ·
        refine ⟨175256292311653648753340747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116837528207769099168893831 175256292311653648753340747)
        ·
          refine ⟨262884438467480473130011121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175256292311653648753340747 262884438467480473130011121)
          ·
            refine ⟨197163328850610354847508341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262884438467480473130011121 197163328850610354847508341)
            ·
              refine ⟨18484062079744720766953907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197163328850610354847508341 18484062079744720766953907)
              ·
                refine ⟨27726093119617081150430861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18484062079744720766953907 27726093119617081150430861)
                ·
                  refine ⟨10397284919856405431411573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27726093119617081150430861 10397284919856405431411573)
                  ·
                    refine ⟨974745461236538009194835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10397284919856405431411573 974745461236538009194835)
                    ·
                      rfl

theorem cell22_2847465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_2847465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847465 prefixEnd_2847465 := by exact prefixLift 2847465
  have htrace : WordTrace (prefixWord ++ tailWord_2847465) baseStart_2847465 baseEnd_2847465 := by
    simpa [prefixWord, tailWord_2847465, baseEnd_2847465] using wordTrace_append hprefix tailTrace_2847465
  have hstable : (prefixWord ++ tailWord_2847465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847465).length < 2 ^ (prefixWord ++ tailWord_2847465).sum := by decide
  have hdescent : baseEnd_2847465 < baseStart_2847465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847467 : List Nat := [1, 1, 1, 1, 2, 4, 1, 7, 4]
def baseStart_2847467 : Nat := 118140960795 + 2847467 * 2 ^ 59
def prefixEnd_2847467 : Nat := 4983230072969 + 3 ^ 40 * 2847467 * 2
def baseEnd_2847467 : Nat := 324915381959136890214943

theorem tailTrace_2847467 : CollatzResearch.WordTrace tailWord_2847467 prefixEnd_2847467 324915381959136890214943 := by
  unfold tailWord_2847467
  simp only [CollatzResearch.WordTrace]
  refine ⟨103855653575120842491700655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69237102383413894994467103 103855653575120842491700655)
  ·
    refine ⟨155783480362681263737550983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103855653575120842491700655 155783480362681263737550983)
    ·
      refine ⟨233675220544021895606326475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155783480362681263737550983 233675220544021895606326475)
      ·
        refine ⟨350512830816032843409489713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233675220544021895606326475 350512830816032843409489713)
        ·
          refine ⟨262884623112024632557117285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350512830816032843409489713 262884623112024632557117285)
          ·
            refine ⟨49290866833504618604459491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262884623112024632557117285 49290866833504618604459491)
            ·
              refine ⟨73936300250256927906689237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49290866833504618604459491 73936300250256927906689237)
              ·
                refine ⟨1732882037115396747813029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73936300250256927906689237 1732882037115396747813029)
                ·
                  refine ⟨324915381959136890214943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732882037115396747813029 324915381959136890214943)
                  ·
                    rfl

theorem cell22_2847467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 4].length) (baseStart_2847467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847467 prefixEnd_2847467 := by exact prefixLift 2847467
  have htrace : WordTrace (prefixWord ++ tailWord_2847467) baseStart_2847467 baseEnd_2847467 := by
    simpa [prefixWord, tailWord_2847467, baseEnd_2847467] using wordTrace_append hprefix tailTrace_2847467
  have hstable : (prefixWord ++ tailWord_2847467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847467).length < 2 ^ (prefixWord ++ tailWord_2847467).sum := by decide
  have hdescent : baseEnd_2847467 < baseStart_2847467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847482 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_2847482 : Nat := 118140960795 + 2847482 * 2 ^ 59
def prefixEnd_2847482 : Nat := 4983230072969 + 3 ^ 40 * 2847482 * 2
def baseEnd_2847482 : Nat := 974751280683955631519783

theorem tailTrace_2847482 : CollatzResearch.WordTrace tailWord_2847482 prefixEnd_2847482 974751280683955631519783 := by
  unfold tailWord_2847482
  simp only [CollatzResearch.WordTrace]
  refine ⟨25964050167516625013374175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69237467113377666702331133 25964050167516625013374175)
  ·
    refine ⟨38946075251274937520061263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25964050167516625013374175 38946075251274937520061263)
    ·
      refine ⟨58419112876912406280091895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38946075251274937520061263 58419112876912406280091895)
      ·
        refine ⟨87628669315368609420137843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58419112876912406280091895 87628669315368609420137843)
        ·
          refine ⟨131443003973052914130206765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87628669315368609420137843 131443003973052914130206765)
          ·
            refine ⟨49291126489894842798827537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131443003973052914130206765 49291126489894842798827537)
            ·
              refine ⟨36968344867421132099120653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49291126489894842798827537 36968344867421132099120653)
              ·
                refine ⟨13863129325282924537170245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36968344867421132099120653 13863129325282924537170245)
                ·
                  refine ⟨2599336748490548350719421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13863129325282924537170245 2599336748490548350719421)
                  ·
                    refine ⟨974751280683955631519783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599336748490548350719421 974751280683955631519783)
                    ·
                      rfl

theorem cell22_2847482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_2847482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847482 prefixEnd_2847482 := by exact prefixLift 2847482
  have htrace : WordTrace (prefixWord ++ tailWord_2847482) baseStart_2847482 baseEnd_2847482 := by
    simpa [prefixWord, tailWord_2847482, baseEnd_2847482] using wordTrace_append hprefix tailTrace_2847482
  have hstable : (prefixWord ++ tailWord_2847482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847482).length < 2 ^ (prefixWord ++ tailWord_2847482).sum := by decide
  have hdescent : baseEnd_2847482 < baseStart_2847482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847484 : List Nat := [2, 2, 2, 1, 3, 3, 1, 4, 4]
def baseStart_2847484 : Nat := 118140960795 + 2847484 * 2 ^ 59
def prefixEnd_2847484 : Nat := 4983230072969 + 3 ^ 40 * 2847484 * 2
def baseEnd_2847484 : Nat := 324917321774942764323259

theorem tailTrace_2847484 : CollatzResearch.WordTrace tailWord_2847484 prefixEnd_2847484 324917321774942764323259 := by
  unfold tailWord_2847484
  simp only [CollatzResearch.WordTrace]
  refine ⟨51928136808029627197534753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69237515744039502930046337 51928136808029627197534753)
  ·
    refine ⟨38946102606022220398151065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51928136808029627197534753 38946102606022220398151065)
    ·
      refine ⟨29209576954516665298613299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38946102606022220398151065 29209576954516665298613299)
      ·
        refine ⟨43814365431774997947919949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29209576954516665298613299 43814365431774997947919949)
        ·
          refine ⟨16430387036915624230469981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43814365431774997947919949 16430387036915624230469981)
          ·
            refine ⟨6161395138843359086426243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16430387036915624230469981 6161395138843359086426243)
            ·
              refine ⟨9242092708265038629639365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6161395138843359086426243 9242092708265038629639365)
              ·
                refine ⟨1732892382799694743057381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9242092708265038629639365 1732892382799694743057381)
                ·
                  refine ⟨324917321774942764323259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732892382799694743057381 324917321774942764323259)
                  ·
                    rfl

theorem cell22_2847484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_2847484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847484 prefixEnd_2847484 := by exact prefixLift 2847484
  have htrace : WordTrace (prefixWord ++ tailWord_2847484) baseStart_2847484 baseEnd_2847484 := by
    simpa [prefixWord, tailWord_2847484, baseEnd_2847484] using wordTrace_append hprefix tailTrace_2847484
  have hstable : (prefixWord ++ tailWord_2847484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847484).length < 2 ^ (prefixWord ++ tailWord_2847484).sum := by decide
  have hdescent : baseEnd_2847484 < baseStart_2847484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847533 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2847533 : Nat := 118140960795 + 2847533 * 2 ^ 59
def prefixEnd_2847533 : Nat := 4983230072969 + 3 ^ 40 * 2847533 * 2
def baseEnd_2847533 : Nat := 974768739026208498494627

theorem tailTrace_2847533 : CollatzResearch.WordTrace tailWord_2847533 prefixEnd_2847533 974768739026208498494627 := by
  unfold tailWord_2847533
  simp only [CollatzResearch.WordTrace]
  refine ⟨103858060792881735763603253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69238707195254490509068835 103858060792881735763603253)
  ·
    refine ⟨9736693199332662727837805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103858060792881735763603253 9736693199332662727837805)
    ·
      refine ⟨3651259949749748522939177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9736693199332662727837805 3651259949749748522939177)
      ·
        refine ⟨2738444962312311392204383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3651259949749748522939177 2738444962312311392204383)
        ·
          refine ⟨4107667443468467088306575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2738444962312311392204383 4107667443468467088306575)
          ·
            refine ⟨6161501165202700632459863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107667443468467088306575 6161501165202700632459863)
            ·
              refine ⟨9242251747804050948689795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6161501165202700632459863 9242251747804050948689795)
              ·
                refine ⟨13863377621706076423034693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9242251747804050948689795 13863377621706076423034693)
                ·
                  refine ⟨2599383304069889329319005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13863377621706076423034693 2599383304069889329319005)
                  ·
                    refine ⟨974768739026208498494627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599383304069889329319005 974768739026208498494627)
                    ·
                      rfl

theorem cell22_2847533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2847533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847533 prefixEnd_2847533 := by exact prefixLift 2847533
  have htrace : WordTrace (prefixWord ++ tailWord_2847533) baseStart_2847533 baseEnd_2847533 := by
    simpa [prefixWord, tailWord_2847533, baseEnd_2847533] using wordTrace_append hprefix tailTrace_2847533
  have hstable : (prefixWord ++ tailWord_2847533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847533).length < 2 ^ (prefixWord ++ tailWord_2847533).sum := by decide
  have hdescent : baseEnd_2847533 < baseStart_2847533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847544 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 3, 3]
def baseStart_2847544 : Nat := 118140960795 + 2847544 * 2 ^ 59
def prefixEnd_2847544 : Nat := 4983230072969 + 3 ^ 40 * 2847544 * 2
def baseEnd_2847544 : Nat := 974772504551008136469593

theorem tailTrace_2847544 : CollatzResearch.WordTrace tailWord_2847544 prefixEnd_2847544 974772504551008136469593 := by
  unfold tailWord_2847544
  simp only [CollatzResearch.WordTrace]
  refine ⟨51929230997920942321126843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69238974663894589761502457 51929230997920942321126843)
  ·
    refine ⟨77893846496881413481690265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51929230997920942321126843 77893846496881413481690265)
    ·
      refine ⟨58420384872661060111267699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77893846496881413481690265 58420384872661060111267699)
      ·
        refine ⟨87630577308991590166901549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58420384872661060111267699 87630577308991590166901549)
        ·
          refine ⟨32861466490871846312588081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87630577308991590166901549 32861466490871846312588081)
          ·
            refine ⟨24646099868153884734441061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32861466490871846312588081 24646099868153884734441061)
            ·
              refine ⟨4621143725278853387707699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24646099868153884734441061 4621143725278853387707699)
              ·
                refine ⟨6931715587918280081561549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4621143725278853387707699 6931715587918280081561549)
                ·
                  refine ⟨2599393345469355030585581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6931715587918280081561549 2599393345469355030585581)
                  ·
                    refine ⟨974772504551008136469593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599393345469355030585581 974772504551008136469593)
                    ·
                      rfl

theorem cell22_2847544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_2847544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847544 prefixEnd_2847544 := by exact prefixLift 2847544
  have htrace : WordTrace (prefixWord ++ tailWord_2847544) baseStart_2847544 baseEnd_2847544 := by
    simpa [prefixWord, tailWord_2847544, baseEnd_2847544] using wordTrace_append hprefix tailTrace_2847544
  have hstable : (prefixWord ++ tailWord_2847544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847544).length < 2 ^ (prefixWord ++ tailWord_2847544).sum := by decide
  have hdescent : baseEnd_2847544 < baseStart_2847544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847578 : List Nat := [3, 1, 1, 2, 1, 6, 1, 3, 1, 3]
def baseStart_2847578 : Nat := 118140960795 + 2847578 * 2 ^ 59
def prefixEnd_2847578 : Nat := 4983230072969 + 3 ^ 40 * 2847578 * 2
def baseEnd_2847578 : Nat := 974784143445843381119489

theorem tailTrace_2847578 : CollatzResearch.WordTrace tailWord_2847578 prefixEnd_2847578 974784143445843381119489 := by
  unfold tailWord_2847578
  simp only [CollatzResearch.WordTrace]
  refine ⟨25964925519429677112247847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69239801385145805632660925 25964925519429677112247847)
  ·
    refine ⟨38947388279144515668371771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25964925519429677112247847 38947388279144515668371771)
    ·
      refine ⟨58421082418716773502557657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38947388279144515668371771 58421082418716773502557657)
      ·
        refine ⟨43815811814037580126918243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58421082418716773502557657 43815811814037580126918243)
        ·
          refine ⟨65723717721056370190377365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43815811814037580126918243 65723717721056370190377365)
          ·
            refine ⟨3080799268174517352673939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65723717721056370190377365 3080799268174517352673939)
            ·
              refine ⟨4621198902261776029010909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080799268174517352673939 4621198902261776029010909)
              ·
                refine ⟨1732949588348166010879091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4621198902261776029010909 1732949588348166010879091)
                ·
                  refine ⟨2599424382522249016318637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732949588348166010879091 2599424382522249016318637)
                  ·
                    refine ⟨974784143445843381119489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599424382522249016318637 974784143445843381119489)
                    ·
                      rfl

theorem cell22_2847578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_2847578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847578 prefixEnd_2847578 := by exact prefixLift 2847578
  have htrace : WordTrace (prefixWord ++ tailWord_2847578) baseStart_2847578 baseEnd_2847578 := by
    simpa [prefixWord, tailWord_2847578, baseEnd_2847578] using wordTrace_append hprefix tailTrace_2847578
  have hstable : (prefixWord ++ tailWord_2847578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847578).length < 2 ^ (prefixWord ++ tailWord_2847578).sum := by decide
  have hdescent : baseEnd_2847578 < baseStart_2847578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847621 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_2847621 : Nat := 118140960795 + 2847621 * 2 ^ 59
def prefixEnd_2847621 : Nat := 4983230072969 + 3 ^ 40 * 2847621 * 2
def baseEnd_2847621 : Nat := 974798863224605602294357

theorem tailTrace_2847621 : CollatzResearch.WordTrace tailWord_2847621 prefixEnd_2847621 974798863224605602294357 := by
  unfold tailWord_2847621
  simp only [CollatzResearch.WordTrace]
  refine ⟨103861270416562926792806717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69240846944375284528537811 103861270416562926792806717)
  ·
    refine ⟨38947976406211097547302519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103861270416562926792806717 38947976406211097547302519)
    ·
      refine ⟨58421964609316646320953779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38947976406211097547302519 58421964609316646320953779)
      ·
        refine ⟨87632946913974969481430669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58421964609316646320953779 87632946913974969481430669)
        ·
          refine ⟨32862355092740613555536501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87632946913974969481430669 32862355092740613555536501)
          ·
            refine ⟨3080845789944432520831547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32862355092740613555536501 3080845789944432520831547)
            ·
              refine ⟨4621268684916648781247321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080845789944432520831547 4621268684916648781247321)
              ·
                refine ⟨3465951513687486585935491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4621268684916648781247321 3465951513687486585935491)
                ·
                  refine ⟨5198927270531229878903237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465951513687486585935491 5198927270531229878903237)
                  ·
                    refine ⟨974798863224605602294357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5198927270531229878903237 974798863224605602294357)
                    ·
                      rfl

theorem cell22_2847621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_2847621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847621 prefixEnd_2847621 := by exact prefixLift 2847621
  have htrace : WordTrace (prefixWord ++ tailWord_2847621) baseStart_2847621 baseEnd_2847621 := by
    simpa [prefixWord, tailWord_2847621, baseEnd_2847621] using wordTrace_append hprefix tailTrace_2847621
  have hstable : (prefixWord ++ tailWord_2847621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847621).length < 2 ^ (prefixWord ++ tailWord_2847621).sum := by decide
  have hdescent : baseEnd_2847621 < baseStart_2847621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847636 : List Nat := [2, 4, 2, 1, 1, 1, 2, 5, 4]
def baseStart_2847636 : Nat := 118140960795 + 2847636 * 2 ^ 59
def prefixEnd_2847636 : Nat := 4983230072969 + 3 ^ 40 * 2847636 * 2
def baseEnd_2847636 : Nat := 324934666010383521056437

theorem tailTrace_2847636 : CollatzResearch.WordTrace tailWord_2847636 prefixEnd_2847636 324934666010383521056437 := by
  unfold tailWord_2847636
  simp only [CollatzResearch.WordTrace]
  refine ⟨51930908755754292177301381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69241211674339056236401841 51930908755754292177301381)
  ·
    refine ⟨9737045391703929783244009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51930908755754292177301381 9737045391703929783244009)
    ·
      refine ⟨7302784043777947337433007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9737045391703929783244009 7302784043777947337433007)
      ·
        refine ⟨10954176065666921006149511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7302784043777947337433007 10954176065666921006149511)
        ·
          refine ⟨16431264098500381509224267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10954176065666921006149511 16431264098500381509224267)
          ·
            refine ⟨24646896147750572263836401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16431264098500381509224267 24646896147750572263836401)
            ·
              refine ⟨18485172110812929197877301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24646896147750572263836401 18485172110812929197877301)
              ·
                refine ⟨1732984885388712112300997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18485172110812929197877301 1732984885388712112300997)
                ·
                  refine ⟨324934666010383521056437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732984885388712112300997 324934666010383521056437)
                  ·
                    rfl

theorem cell22_2847636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_2847636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847636 prefixEnd_2847636 := by exact prefixLift 2847636
  have htrace : WordTrace (prefixWord ++ tailWord_2847636) baseStart_2847636 baseEnd_2847636 := by
    simpa [prefixWord, tailWord_2847636, baseEnd_2847636] using wordTrace_append hprefix tailTrace_2847636
  have hstable : (prefixWord ++ tailWord_2847636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847636).length < 2 ^ (prefixWord ++ tailWord_2847636).sum := by decide
  have hdescent : baseEnd_2847636 < baseStart_2847636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847647 : List Nat := [1, 1, 2, 5, 2, 11]
def baseStart_2847647 : Nat := 118140960795 + 2847647 * 2 ^ 59
def prefixEnd_2847647 : Nat := 4983230072969 + 3 ^ 40 * 2847647 * 2
def baseEnd_2847647 : Nat := 12034663747604323470917

theorem tailTrace_2847647 : CollatzResearch.WordTrace tailWord_2847647 prefixEnd_2847647 12034663747604323470917 := by
  unfold tailWord_2847647
  simp only [CollatzResearch.WordTrace]
  refine ⟨103862218714468733233253195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69241479142979155488835463 103862218714468733233253195)
  ·
    refine ⟨155793328071703099849879793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103862218714468733233253195 155793328071703099849879793)
    ·
      refine ⟨116844996053777324887409845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155793328071703099849879793 116844996053777324887409845)
      ·
        refine ⟨10954218380041624208194673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116844996053777324887409845 10954218380041624208194673)
        ·
          refine ⟨8215663785031218156146005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10954218380041624208194673 8215663785031218156146005)
          ·
            refine ⟨12034663747604323470917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8215663785031218156146005 12034663747604323470917)
            ·
              rfl

theorem cell22_2847647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 11].length) (baseStart_2847647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847647 prefixEnd_2847647 := by exact prefixLift 2847647
  have htrace : WordTrace (prefixWord ++ tailWord_2847647) baseStart_2847647 baseEnd_2847647 := by
    simpa [prefixWord, tailWord_2847647, baseEnd_2847647] using wordTrace_append hprefix tailTrace_2847647
  have hstable : (prefixWord ++ tailWord_2847647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847647).length < 2 ^ (prefixWord ++ tailWord_2847647).sum := by decide
  have hdescent : baseEnd_2847647 < baseStart_2847647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847668 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2847668 : Nat := 118140960795 + 2847668 * 2 ^ 59
def prefixEnd_2847668 : Nat := 4983230072969 + 3 ^ 40 * 2847668 * 2
def baseEnd_2847668 : Nat := 974814952285113146369213

theorem tailTrace_2847668 : CollatzResearch.WordTrace tailWord_2847668 prefixEnd_2847668 974814952285113146369213 := by
  unfold tailWord_2847668
  simp only [CollatzResearch.WordTrace]
  refine ⟨51931492323696326909883829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69241989764928435879845105 51931492323696326909883829)
  ·
    refine ⟨4868577405346530647801609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51931492323696326909883829 4868577405346530647801609)
    ·
      refine ⟨3651433054009897985851207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4868577405346530647801609 3651433054009897985851207)
      ·
        refine ⟨5477149581014846978776811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3651433054009897985851207 5477149581014846978776811)
        ·
          refine ⟨8215724371522270468165217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477149581014846978776811 8215724371522270468165217)
          ·
            refine ⟨6161793278641702851123913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8215724371522270468165217 6161793278641702851123913)
            ·
              refine ⟨4621344958981277138342935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6161793278641702851123913 4621344958981277138342935)
              ·
                refine ⟨6932017438471915707514403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4621344958981277138342935 6932017438471915707514403)
                ·
                  refine ⟨10398026157707873561271605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6932017438471915707514403 10398026157707873561271605)
                  ·
                    refine ⟨974814952285113146369213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10398026157707873561271605 974814952285113146369213)
                    ·
                      rfl

theorem cell22_2847668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2847668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847668 prefixEnd_2847668 := by exact prefixLift 2847668
  have htrace : WordTrace (prefixWord ++ tailWord_2847668) baseStart_2847668 baseEnd_2847668 := by
    simpa [prefixWord, tailWord_2847668, baseEnd_2847668] using wordTrace_append hprefix tailTrace_2847668
  have hstable : (prefixWord ++ tailWord_2847668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847668).length < 2 ^ (prefixWord ++ tailWord_2847668).sum := by decide
  have hdescent : baseEnd_2847668 < baseStart_2847668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847670 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_2847670 : Nat := 118140960795 + 2847670 * 2 ^ 59
def prefixEnd_2847670 : Nat := 4983230072969 + 3 ^ 40 * 2847670 * 2
def baseEnd_2847670 : Nat := 324938545641995269273069

theorem tailTrace_2847670 : CollatzResearch.WordTrace tailWord_2847670 prefixEnd_2847670 324938545641995269273069 := by
  unfold tailWord_2847670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491441099586588010083779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69242038395590272107560309 6491441099586588010083779)
  ·
    refine ⟨9737161649379882015125669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6491441099586588010083779 9737161649379882015125669)
    ·
      refine ⟨1825717809258727877836063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9737161649379882015125669 1825717809258727877836063)
      ·
        refine ⟨2738576713888091816754095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1825717809258727877836063 2738576713888091816754095)
        ·
          refine ⟨4107865070832137725131143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2738576713888091816754095 4107865070832137725131143)
          ·
            refine ⟨6161797606248206587696715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107865070832137725131143 6161797606248206587696715)
            ·
              refine ⟨9242696409372309881545073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6161797606248206587696715 9242696409372309881545073)
              ·
                refine ⟨6932022307029232411158805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9242696409372309881545073 6932022307029232411158805)
                ·
                  refine ⟨324938545641995269273069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6932022307029232411158805 324938545641995269273069)
                  ·
                    rfl

theorem cell22_2847670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_2847670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847670 prefixEnd_2847670 := by exact prefixLift 2847670
  have htrace : WordTrace (prefixWord ++ tailWord_2847670) baseStart_2847670 baseEnd_2847670 := by
    simpa [prefixWord, tailWord_2847670, baseEnd_2847670] using wordTrace_append hprefix tailTrace_2847670
  have hstable : (prefixWord ++ tailWord_2847670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847670).length < 2 ^ (prefixWord ++ tailWord_2847670).sum := by decide
  have hdescent : baseEnd_2847670 < baseStart_2847670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847756 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_2847756 : Nat := 118140960795 + 2847756 * 2 ^ 59
def prefixEnd_2847756 : Nat := 4983230072969 + 3 ^ 40 * 2847756 * 2
def baseEnd_2847756 : Nat := 974845076483510250168943

theorem tailTrace_2847756 : CollatzResearch.WordTrace tailWord_2847756 prefixEnd_2847756 974845076483510250168943 := by
  unfold tailWord_2847756
  simp only [CollatzResearch.WordTrace]
  refine ⟨51933097135536922424485561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69244129514049229899314081 51933097135536922424485561)
  ·
    refine ⟨38949822851652691818364171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51933097135536922424485561 38949822851652691818364171)
    ·
      refine ⟨58424734277479037727546257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38949822851652691818364171 58424734277479037727546257)
      ·
        refine ⟨43818550708109278295659693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58424734277479037727546257 43818550708109278295659693)
        ·
          refine ⟨16431956515540979360872385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43818550708109278295659693 16431956515540979360872385)
          ·
            refine ⟨12323967386655734520654289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16431956515540979360872385 12323967386655734520654289)
            ·
              refine ⟨9242975539991800890490717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12323967386655734520654289 9242975539991800890490717)
              ·
                refine ⟨3466115827496925333934019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9242975539991800890490717 3466115827496925333934019)
                ·
                  refine ⟨5199173741245388000901029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466115827496925333934019 5199173741245388000901029)
                  ·
                    refine ⟨974845076483510250168943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5199173741245388000901029 974845076483510250168943)
                    ·
                      rfl

theorem cell22_2847756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_2847756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847756 prefixEnd_2847756 := by exact prefixLift 2847756
  have htrace : WordTrace (prefixWord ++ tailWord_2847756) baseStart_2847756 baseEnd_2847756 := by
    simpa [prefixWord, tailWord_2847756, baseEnd_2847756] using wordTrace_append hprefix tailTrace_2847756
  have hstable : (prefixWord ++ tailWord_2847756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847756).length < 2 ^ (prefixWord ++ tailWord_2847756).sum := by decide
  have hdescent : baseEnd_2847756 < baseStart_2847756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847801 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_2847801 : Nat := 118140960795 + 2847801 * 2 ^ 59
def prefixEnd_2847801 : Nat := 4983230072969 + 3 ^ 40 * 2847801 * 2
def baseEnd_2847801 : Nat := 974860480903145132793805

theorem tailTrace_2847801 : CollatzResearch.WordTrace tailWord_2847801 prefixEnd_2847801 974860480903145132793805 := by
  unfold tailWord_2847801
  simp only [CollatzResearch.WordTrace]
  refine ⟨103867835555910817534359257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69245223703940545022906171 103867835555910817534359257)
  ·
    refine ⟨77900876666933113150769443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103867835555910817534359257 77900876666933113150769443)
    ·
      refine ⟨116851315000399669726154165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77900876666933113150769443 116851315000399669726154165)
      ·
        refine ⟨10954810781287469036826953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116851315000399669726154165 10954810781287469036826953)
        ·
          refine ⟨8216108085965601777620215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10954810781287469036826953 8216108085965601777620215)
          ·
            refine ⟨12324162128948402666430323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216108085965601777620215 12324162128948402666430323)
            ·
              refine ⟨18486243193422603999645485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12324162128948402666430323 18486243193422603999645485)
              ·
                refine ⟨6932341197533476499867057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18486243193422603999645485 6932341197533476499867057)
                ·
                  refine ⟨5199255898150107374900293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6932341197533476499867057 5199255898150107374900293)
                  ·
                    refine ⟨974860480903145132793805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5199255898150107374900293 974860480903145132793805)
                    ·
                      rfl

theorem cell22_2847801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_2847801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847801 prefixEnd_2847801 := by exact prefixLift 2847801
  have htrace : WordTrace (prefixWord ++ tailWord_2847801) baseStart_2847801 baseEnd_2847801 := by
    simpa [prefixWord, tailWord_2847801, baseEnd_2847801] using wordTrace_append hprefix tailTrace_2847801
  have hstable : (prefixWord ++ tailWord_2847801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847801).length < 2 ^ (prefixWord ++ tailWord_2847801).sum := by decide
  have hdescent : baseEnd_2847801 < baseStart_2847801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847829 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2847829 : Nat := 118140960795 + 2847829 * 2 ^ 59
def prefixEnd_2847829 : Nat := 4983230072969 + 3 ^ 40 * 2847829 * 2
def baseEnd_2847829 : Nat := 974870065875362393093719

theorem tailTrace_2847829 : CollatzResearch.WordTrace tailWord_2847829 prefixEnd_2847829 974870065875362393093719 := by
  unfold tailWord_2847829
  simp only [CollatzResearch.WordTrace]
  refine ⟨103868856799809378316378541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69245904533206252210919027 103868856799809378316378541)
  ·
    refine ⟨38950821299928516868641953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103868856799809378316378541 38950821299928516868641953)
    ·
      refine ⟨29213115974946387651481465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38950821299928516868641953 29213115974946387651481465)
      ·
        refine ⟨21909836981209790738611099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29213115974946387651481465 21909836981209790738611099)
        ·
          refine ⟨32864755471814686107916649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21909836981209790738611099 32864755471814686107916649)
          ·
            refine ⟨24648566603861014580937487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32864755471814686107916649 24648566603861014580937487)
            ·
              refine ⟨36972849905791521871406231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24648566603861014580937487 36972849905791521871406231)
              ·
                refine ⟨55459274858687282807109347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36972849905791521871406231 55459274858687282807109347)
                ·
                  refine ⟨83188912288030924210664021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55459274858687282807109347 83188912288030924210664021)
                  ·
                    refine ⟨974870065875362393093719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83188912288030924210664021 974870065875362393093719)
                    ·
                      rfl

theorem cell22_2847829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2847829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847829 prefixEnd_2847829 := by exact prefixLift 2847829
  have htrace : WordTrace (prefixWord ++ tailWord_2847829) baseStart_2847829 baseEnd_2847829 := by
    simpa [prefixWord, tailWord_2847829, baseEnd_2847829] using wordTrace_append hprefix tailTrace_2847829
  have hstable : (prefixWord ++ tailWord_2847829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847829).length < 2 ^ (prefixWord ++ tailWord_2847829).sum := by decide
  have hdescent : baseEnd_2847829 < baseStart_2847829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847831 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 3, 3]
def baseStart_2847831 : Nat := 118140960795 + 2847831 * 2 ^ 59
def prefixEnd_2847831 : Nat := 4983230072969 + 3 ^ 40 * 2847831 * 2
def baseEnd_2847831 : Nat := 974870750516235054543713

theorem tailTrace_2847831 : CollatzResearch.WordTrace tailWord_2847831 prefixEnd_2847831 974870750516235054543713 := by
  unfold tailWord_2847831
  simp only [CollatzResearch.WordTrace]
  refine ⟨103868929745802132657951347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69245953163868088438634231 103868929745802132657951347)
  ·
    refine ⟨155803394618703198986927021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103868929745802132657951347 155803394618703198986927021)
    ·
      refine ⟨58426272982013699620097633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155803394618703198986927021 58426272982013699620097633)
      ·
        refine ⟨43819704736510274715073225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58426272982013699620097633 43819704736510274715073225)
        ·
          refine ⟨32864778552382706036304919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43819704736510274715073225 32864778552382706036304919)
          ·
            refine ⟨49297167828574059054457379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32864778552382706036304919 49297167828574059054457379)
            ·
              refine ⟨73945751742861088581686069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49297167828574059054457379 73945751742861088581686069)
              ·
                refine ⟨6932414225893227054533069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73945751742861088581686069 6932414225893227054533069)
                ·
                  refine ⟨2599655334709960145449901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6932414225893227054533069 2599655334709960145449901)
                  ·
                    refine ⟨974870750516235054543713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599655334709960145449901 974870750516235054543713)
                    ·
                      rfl

theorem cell22_2847831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_2847831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847831 prefixEnd_2847831 := by exact prefixLift 2847831
  have htrace : WordTrace (prefixWord ++ tailWord_2847831) baseStart_2847831 baseEnd_2847831 := by
    simpa [prefixWord, tailWord_2847831, baseEnd_2847831] using wordTrace_append hprefix tailTrace_2847831
  have hstable : (prefixWord ++ tailWord_2847831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847831).length < 2 ^ (prefixWord ++ tailWord_2847831).sum := by decide
  have hdescent : baseEnd_2847831 < baseStart_2847831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847844 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 9]
def baseStart_2847844 : Nat := 118140960795 + 2847844 * 2 ^ 59
def prefixEnd_2847844 : Nat := 4983230072969 + 3 ^ 40 * 2847844 * 2
def baseEnd_2847844 : Nat := 324958400227302451322891

theorem tailTrace_2847844 : CollatzResearch.WordTrace tailWord_2847844 prefixEnd_2847844 324958400227302451322891 := by
  unfold tailWord_2847844
  simp only [CollatzResearch.WordTrace]
  refine ⟨51934701947377517939087293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69246269263170023918783057 51934701947377517939087293)
  ·
    refine ⟨19475513230266569227157735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51934701947377517939087293 19475513230266569227157735)
    ·
      refine ⟨29213269845399853840736603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19475513230266569227157735 29213269845399853840736603)
      ·
        refine ⟨43819904768099780761104905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29213269845399853840736603 43819904768099780761104905)
        ·
          refine ⟨32864928576074835570828679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43819904768099780761104905 32864928576074835570828679)
          ·
            refine ⟨49297392864112253356243019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32864928576074835570828679 49297392864112253356243019)
            ·
              refine ⟨73946089296168380034364529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49297392864112253356243019 73946089296168380034364529)
              ·
                refine ⟨55459566972126285025773397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73946089296168380034364529 55459566972126285025773397)
                ·
                  refine ⟨324958400227302451322891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55459566972126285025773397 324958400227302451322891)
                  ·
                    rfl

theorem cell22_2847844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_2847844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847844 prefixEnd_2847844 := by exact prefixLift 2847844
  have htrace : WordTrace (prefixWord ++ tailWord_2847844) baseStart_2847844 baseEnd_2847844 := by
    simpa [prefixWord, tailWord_2847844, baseEnd_2847844] using wordTrace_append hprefix tailTrace_2847844
  have hstable : (prefixWord ++ tailWord_2847844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847844).length < 2 ^ (prefixWord ++ tailWord_2847844).sum := by decide
  have hdescent : baseEnd_2847844 < baseStart_2847844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847876 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2847876 : Nat := 118140960795 + 2847876 * 2 ^ 59
def prefixEnd_2847876 : Nat := 4983230072969 + 3 ^ 40 * 2847876 * 2
def baseEnd_2847876 : Nat := 974886154935869937168575

theorem tailTrace_2847876 : CollatzResearch.WordTrace tailWord_2847876 prefixEnd_2847876 974886154935869937168575 := by
  unfold tailWord_2847876
  simp only [CollatzResearch.WordTrace]
  refine ⟨51935285515319552671669741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69247047353759403562226321 51935285515319552671669741)
  ·
    refine ⟨19475732068244832251876153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51935285515319552671669741 19475732068244832251876153)
    ·
      refine ⟨14606799051183624188907115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19475732068244832251876153 14606799051183624188907115)
      ·
        refine ⟨21910198576775436283360673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14606799051183624188907115 21910198576775436283360673)
        ·
          refine ⟨16432648932581577212520505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21910198576775436283360673 16432648932581577212520505)
          ·
            refine ⟨12324486699436182909390379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16432648932581577212520505 12324486699436182909390379)
            ·
              refine ⟨18486730049154274364085569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12324486699436182909390379 18486730049154274364085569)
              ·
                refine ⟨13865047536865705773064177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18486730049154274364085569 13865047536865705773064177)
                ·
                  refine ⟨10398785652649279329798133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13865047536865705773064177 10398785652649279329798133)
                  ·
                    refine ⟨974886154935869937168575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10398785652649279329798133 974886154935869937168575)
                    ·
                      rfl

theorem cell22_2847876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2847876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847876 prefixEnd_2847876 := by exact prefixLift 2847876
  have htrace : WordTrace (prefixWord ++ tailWord_2847876) baseStart_2847876 baseEnd_2847876 := by
    simpa [prefixWord, tailWord_2847876, baseEnd_2847876] using wordTrace_append hprefix tailTrace_2847876
  have hstable : (prefixWord ++ tailWord_2847876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847876).length < 2 ^ (prefixWord ++ tailWord_2847876).sum := by decide
  have hdescent : baseEnd_2847876 < baseStart_2847876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847908 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_2847908 : Nat := 118140960795 + 2847908 * 2 ^ 59
def prefixEnd_2847908 : Nat := 4983230072969 + 3 ^ 40 * 2847908 * 2
def baseEnd_2847908 : Nat := 974897109189832520368477

theorem tailTrace_2847908 : CollatzResearch.WordTrace tailWord_2847908 prefixEnd_2847908 974897109189832520368477 := by
  unfold tailWord_2847908
  simp only [CollatzResearch.WordTrace]
  refine ⟨51935869083261587404252189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69247825444348783205669585 51935869083261587404252189)
  ·
    refine ⟨19475950906223095276594571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51935869083261587404252189 19475950906223095276594571)
    ·
      refine ⟨29213926359334642914891857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19475950906223095276594571 29213926359334642914891857)
      ·
        refine ⟨21910444769500982186168893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29213926359334642914891857 21910444769500982186168893)
        ·
          refine ⟨8216416788562868319813335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21910444769500982186168893 8216416788562868319813335)
          ·
            refine ⟨12324625182844302479720003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216416788562868319813335 12324625182844302479720003)
            ·
              refine ⟨18486937774266453719580005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12324625182844302479720003 18486937774266453719580005)
              ·
                refine ⟨3466300832674960072421251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18486937774266453719580005 3466300832674960072421251)
                ·
                  refine ⟨5199451249012440108631877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466300832674960072421251 5199451249012440108631877)
                  ·
                    refine ⟨974897109189832520368477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5199451249012440108631877 974897109189832520368477)
                    ·
                      rfl

theorem cell22_2847908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_2847908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847908 prefixEnd_2847908 := by exact prefixLift 2847908
  have htrace : WordTrace (prefixWord ++ tailWord_2847908) baseStart_2847908 baseEnd_2847908 := by
    simpa [prefixWord, tailWord_2847908, baseEnd_2847908] using wordTrace_append hprefix tailTrace_2847908
  have hstable : (prefixWord ++ tailWord_2847908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847908).length < 2 ^ (prefixWord ++ tailWord_2847908).sum := by decide
  have hdescent : baseEnd_2847908 < baseStart_2847908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847923 : List Nat := [1, 1, 1, 2, 3, 2, 5, 3, 4]
def baseStart_2847923 : Nat := 118140960795 + 2847923 * 2 ^ 59
def prefixEnd_2847923 : Nat := 4983230072969 + 3 ^ 40 * 2847923 * 2
def baseEnd_2847923 : Nat := 324967414665459160414477

theorem tailTrace_2847923 : CollatzResearch.WordTrace tailWord_2847923 prefixEnd_2847923 324967414665459160414477 := by
  unfold tailWord_2847923
  simp only [CollatzResearch.WordTrace]
  refine ⟨103872285261468832370300423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69248190174312554913533615 103872285261468832370300423)
  ·
    refine ⟨155808427892203248555450635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103872285261468832370300423 155808427892203248555450635)
    ·
      refine ⟨233712641838304872833175953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155808427892203248555450635 233712641838304872833175953)
      ·
        refine ⟨175284481378728654624881965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233712641838304872833175953 175284481378728654624881965)
        ·
          refine ⟨65731680517023245484330737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175284481378728654624881965 65731680517023245484330737)
          ·
            refine ⟨49298760387767434113248053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65731680517023245484330737 49298760387767434113248053)
            ·
              refine ⟨4621758786353196948117005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49298760387767434113248053 4621758786353196948117005)
              ·
                refine ⟨1733159544882448855543877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4621758786353196948117005 1733159544882448855543877)
                ·
                  refine ⟨324967414665459160414477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733159544882448855543877 324967414665459160414477)
                  ·
                    rfl

theorem cell22_2847923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 4].length) (baseStart_2847923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847923 prefixEnd_2847923 := by exact prefixLift 2847923
  have htrace : WordTrace (prefixWord ++ tailWord_2847923) baseStart_2847923 baseEnd_2847923 := by
    simpa [prefixWord, tailWord_2847923, baseEnd_2847923] using wordTrace_append hprefix tailTrace_2847923
  have hstable : (prefixWord ++ tailWord_2847923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847923).length < 2 ^ (prefixWord ++ tailWord_2847923).sum := by decide
  have hdescent : baseEnd_2847923 < baseStart_2847923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847940 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 6]
def baseStart_2847940 : Nat := 118140960795 + 2847940 * 2 ^ 59
def prefixEnd_2847940 : Nat := 4983230072969 + 3 ^ 40 * 2847940 * 2
def baseEnd_2847940 : Nat := 324969354481265034522793

theorem tailTrace_2847940 : CollatzResearch.WordTrace tailWord_2847940 prefixEnd_2847940 324969354481265034522793 := by
  unfold tailWord_2847940
  simp only [CollatzResearch.WordTrace]
  refine ⟨51936452651203622136834637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69248603534938162849112849 51936452651203622136834637)
  ·
    refine ⟨19476169744201358301312989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51936452651203622136834637 19476169744201358301312989)
    ·
      refine ⟨7303563654075509362992371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19476169744201358301312989 7303563654075509362992371)
      ·
        refine ⟨10955345481113264044488557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7303563654075509362992371 10955345481113264044488557)
        ·
          refine ⟨4108254555417474016683209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10955345481113264044488557 4108254555417474016683209)
          ·
            refine ⟨3081190916563105512512407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108254555417474016683209 3081190916563105512512407)
            ·
              refine ⟨4621786374844658268768611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081190916563105512512407 4621786374844658268768611)
              ·
                refine ⟨6932679562266987403152917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4621786374844658268768611 6932679562266987403152917)
                ·
                  refine ⟨324969354481265034522793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6932679562266987403152917 324969354481265034522793)
                  ·
                    rfl

theorem cell22_2847940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_2847940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847940 prefixEnd_2847940 := by exact prefixLift 2847940
  have htrace : WordTrace (prefixWord ++ tailWord_2847940) baseStart_2847940 baseEnd_2847940 := by
    simpa [prefixWord, tailWord_2847940, baseEnd_2847940] using wordTrace_append hprefix tailTrace_2847940
  have hstable : (prefixWord ++ tailWord_2847940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847940).length < 2 ^ (prefixWord ++ tailWord_2847940).sum := by decide
  have hdescent : baseEnd_2847940 < baseStart_2847940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847998 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2847998 : Nat := 118140960795 + 2847998 * 2 ^ 59
def prefixEnd_2847998 : Nat := 4983230072969 + 3 ^ 40 * 2847998 * 2
def baseEnd_2847998 : Nat := 974927918029102285618201

theorem tailTrace_2847998 : CollatzResearch.WordTrace tailWord_2847998 prefixEnd_2847998 974927918029102285618201 := by
  unfold tailWord_2847998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12984377592024640022410081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69250013824131413452853765 12984377592024640022410081)
  ·
    refine ⟨9738283194018480016807561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12984377592024640022410081 9738283194018480016807561)
    ·
      refine ⟨7303712395513860012605671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9738283194018480016807561 7303712395513860012605671)
      ·
        refine ⟨10955568593270790018908507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7303712395513860012605671 10955568593270790018908507)
        ·
          refine ⟨16433352889906185028362761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10955568593270790018908507 16433352889906185028362761)
          ·
            refine ⟨12325014667429638771272071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16433352889906185028362761 12325014667429638771272071)
            ·
              refine ⟨18487522001144458156908107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12325014667429638771272071 18487522001144458156908107)
              ·
                refine ⟨27731283001716687235362161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18487522001144458156908107 27731283001716687235362161)
                ·
                  refine ⟨20798462251287515426521621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27731283001716687235362161 20798462251287515426521621)
                  ·
                    refine ⟨974927918029102285618201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20798462251287515426521621 974927918029102285618201)
                    ·
                      rfl

theorem cell22_2847998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2847998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2847998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2847998 prefixEnd_2847998 := by exact prefixLift 2847998
  have htrace : WordTrace (prefixWord ++ tailWord_2847998) baseStart_2847998 baseEnd_2847998 := by
    simpa [prefixWord, tailWord_2847998, baseEnd_2847998] using wordTrace_append hprefix tailTrace_2847998
  have hstable : (prefixWord ++ tailWord_2847998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847998).length < 2 ^ (prefixWord ++ tailWord_2847998).sum := by decide
  have hdescent : baseEnd_2847998 < baseStart_2847998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848002 : List Nat := [3, 4, 1, 1, 4, 1, 1, 7]
def baseStart_2848002 : Nat := 118140960795 + 2848002 * 2 ^ 59
def prefixEnd_2848002 : Nat := 4983230072969 + 3 ^ 40 * 2848002 * 2
def baseEnd_2848002 : Nat := 108325476367871956502021

theorem tailTrace_2848002 : CollatzResearch.WordTrace tailWord_2848002 prefixEnd_2848002 108325476367871956502021 := by
  unfold tailWord_2848002
  simp only [CollatzResearch.WordTrace]
  refine ⟨25968791657045657215606565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69250111085455085908284173 25968791657045657215606565)
  ·
    refine ⟨4869148435696060727926231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25968791657045657215606565 4869148435696060727926231)
    ·
      refine ⟨7303722653544091091889347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4869148435696060727926231 7303722653544091091889347)
      ·
        refine ⟨10955583980316136637834021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7303722653544091091889347 10955583980316136637834021)
        ·
          refine ⟨2054171996309275619593879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10955583980316136637834021 2054171996309275619593879)
          ·
            refine ⟨3081257994463913429390819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054171996309275619593879 3081257994463913429390819)
            ·
              refine ⟨4621886991695870144086229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081257994463913429390819 4621886991695870144086229)
              ·
                refine ⟨108325476367871956502021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4621886991695870144086229 108325476367871956502021)
                ·
                  rfl

theorem cell22_2848002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_2848002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848002 prefixEnd_2848002 := by exact prefixLift 2848002
  have htrace : WordTrace (prefixWord ++ tailWord_2848002) baseStart_2848002 baseEnd_2848002 := by
    simpa [prefixWord, tailWord_2848002, baseEnd_2848002] using wordTrace_append hprefix tailTrace_2848002
  have hstable : (prefixWord ++ tailWord_2848002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848002).length < 2 ^ (prefixWord ++ tailWord_2848002).sum := by decide
  have hdescent : baseEnd_2848002 < baseStart_2848002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848011 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 1, 7]
def baseStart_2848011 : Nat := 118140960795 + 2848011 * 2 ^ 59
def prefixEnd_2848011 : Nat := 4983230072969 + 3 ^ 40 * 2848011 * 2
def baseEnd_2848011 : Nat := 974932368194774585043161

theorem tailTrace_2848011 : CollatzResearch.WordTrace tailWord_2848011 prefixEnd_2848011 974932368194774585043161 := by
  unfold tailWord_2848011
  simp only [CollatzResearch.WordTrace]
  refine ⟨103875494885150023399503887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69250329923433348933002591 103875494885150023399503887)
  ·
    refine ⟨155813242327725035099255831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103875494885150023399503887 155813242327725035099255831)
    ·
      refine ⟨233719863491587552648883747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155813242327725035099255831 233719863491587552648883747)
      ·
        refine ⟨350579795237381328973325621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233719863491587552648883747 350579795237381328973325621)
        ·
          refine ⟨32866855803504499591249277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 350579795237381328973325621 32866855803504499591249277)
          ·
            refine ⟨12325070926314187346718479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32866855803504499591249277 12325070926314187346718479)
            ·
              refine ⟨18487606389471281020077719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12325070926314187346718479 18487606389471281020077719)
              ·
                refine ⟨27731409584206921530116579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18487606389471281020077719 27731409584206921530116579)
                ·
                  refine ⟨41597114376310382295174869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27731409584206921530116579 41597114376310382295174869)
                  ·
                    refine ⟨974932368194774585043161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41597114376310382295174869 974932368194774585043161)
                    ·
                      rfl

theorem cell22_2848011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_2848011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848011 prefixEnd_2848011 := by exact prefixLift 2848011
  have htrace : WordTrace (prefixWord ++ tailWord_2848011) baseStart_2848011 baseEnd_2848011 := by
    simpa [prefixWord, tailWord_2848011, baseEnd_2848011] using wordTrace_append hprefix tailTrace_2848011
  have hstable : (prefixWord ++ tailWord_2848011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848011).length < 2 ^ (prefixWord ++ tailWord_2848011).sum := by decide
  have hdescent : baseEnd_2848011 < baseStart_2848011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848034 : List Nat := [3, 3, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_2848034 : Nat := 118140960795 + 2848034 * 2 ^ 59
def prefixEnd_2848034 : Nat := 4983230072969 + 3 ^ 40 * 2848034 * 2
def baseEnd_2848034 : Nat := 974940241564810191718091

theorem tailTrace_2848034 : CollatzResearch.WordTrace tailWord_2848034 prefixEnd_2848034 974940241564810191718091 := by
  unfold tailWord_2848034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25969083441016674581897789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69250889176044465551727437 25969083441016674581897789)
  ·
    refine ⟨9738406290381252968211671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25969083441016674581897789 9738406290381252968211671)
    ·
      refine ⟨14607609435571879452317507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9738406290381252968211671 14607609435571879452317507)
      ·
        refine ⟨21911414153357819178476261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14607609435571879452317507 21911414153357819178476261)
        ·
          refine ⟨4108390153754591095964299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21911414153357819178476261 4108390153754591095964299)
          ·
            refine ⟨6162585230631886643946449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4108390153754591095964299 6162585230631886643946449)
            ·
              refine ⟨4621938922973914982959837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6162585230631886643946449 4621938922973914982959837)
              ·
                refine ⟨1733227096115218118609939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4621938922973914982959837 1733227096115218118609939)
                ·
                  refine ⟨2599840644172827177914909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733227096115218118609939 2599840644172827177914909)
                  ·
                    refine ⟨974940241564810191718091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2599840644172827177914909 974940241564810191718091)
                    ·
                      rfl

theorem cell22_2848034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_2848034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848034 prefixEnd_2848034 := by exact prefixLift 2848034
  have htrace : WordTrace (prefixWord ++ tailWord_2848034) baseStart_2848034 baseEnd_2848034 := by
    simpa [prefixWord, tailWord_2848034, baseEnd_2848034] using wordTrace_append hprefix tailTrace_2848034
  have hstable : (prefixWord ++ tailWord_2848034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848034).length < 2 ^ (prefixWord ++ tailWord_2848034).sum := by decide
  have hdescent : baseEnd_2848034 < baseStart_2848034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848045 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2848045 : Nat := 118140960795 + 2848045 * 2 ^ 59
def prefixEnd_2848045 : Nat := 4983230072969 + 3 ^ 40 * 2848045 * 2
def baseEnd_2848045 : Nat := 974944007089609829693057

theorem tailTrace_2848045 : CollatzResearch.WordTrace tailWord_2848045 prefixEnd_2848045 974944007089609829693057 := by
  unfold tailWord_2848045
  simp only [CollatzResearch.WordTrace]
  refine ⟨103876734967026847206241589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69251156644684564804161059 103876734967026847206241589)
  ·
    refine ⟨9738443903158766925585149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103876734967026847206241589 9738443903158766925585149)
    ·
      refine ⟨3651916463684537597094431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9738443903158766925585149 3651916463684537597094431)
      ·
        refine ⟨5477874695526806395641647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3651916463684537597094431 5477874695526806395641647)
        ·
          refine ⟨8216812043290209593462471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477874695526806395641647 8216812043290209593462471)
          ·
            refine ⟨12325218064935314390193707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216812043290209593462471 12325218064935314390193707)
            ·
              refine ⟨18487827097402971585290561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12325218064935314390193707 18487827097402971585290561)
              ·
                refine ⟨13865870323052228688967921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18487827097402971585290561 13865870323052228688967921)
                ·
                  refine ⟨10399402742289171516725941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13865870323052228688967921 10399402742289171516725941)
                  ·
                    refine ⟨974944007089609829693057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10399402742289171516725941 974944007089609829693057)
                    ·
                      rfl

theorem cell22_2848045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2848045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848045 prefixEnd_2848045 := by exact prefixLift 2848045
  have htrace : WordTrace (prefixWord ++ tailWord_2848045) baseStart_2848045 baseEnd_2848045 := by
    simpa [prefixWord, tailWord_2848045, baseEnd_2848045] using wordTrace_append hprefix tailTrace_2848045
  have hstable : (prefixWord ++ tailWord_2848045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848045).length < 2 ^ (prefixWord ++ tailWord_2848045).sum := by decide
  have hdescent : baseEnd_2848045 < baseStart_2848045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848058 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_2848058 : Nat := 118140960795 + 2848058 * 2 ^ 59
def prefixEnd_2848058 : Nat := 4983230072969 + 3 ^ 40 * 2848058 * 2
def baseEnd_2848058 : Nat := 324982819085094043039339

theorem tailTrace_2848058 : CollatzResearch.WordTrace tailWord_2848058 prefixEnd_2848058 324982819085094043039339 := by
  unfold tailWord_2848058
  simp only [CollatzResearch.WordTrace]
  refine ⟨25969302278994937606616207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69251472743986500284309885 25969302278994937606616207)
  ·
    refine ⟨38953953418492406409924311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25969302278994937606616207 38953953418492406409924311)
    ·
      refine ⟨58430930127738609614886467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38953953418492406409924311 58430930127738609614886467)
      ·
        refine ⟨87646395191607914422329701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58430930127738609614886467 87646395191607914422329701)
        ·
          refine ⟨16433699098426483954186819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87646395191607914422329701 16433699098426483954186819)
          ·
            refine ⟨24650548647639725931280229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16433699098426483954186819 24650548647639725931280229)
            ·
              refine ⟨4621977871432448612115043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24650548647639725931280229 4621977871432448612115043)
              ·
                refine ⟨6932966807148672918172565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4621977871432448612115043 6932966807148672918172565)
                ·
                  refine ⟨324982819085094043039339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6932966807148672918172565 324982819085094043039339)
                  ·
                    rfl

theorem cell22_2848058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_2848058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848058 prefixEnd_2848058 := by exact prefixLift 2848058
  have htrace : WordTrace (prefixWord ++ tailWord_2848058) baseStart_2848058 baseEnd_2848058 := by
    simpa [prefixWord, tailWord_2848058, baseEnd_2848058] using wordTrace_append hprefix tailTrace_2848058
  have hstable : (prefixWord ++ tailWord_2848058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848058).length < 2 ^ (prefixWord ++ tailWord_2848058).sum := by decide
  have hdescent : baseEnd_2848058 < baseStart_2848058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848073 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_2848073 : Nat := 118140960795 + 2848073 * 2 ^ 59
def prefixEnd_2848073 : Nat := 4983230072969 + 3 ^ 40 * 2848073 * 2
def baseEnd_2848073 : Nat := 974953592061827089992971

theorem tailTrace_2848073 : CollatzResearch.WordTrace tailWord_2848073 prefixEnd_2848073 974953592061827089992971 := by
  unfold tailWord_2848073
  simp only [CollatzResearch.WordTrace]
  refine ⟨103877756210925407988260873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69251837473950271992173915 103877756210925407988260873)
  ·
    refine ⟨77908317158194055991195655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103877756210925407988260873 77908317158194055991195655)
    ·
      refine ⟨116862475737291083986793483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77908317158194055991195655 116862475737291083986793483)
      ·
        refine ⟨175293713605936625980190225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116862475737291083986793483 175293713605936625980190225)
        ·
          refine ⟨131470285204452469485142669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175293713605936625980190225 131470285204452469485142669)
          ·
            refine ⟨49301356951669676056928501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131470285204452469485142669 49301356951669676056928501)
            ·
              refine ⟨4622002214219032130337047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49301356951669676056928501 4622002214219032130337047)
              ·
                refine ⟨6933003321328548195505571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622002214219032130337047 6933003321328548195505571)
                ·
                  refine ⟨10399504981992822293258357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6933003321328548195505571 10399504981992822293258357)
                  ·
                    refine ⟨974953592061827089992971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10399504981992822293258357 974953592061827089992971)
                    ·
                      rfl

theorem cell22_2848073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_2848073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848073 prefixEnd_2848073 := by exact prefixLift 2848073
  have htrace : WordTrace (prefixWord ++ tailWord_2848073) baseStart_2848073 baseEnd_2848073 := by
    simpa [prefixWord, tailWord_2848073, baseEnd_2848073] using wordTrace_append hprefix tailTrace_2848073
  have hstable : (prefixWord ++ tailWord_2848073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848073).length < 2 ^ (prefixWord ++ tailWord_2848073).sum := by decide
  have hdescent : baseEnd_2848073 < baseStart_2848073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848088 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_2848088 : Nat := 118140960795 + 2848088 * 2 ^ 59
def prefixEnd_2848088 : Nat := 4983230072969 + 3 ^ 40 * 2848088 * 2
def baseEnd_2848088 : Nat := 974958726868372050867925

theorem tailTrace_2848088 : CollatzResearch.WordTrace tailWord_2848088 prefixEnd_2848088 974958726868372050867925 := by
  unfold tailWord_2848088
  simp only [CollatzResearch.WordTrace]
  refine ⟨51939151652935532775028459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69252202203914043700037945 51939151652935532775028459)
  ·
    refine ⟨77908727479403299162542689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51939151652935532775028459 77908727479403299162542689)
    ·
      refine ⟨58431545609552474371907017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77908727479403299162542689 58431545609552474371907017)
      ·
        refine ⟨43823659207164355778930263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58431545609552474371907017 43823659207164355778930263)
        ·
          refine ⟨65735488810746533668395395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43823659207164355778930263 65735488810746533668395395)
          ·
            refine ⟨98603233216119800502593093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65735488810746533668395395 98603233216119800502593093)
            ·
              refine ⟨18488106228022462594236205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98603233216119800502593093 18488106228022462594236205)
              ·
                refine ⟨6933039835508423472838577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18488106228022462594236205 6933039835508423472838577)
                ·
                  refine ⟨5199779876631317604628933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6933039835508423472838577 5199779876631317604628933)
                  ·
                    refine ⟨974958726868372050867925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5199779876631317604628933 974958726868372050867925)
                    ·
                      rfl

theorem cell22_2848088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_2848088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848088 prefixEnd_2848088 := by exact prefixLift 2848088
  have htrace : WordTrace (prefixWord ++ tailWord_2848088) baseStart_2848088 baseEnd_2848088 := by
    simpa [prefixWord, tailWord_2848088, baseEnd_2848088] using wordTrace_append hprefix tailTrace_2848088
  have hstable : (prefixWord ++ tailWord_2848088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848088).length < 2 ^ (prefixWord ++ tailWord_2848088).sum := by decide
  have hdescent : baseEnd_2848088 < baseStart_2848088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848163 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 2, 5]
def baseStart_2848163 : Nat := 118140960795 + 2848163 * 2 ^ 59
def prefixEnd_2848163 : Nat := 4983230072969 + 3 ^ 40 * 2848163 * 2
def baseEnd_2848163 : Nat := 974984400901096855242695

theorem tailTrace_2848163 : CollatzResearch.WordTrace tailWord_2848163 prefixEnd_2848163 974984400901096855242695 := by
  unfold tailWord_2848163
  simp only [CollatzResearch.WordTrace]
  refine ⟨103881038780599353359037143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69254025853732902239358095 103881038780599353359037143)
  ·
    refine ⟨155821558170899030038555715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103881038780599353359037143 155821558170899030038555715)
    ·
      refine ⟨233732337256348545057833573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155821558170899030038555715 233732337256348545057833573)
      ·
        refine ⟨43824813235565352198343795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233732337256348545057833573 43824813235565352198343795)
        ·
          refine ⟨65737219853348028297515693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43824813235565352198343795 65737219853348028297515693)
          ·
            refine ⟨24651457445005510611568385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65737219853348028297515693 24651457445005510611568385)
            ·
              refine ⟨18488593083754132958676289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24651457445005510611568385 18488593083754132958676289)
              ·
                refine ⟨13866444812815599719007217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18488593083754132958676289 13866444812815599719007217)
                ·
                  refine ⟨10399833609611699789255413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13866444812815599719007217 10399833609611699789255413)
                  ·
                    refine ⟨974984400901096855242695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10399833609611699789255413 974984400901096855242695)
                    ·
                      rfl

theorem cell22_2848163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_2848163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848163 prefixEnd_2848163 := by exact prefixLift 2848163
  have htrace : WordTrace (prefixWord ++ tailWord_2848163) baseStart_2848163 baseEnd_2848163 := by
    simpa [prefixWord, tailWord_2848163, baseEnd_2848163] using wordTrace_append hprefix tailTrace_2848163
  have hstable : (prefixWord ++ tailWord_2848163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848163).length < 2 ^ (prefixWord ++ tailWord_2848163).sum := by decide
  have hdescent : baseEnd_2848163 < baseStart_2848163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848227 : List Nat := [1, 1, 1, 6, 2, 1, 2, 4, 4]
def baseStart_2848227 : Nat := 118140960795 + 2848227 * 2 ^ 59
def prefixEnd_2848227 : Nat := 4983230072969 + 3 ^ 40 * 2848227 * 2
def baseEnd_2848227 : Nat := 325002103136340673880833

theorem tailTrace_2848227 : CollatzResearch.WordTrace tailWord_2848227 prefixEnd_2848227 325002103136340673880833 := by
  unfold tailWord_2848227
  simp only [CollatzResearch.WordTrace]
  refine ⟨103883373052367492289366935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69255582034911661526244623 103883373052367492289366935)
  ·
    refine ⟨155825059578551238434050403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103883373052367492289366935 155825059578551238434050403)
    ·
      refine ⟨233737589367826857651075605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155825059578551238434050403 233737589367826857651075605)
      ·
        refine ⟨10956449501616883952394169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 233737589367826857651075605 10956449501616883952394169)
        ·
          refine ⟨8217337126212662964295627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10956449501616883952394169 8217337126212662964295627)
          ·
            refine ⟨12326005689318994446443441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8217337126212662964295627 12326005689318994446443441)
            ·
              refine ⟨9244504266989245834832581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12326005689318994446443441 9244504266989245834832581)
              ·
                refine ⟨1733344550060483594031109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9244504266989245834832581 1733344550060483594031109)
                ·
                  refine ⟨325002103136340673880833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733344550060483594031109 325002103136340673880833)
                  ·
                    rfl

theorem cell22_2848227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 4].length) (baseStart_2848227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848227 prefixEnd_2848227 := by exact prefixLift 2848227
  have htrace : WordTrace (prefixWord ++ tailWord_2848227) baseStart_2848227 baseEnd_2848227 := by
    simpa [prefixWord, tailWord_2848227, baseEnd_2848227] using wordTrace_append hprefix tailTrace_2848227
  have hstable : (prefixWord ++ tailWord_2848227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848227).length < 2 ^ (prefixWord ++ tailWord_2848227).sum := by decide
  have hdescent : baseEnd_2848227 < baseStart_2848227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848242 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_2848242 : Nat := 118140960795 + 2848242 * 2 ^ 59
def prefixEnd_2848242 : Nat := 4983230072969 + 3 ^ 40 * 2848242 * 2
def baseEnd_2848242 : Nat := 975011444215566982517453

theorem tailTrace_2848242 : CollatzResearch.WordTrace tailWord_2848242 prefixEnd_2848242 975011444215566982517453 := by
  unfold tailWord_2848242
  simp only [CollatzResearch.WordTrace]
  refine ⟨25970980036828287462790745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69255946764875433234108653 25970980036828287462790745)
  ·
    refine ⟨19478235027621215597093059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25970980036828287462790745 19478235027621215597093059)
    ·
      refine ⟨29217352541431823395639589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19478235027621215597093059 29217352541431823395639589)
      ·
        refine ⟨5478253601518466886682423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29217352541431823395639589 5478253601518466886682423)
        ·
          refine ⟨8217380402277700330023635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5478253601518466886682423 8217380402277700330023635)
          ·
            refine ⟨12326070603416550495035453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8217380402277700330023635 12326070603416550495035453)
            ·
              refine ⟨4622276476281206435638295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12326070603416550495035453 4622276476281206435638295)
              ·
                refine ⟨6933414714421809653457443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622276476281206435638295 6933414714421809653457443)
                ·
                  refine ⟨10400122071632714480186165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6933414714421809653457443 10400122071632714480186165)
                  ·
                    refine ⟨975011444215566982517453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10400122071632714480186165 975011444215566982517453)
                    ·
                      rfl

theorem cell22_2848242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_2848242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848242 prefixEnd_2848242 := by exact prefixLift 2848242
  have htrace : WordTrace (prefixWord ++ tailWord_2848242) baseStart_2848242 baseEnd_2848242 := by
    simpa [prefixWord, tailWord_2848242, baseEnd_2848242] using wordTrace_append hprefix tailTrace_2848242
  have hstable : (prefixWord ++ tailWord_2848242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848242).length < 2 ^ (prefixWord ++ tailWord_2848242).sum := by decide
  have hdescent : baseEnd_2848242 < baseStart_2848242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848285 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2848285 : Nat := 118140960795 + 2848285 * 2 ^ 59
def prefixEnd_2848285 : Nat := 4983230072969 + 3 ^ 40 * 2848285 * 2
def baseEnd_2848285 : Nat := 975026163994329203692321

theorem tailTrace_2848285 : CollatzResearch.WordTrace tailWord_2848285 prefixEnd_2848285 975026163994329203692321 := by
  unfold tailWord_2848285
  simp only [CollatzResearch.WordTrace]
  refine ⟨103885488486157368194978309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69256992324104912129985539 103885488486157368194978309)
  ·
    refine ⟨19478529091154506536558433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103885488486157368194978309 19478529091154506536558433)
    ·
      refine ⟨14608896818365879902418825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19478529091154506536558433 14608896818365879902418825)
      ·
        refine ⟨10956672613774409926814119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14608896818365879902418825 10956672613774409926814119)
        ·
          refine ⟨16435008920661614890221179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10956672613774409926814119 16435008920661614890221179)
          ·
            refine ⟨24652513380992422335331769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16435008920661614890221179 24652513380992422335331769)
            ·
              refine ⟨18489385035744316751498827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24652513380992422335331769 18489385035744316751498827)
              ·
                refine ⟨27734077553616475127248241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18489385035744316751498827 27734077553616475127248241)
                ·
                  refine ⟨20800558165212356345436181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27734077553616475127248241 20800558165212356345436181)
                  ·
                    refine ⟨975026163994329203692321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20800558165212356345436181 975026163994329203692321)
                    ·
                      rfl

theorem cell22_2848285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2848285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848285 prefixEnd_2848285 := by exact prefixLift 2848285
  have htrace : WordTrace (prefixWord ++ tailWord_2848285) baseStart_2848285 baseEnd_2848285 := by
    simpa [prefixWord, tailWord_2848285, baseEnd_2848285] using wordTrace_append hprefix tailTrace_2848285
  have hstable : (prefixWord ++ tailWord_2848285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848285).length < 2 ^ (prefixWord ++ tailWord_2848285).sum := by decide
  have hdescent : baseEnd_2848285 < baseStart_2848285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848287 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 3, 3]
def baseStart_2848287 : Nat := 118140960795 + 2848287 * 2 ^ 59
def prefixEnd_2848287 : Nat := 4983230072969 + 3 ^ 40 * 2848287 * 2
def baseEnd_2848287 : Nat := 975026848635201865142315

theorem tailTrace_2848287 : CollatzResearch.WordTrace tailWord_2848287 prefixEnd_2848287 975026848635201865142315 := by
  unfold tailWord_2848287
  simp only [CollatzResearch.WordTrace]
  refine ⟨103885561432150122536551115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69257040954766748357700743 103885561432150122536551115)
  ·
    refine ⟨155828342148225183804826673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103885561432150122536551115 155828342148225183804826673)
    ·
      refine ⟨116871256611168887853620005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155828342148225183804826673 116871256611168887853620005)
      ·
        refine ⟨21913360614594166472553751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116871256611168887853620005 21913360614594166472553751)
        ·
          refine ⟨32870040921891249708830627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21913360614594166472553751 32870040921891249708830627)
          ·
            refine ⟨49305061382836874563245941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32870040921891249708830627 49305061382836874563245941)
            ·
              refine ⟨4622349504640956990304307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49305061382836874563245941 4622349504640956990304307)
              ·
                refine ⟨6933524256961435485456461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622349504640956990304307 6933524256961435485456461)
                ·
                  refine ⟨2600071596360538307046173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6933524256961435485456461 2600071596360538307046173)
                  ·
                    refine ⟨975026848635201865142315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2600071596360538307046173 975026848635201865142315)
                    ·
                      rfl

theorem cell22_2848287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_2848287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848287 prefixEnd_2848287 := by exact prefixLift 2848287
  have htrace : WordTrace (prefixWord ++ tailWord_2848287) baseStart_2848287 baseEnd_2848287 := by
    simpa [prefixWord, tailWord_2848287, baseEnd_2848287] using wordTrace_append hprefix tailTrace_2848287
  have hstable : (prefixWord ++ tailWord_2848287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848287).length < 2 ^ (prefixWord ++ tailWord_2848287).sum := by decide
  have hdescent : baseEnd_2848287 < baseStart_2848287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848338 : List Nat := [3, 2, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_2848338 : Nat := 118140960795 + 2848338 * 2 ^ 59
def prefixEnd_2848338 : Nat := 4983230072969 + 3 ^ 40 * 2848338 * 2
def baseEnd_2848338 : Nat := 975044306977454732117159

theorem tailTrace_2848338 : CollatzResearch.WordTrace tailWord_2848338 prefixEnd_2848338 975044306977454732117159 := by
  unfold tailWord_2848338
  simp only [CollatzResearch.WordTrace]
  refine ⟨25971855388741339561664417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69258281036643572164438445 25971855388741339561664417)
  ·
    refine ⟨19478891541556004671248313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25971855388741339561664417 19478891541556004671248313)
    ·
      refine ⟨14609168656167003503436235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19478891541556004671248313 14609168656167003503436235)
      ·
        refine ⟨21913752984250505255154353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14609168656167003503436235 21913752984250505255154353)
        ·
          refine ⟨16435314738187878941365765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21913752984250505255154353 16435314738187878941365765)
          ·
            refine ⟨3081621513410227301506081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16435314738187878941365765 3081621513410227301506081)
            ·
              refine ⟨2311216135057670476129561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081621513410227301506081 2311216135057670476129561)
              ·
                refine ⟨1733412101293252857097171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2311216135057670476129561 1733412101293252857097171)
                ·
                  refine ⟨2600118151939879285645757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733412101293252857097171 2600118151939879285645757)
                  ·
                    refine ⟨975044306977454732117159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2600118151939879285645757 975044306977454732117159)
                    ·
                      rfl

theorem cell22_2848338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_2848338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848338 prefixEnd_2848338 := by exact prefixLift 2848338
  have htrace : WordTrace (prefixWord ++ tailWord_2848338) baseStart_2848338 baseEnd_2848338 := by
    simpa [prefixWord, tailWord_2848338, baseEnd_2848338] using wordTrace_append hprefix tailTrace_2848338
  have hstable : (prefixWord ++ tailWord_2848338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848338).length < 2 ^ (prefixWord ++ tailWord_2848338).sum := by decide
  have hdescent : baseEnd_2848338 < baseStart_2848338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848362 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_2848362 : Nat := 118140960795 + 2848362 * 2 ^ 59
def prefixEnd_2848362 : Nat := 4983230072969 + 3 ^ 40 * 2848362 * 2
def baseEnd_2848362 : Nat := 325017507555975556505695

theorem tailTrace_2848362 : CollatzResearch.WordTrace tailWord_2848362 prefixEnd_2848362 325017507555975556505695 := by
  unfold tailWord_2848362
  simp only [CollatzResearch.WordTrace]
  refine ⟨25972074226719602586382835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69258864604585606897020893 25972074226719602586382835)
  ·
    refine ⟨38958111340079403879574253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25972074226719602586382835 38958111340079403879574253)
    ·
      refine ⟨14609291752529776454840345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38958111340079403879574253 14609291752529776454840345)
      ·
        refine ⟨10956968814397332341130259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14609291752529776454840345 10956968814397332341130259)
        ·
          refine ⟨16435453221595998511695389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10956968814397332341130259 16435453221595998511695389)
          ·
            refine ⟨6163294958098499441885771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16435453221595998511695389 6163294958098499441885771)
            ·
              refine ⟨9244942437147749162828657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163294958098499441885771 9244942437147749162828657)
              ·
                refine ⟨6933706827860811872121493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9244942437147749162828657 6933706827860811872121493)
                ·
                  refine ⟨325017507555975556505695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6933706827860811872121493 325017507555975556505695)
                  ·
                    rfl

theorem cell22_2848362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_2848362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848362 prefixEnd_2848362 := by exact prefixLift 2848362
  have htrace : WordTrace (prefixWord ++ tailWord_2848362) baseStart_2848362 baseEnd_2848362 := by
    simpa [prefixWord, tailWord_2848362, baseEnd_2848362] using wordTrace_append hprefix tailTrace_2848362
  have hstable : (prefixWord ++ tailWord_2848362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848362).length < 2 ^ (prefixWord ++ tailWord_2848362).sum := by decide
  have hdescent : baseEnd_2848362 < baseStart_2848362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848377 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 4, 3]
def baseStart_2848377 : Nat := 118140960795 + 2848377 * 2 ^ 59
def prefixEnd_2848377 : Nat := 4983230072969 + 3 ^ 40 * 2848377 * 2
def baseEnd_2848377 : Nat := 975057657474471630392039

theorem tailTrace_2848377 : CollatzResearch.WordTrace tailWord_2848377 prefixEnd_2848377 975057657474471630392039 := by
  unfold tailWord_2848377
  simp only [CollatzResearch.WordTrace]
  refine ⟨103888844001824067907327385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69259229334549378604884923 103888844001824067907327385)
  ·
    refine ⟨77916633001368050930495539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103888844001824067907327385 77916633001368050930495539)
    ·
      refine ⟨116874949502052076395743309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77916633001368050930495539 116874949502052076395743309)
      ·
        refine ⟨43828106063269528648403741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116874949502052076395743309 43828106063269528648403741)
        ·
          refine ⟨16435539773726073243151403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43828106063269528648403741 16435539773726073243151403)
          ·
            refine ⟨24653309660589109864727105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16435539773726073243151403 24653309660589109864727105)
            ·
              refine ⟨18489982245441832398545329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24653309660589109864727105 18489982245441832398545329)
              ·
                refine ⟨13867486684081374298908997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18489982245441832398545329 13867486684081374298908997)
                ·
                  refine ⟨2600153753265257681045437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13867486684081374298908997 2600153753265257681045437)
                  ·
                    refine ⟨975057657474471630392039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2600153753265257681045437 975057657474471630392039)
                    ·
                      rfl

theorem cell22_2848377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_2848377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848377 prefixEnd_2848377 := by exact prefixLift 2848377
  have htrace : WordTrace (prefixWord ++ tailWord_2848377) baseStart_2848377 baseEnd_2848377 := by
    simpa [prefixWord, tailWord_2848377, baseEnd_2848377] using wordTrace_append hprefix tailTrace_2848377
  have hstable : (prefixWord ++ tailWord_2848377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848377).length < 2 ^ (prefixWord ++ tailWord_2848377).sum := by decide
  have hdescent : baseEnd_2848377 < baseStart_2848377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848381 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_2848381 : Nat := 118140960795 + 2848381 * 2 ^ 59
def prefixEnd_2848381 : Nat := 4983230072969 + 3 ^ 40 * 2848381 * 2
def baseEnd_2848381 : Nat := 975059026756216953292027

theorem tailTrace_2848381 : CollatzResearch.WordTrace tailWord_2848381 prefixEnd_2848381 975059026756216953292027 := by
  unfold tailWord_2848381
  simp only [CollatzResearch.WordTrace]
  refine ⟨103888989893809576590472997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69259326595873051060315331 103888989893809576590472997)
  ·
    refine ⟨19479185605089295610713687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103888989893809576590472997 19479185605089295610713687)
    ·
      refine ⟨29218778407633943416070531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19479185605089295610713687 29218778407633943416070531)
      ·
        refine ⟨43828167611450915124105797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29218778407633943416070531 43828167611450915124105797)
        ·
          refine ⟨8217781427147046585769837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43828167611450915124105797 8217781427147046585769837)
          ·
            refine ⟨3081668035180142469663689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8217781427147046585769837 3081668035180142469663689)
            ·
              refine ⟨2311251026385106852247767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081668035180142469663689 2311251026385106852247767)
              ·
                refine ⟨3466876539577660278371651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311251026385106852247767 3466876539577660278371651)
                ·
                  refine ⟨5200314809366490417557477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466876539577660278371651 5200314809366490417557477)
                  ·
                    refine ⟨975059026756216953292027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5200314809366490417557477 975059026756216953292027)
                    ·
                      rfl

theorem cell22_2848381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_2848381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848381 prefixEnd_2848381 := by exact prefixLift 2848381
  have htrace : WordTrace (prefixWord ++ tailWord_2848381) baseStart_2848381 baseEnd_2848381 := by
    simpa [prefixWord, tailWord_2848381, baseEnd_2848381] using wordTrace_append hprefix tailTrace_2848381
  have hstable : (prefixWord ++ tailWord_2848381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848381).length < 2 ^ (prefixWord ++ tailWord_2848381).sum := by decide
  have hdescent : baseEnd_2848381 < baseStart_2848381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848394 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_2848394 : Nat := 118140960795 + 2848394 * 2 ^ 59
def prefixEnd_2848394 : Nat := 4983230072969 + 3 ^ 40 * 2848394 * 2
def baseEnd_2848394 : Nat := 975063476921889252716987

theorem tailTrace_2848394 : CollatzResearch.WordTrace tailWord_2848394 prefixEnd_2848394 975063476921889252716987 := by
  unfold tailWord_2848394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25972366010690619952674059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69259642695174986540464157 25972366010690619952674059)
  ·
    refine ⟨38958549016035929929011089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25972366010690619952674059 38958549016035929929011089)
    ·
      refine ⟨29218911762026947446758317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38958549016035929929011089 29218911762026947446758317)
      ·
        refine ⟨10957091910760105292534369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29218911762026947446758317 10957091910760105292534369)
        ·
          refine ⟨8217818933070078969400777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10957091910760105292534369 8217818933070078969400777)
          ·
            refine ⟨6163364199802559227050583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8217818933070078969400777 6163364199802559227050583)
            ·
              refine ⟨9245046299703838840575875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163364199802559227050583 9245046299703838840575875)
              ·
                refine ⟨13867569449555758260863813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9245046299703838840575875 13867569449555758260863813)
                ·
                  refine ⟨2600169271791704673911965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13867569449555758260863813 2600169271791704673911965)
                  ·
                    refine ⟨975063476921889252716987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2600169271791704673911965 975063476921889252716987)
                    ·
                      rfl

theorem cell22_2848394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_2848394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848394 prefixEnd_2848394 := by exact prefixLift 2848394
  have htrace : WordTrace (prefixWord ++ tailWord_2848394) baseStart_2848394 baseEnd_2848394 := by
    simpa [prefixWord, tailWord_2848394, baseEnd_2848394] using wordTrace_append hprefix tailTrace_2848394
  have hstable : (prefixWord ++ tailWord_2848394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848394).length < 2 ^ (prefixWord ++ tailWord_2848394).sum := by decide
  have hdescent : baseEnd_2848394 < baseStart_2848394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848430 : List Nat := [4, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_2848430 : Nat := 118140960795 + 2848430 * 2 ^ 59
def prefixEnd_2848430 : Nat := 4983230072969 + 3 ^ 40 * 2848430 * 2
def baseEnd_2848430 : Nat := 325025266819199052938959

theorem tailTrace_2848430 : CollatzResearch.WordTrace tailWord_2848430 prefixEnd_2848430 325025266819199052938959 := by
  unfold tailWord_2848430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12986347133829007244875843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69260518047088038639337829 12986347133829007244875843)
  ·
    refine ⟨19479520700743510867313765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12986347133829007244875843 19479520700743510867313765)
    ·
      refine ⟨3652410131389408287621331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19479520700743510867313765 3652410131389408287621331)
      ·
        refine ⟨5478615197084112431431997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652410131389408287621331 5478615197084112431431997)
        ·
          refine ⟨2054480698906542161786999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5478615197084112431431997 2054480698906542161786999)
          ·
            refine ⟨3081721048359813242680499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054480698906542161786999 3081721048359813242680499)
            ·
              refine ⟨4622581572539719864020749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081721048359813242680499 4622581572539719864020749)
              ·
                refine ⟨1733468089702394949007781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4622581572539719864020749 1733468089702394949007781)
                ·
                  refine ⟨325025266819199052938959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733468089702394949007781 325025266819199052938959)
                  ·
                    rfl

theorem cell22_2848430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_2848430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848430 prefixEnd_2848430 := by exact prefixLift 2848430
  have htrace : WordTrace (prefixWord ++ tailWord_2848430) baseStart_2848430 baseEnd_2848430 := by
    simpa [prefixWord, tailWord_2848430, baseEnd_2848430] using wordTrace_append hprefix tailTrace_2848430
  have hstable : (prefixWord ++ tailWord_2848430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848430).length < 2 ^ (prefixWord ++ tailWord_2848430).sum := by decide
  have hdescent : baseEnd_2848430 < baseStart_2848430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848435 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 9]
def baseStart_2848435 : Nat := 118140960795 + 2848435 * 2 ^ 59
def prefixEnd_2848435 : Nat := 4983230072969 + 3 ^ 40 * 2848435 * 2
def baseEnd_2848435 : Nat := 325025837353259604147287

theorem tailTrace_2848435 : CollatzResearch.WordTrace tailWord_2848435 prefixEnd_2848435 325025837353259604147287 := by
  unfold tailWord_2848435
  simp only [CollatzResearch.WordTrace]
  refine ⟨103890959435613943812938759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69260639623742629208625839 103890959435613943812938759)
  ·
    refine ⟨155836439153420915719408139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103890959435613943812938759 155836439153420915719408139)
    ·
      refine ⟨233754658730131373579112209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155836439153420915719408139 233754658730131373579112209)
      ·
        refine ⟨175315994047598530184334157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233754658730131373579112209 175315994047598530184334157)
        ·
          refine ⟨65743497767849448819125309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175315994047598530184334157 65743497767849448819125309)
          ·
            refine ⟨24653811662943543307171991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65743497767849448819125309 24653811662943543307171991)
            ·
              refine ⟨36980717494415314960757987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24653811662943543307171991 36980717494415314960757987)
              ·
                refine ⟨55471076241622972441136981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36980717494415314960757987 55471076241622972441136981)
                ·
                  refine ⟨325025837353259604147287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55471076241622972441136981 325025837353259604147287)
                  ·
                    rfl

theorem cell22_2848435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 9].length) (baseStart_2848435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848435 prefixEnd_2848435 := by exact prefixLift 2848435
  have htrace : WordTrace (prefixWord ++ tailWord_2848435) baseStart_2848435 baseEnd_2848435 := by
    simpa [prefixWord, tailWord_2848435, baseEnd_2848435] using wordTrace_append hprefix tailTrace_2848435
  have hstable : (prefixWord ++ tailWord_2848435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848435).length < 2 ^ (prefixWord ++ tailWord_2848435).sum := by decide
  have hdescent : baseEnd_2848435 < baseStart_2848435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848452 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 7]
def baseStart_2848452 : Nat := 118140960795 + 2848452 * 2 ^ 59
def prefixEnd_2848452 : Nat := 4983230072969 + 3 ^ 40 * 2848452 * 2
def baseEnd_2848452 : Nat := 325027777169065478255603

theorem tailTrace_2848452 : CollatzResearch.WordTrace tailWord_2848452 prefixEnd_2848452 325027777169065478255603 := by
  unfold tailWord_2848452
  simp only [CollatzResearch.WordTrace]
  refine ⟨51945789738276177858153805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69261052984368237144205073 51945789738276177858153805)
  ·
    refine ⟨19479671151853566696807677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51945789738276177858153805 19479671151853566696807677)
    ·
      refine ⟨7304876681945087511302879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19479671151853566696807677 7304876681945087511302879)
      ·
        refine ⟨10957315022917631266954319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7304876681945087511302879 10957315022917631266954319)
        ·
          refine ⟨16435972534376446900431479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10957315022917631266954319 16435972534376446900431479)
          ·
            refine ⟨24653958801564670350647219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16435972534376446900431479 24653958801564670350647219)
            ·
              refine ⟨36980938202347005525970829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24653958801564670350647219 36980938202347005525970829)
              ·
                refine ⟨13867851825880127072239061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36980938202347005525970829 13867851825880127072239061)
                ·
                  refine ⟨325027777169065478255603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13867851825880127072239061 325027777169065478255603)
                  ·
                    rfl

theorem cell22_2848452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_2848452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2848452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2848452 prefixEnd_2848452 := by exact prefixLift 2848452
  have htrace : WordTrace (prefixWord ++ tailWord_2848452) baseStart_2848452 baseEnd_2848452 := by
    simpa [prefixWord, tailWord_2848452, baseEnd_2848452] using wordTrace_append hprefix tailTrace_2848452
  have hstable : (prefixWord ++ tailWord_2848452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848452).length < 2 ^ (prefixWord ++ tailWord_2848452).sum := by decide
  have hdescent : baseEnd_2848452 < baseStart_2848452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
